//! Consensus Module
//!
//! This module implements the TimeVote consensus protocol for instant transaction finality.
//! Key components:
//! - TimeVote: Unified consensus with progressive finality proof assembly
//! - TimeVote Protocol: Low-latency stake-weighted voting consensus primitives adapted for signed vote collection
//! - Transaction validation and UTXO management
//! - Stake-weighted validator sampling and vote accumulation
//!
//! Note: Some methods are scaffolding for full consensus integration.

#![allow(dead_code)]

use crate::block::types::Block;
use crate::finality_proof::FinalityProofManager;
use crate::masternode_registry::MasternodeRegistry;
use crate::network::message::NetworkMessage;
use crate::state_notifier::StateNotifier;
use crate::transaction_pool::TransactionPool;
use crate::types::*;
use crate::utxo_manager::UTXOStateManager;
use dashmap::{DashMap, DashSet};
use ed25519_dalek::{Signer, VerifyingKey};
use parking_lot::RwLock;
use sha2::{Digest, Sha256, Sha512};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::sync::OnceLock;
use std::time::{Duration, Instant};
use thiserror::Error;
use tokio::sync::{Notify, RwLock as TokioRwLock};

// Resource limits to prevent DOS attacks
const MAX_MEMPOOL_TRANSACTIONS: usize = 10_000;
#[allow(dead_code)] // Used by TransactionPool for mempool size limits
const MAX_MEMPOOL_SIZE_BYTES: usize = 300_000_000; // 300MB
const MAX_TX_SIZE: usize = 10_000_000; // 10MB
pub const MIN_TX_FEE: u64 = 1_000_000; // 0.01 TIME minimum fee
const DUST_THRESHOLD: u64 = 1000; // Minimum output value (prevents spam)
const SATOSHIS_PER_TIME: u64 = 100_000_000;

/// Governance-adjustable fee schedule.
/// Stored in consensus state so governance proposals can update tiers and
/// minimum fee without requiring a software upgrade or hard fork.
#[derive(Clone, Debug)]
pub struct FeeSchedule {
    /// (upper_bound_satoshis, rate_basis_points). Ordered smallest first.
    pub tiers: Vec<(u64, u64)>,
    pub min_fee: u64,
}

impl Default for FeeSchedule {
    fn default() -> Self {
        Self {
            tiers: vec![
                (100 * SATOSHIS_PER_TIME, 100),   // < 100 TIME  → 1%
                (1_000 * SATOSHIS_PER_TIME, 50),  // < 1k TIME   → 0.5%
                (10_000 * SATOSHIS_PER_TIME, 25), // < 10k TIME  → 0.25%
                (u64::MAX, 10),                   // >= 10k TIME → 0.1%
            ],
            min_fee: MIN_TX_FEE,
        }
    }
}

impl FeeSchedule {
    pub fn required_fee(&self, send_amount: u64) -> u64 {
        let rate_bps = self
            .tiers
            .iter()
            .find(|(up_to, _)| send_amount < *up_to)
            .map(|(_, bps)| *bps)
            .unwrap_or(10);
        let proportional = send_amount * rate_bps / 10_000;
        proportional.max(self.min_fee)
    }

    /// Fee to deduct from a gross amount so the recipient gets `amount - fee` and the
    /// fee satisfies `fee >= required_fee(amount - fee)`.
    ///
    /// Simple iteration loses 1 satoshi to truncation near tier boundaries. This solves
    /// it algebraically: for a given rate_bps,
    ///   fee = ceil(amount × rate_bps / (10_000 + rate_bps))
    /// guarantees the fee is valid against the actual send_amount in that tier.
    /// Tiers are tried highest-rate-first; the first one where `amount - fee` falls
    /// below the tier limit is the correct solution.
    pub fn required_fee_subtract(&self, amount: u64) -> u64 {
        for &(tier_limit, rate_bps) in &self.tiers {
            let divisor = 10_000 + rate_bps;
            let f = amount.saturating_mul(rate_bps).div_ceil(divisor);
            let f = f.max(self.min_fee);
            let send_amount = amount.saturating_sub(f);
            if send_amount < tier_limit {
                return f;
            }
        }
        self.min_fee
    }
}

#[cfg(test)]
mod fee_tests {
    use super::*;

    fn sched() -> FeeSchedule {
        FeeSchedule::default()
    }

    /// For every test amount, assert that the fee returned by required_fee_subtract
    /// is accepted by the validator (fee >= required_fee(send_amount)) and that
    /// send_amount + fee == amount exactly.
    fn assert_subtract_fee_valid(amount: u64) {
        let s = sched();
        let fee = s.required_fee_subtract(amount);
        let send_amount = amount - fee;
        let required = s.required_fee(send_amount);
        assert!(
            fee >= required,
            "amount={amount}: fee {fee} < required_fee({send_amount})={required}"
        );
        assert_eq!(
            send_amount + fee,
            amount,
            "amount={amount}: send+fee != amount"
        );
    }

    #[test]
    fn test_subtract_fee_boundary_100_time() {
        // 100 TIME sits in the 0.5% tier but recipient output falls into 1% tier.
        // This was the exact scenario that caused "Insufficient fee" rejections.
        let amount = 100 * SATOSHIS_PER_TIME; // 10_000_000_000
        assert_subtract_fee_valid(amount);
    }

    #[test]
    fn test_subtract_fee_boundary_1000_time() {
        // 1000 TIME sits in 0.25% tier; recipient may cross into 0.5% tier.
        assert_subtract_fee_valid(1_000 * SATOSHIS_PER_TIME);
    }

    #[test]
    fn test_subtract_fee_boundary_10000_time() {
        assert_subtract_fee_valid(10_000 * SATOSHIS_PER_TIME);
    }

    #[test]
    fn test_subtract_fee_various_amounts() {
        for &time in &[
            1u64, 50, 99, 100, 101, 500, 999, 1000, 1001, 5000, 9999, 10000, 50000,
        ] {
            assert_subtract_fee_valid(time * SATOSHIS_PER_TIME);
        }
    }

    #[test]
    fn test_subtract_fee_min_fee_floor() {
        // Very small amounts should still return at least min_fee.
        let s = sched();
        let fee = s.required_fee_subtract(MIN_TX_FEE + 1);
        assert!(fee >= MIN_TX_FEE);
    }
}

// §7.6 Liveness Fallback Protocol Parameters
const STALL_TIMEOUT: Duration = Duration::from_secs(30); // Protocol §7.6.1
const FALLBACK_MIN_DURATION: Duration = Duration::from_secs(20); // Protocol §7.6.3
const FALLBACK_ROUND_TIMEOUT: Duration = Duration::from_secs(10); // Protocol §7.6.5
const MAX_FALLBACK_ROUNDS: u32 = 5; // Protocol §7.6.5

type BroadcastCallback = Arc<TokioRwLock<Option<Arc<dyn Fn(NetworkMessage) + Send + Sync>>>>;

struct NodeIdentity {
    address: String,
    signing_key: ed25519_dalek::SigningKey,
}

impl NodeIdentity {
    /// Sign a finality vote with this node's key
    #[allow(clippy::too_many_arguments)]
    fn sign_finality_vote(
        &self,
        chain_id: u32,
        txid: Hash256,
        tx_hash_commitment: Hash256,
        slot_index: u64,
        decision: VoteDecision, // NEW: Accept or Reject
        voter_mn_id: String,
        voter_weight: u64,
    ) -> FinalityVote {
        use ed25519_dalek::Signer;

        // Create the signing message
        let mut msg = Vec::new();
        msg.extend_from_slice(&chain_id.to_le_bytes());
        msg.extend_from_slice(&txid);
        msg.extend_from_slice(&tx_hash_commitment);
        msg.extend_from_slice(&slot_index.to_le_bytes());
        // CRITICAL: Include decision in signature (equivocation prevention)
        msg.push(match decision {
            VoteDecision::Accept => 0x01,
            VoteDecision::Reject => 0x00,
        });
        msg.extend_from_slice(voter_mn_id.as_bytes());
        msg.extend_from_slice(&voter_weight.to_le_bytes());

        // Sign the message
        let signature = self.signing_key.sign(&msg);

        FinalityVote {
            chain_id,
            txid,
            tx_hash_commitment,
            slot_index,
            decision, // Include decision in vote
            voter_mn_id,
            voter_weight,
            signature: signature.to_bytes().to_vec(),
        }
    }

    /// Sign a LivenessAlert with this node's key (§7.6.2)
    #[allow(clippy::too_many_arguments)]
    fn sign_liveness_alert(
        &self,
        chain_id: u32,
        txid: Hash256,
        tx_hash_commitment: Hash256,
        slot_index: u64,
        poll_history: Vec<PollResult>,
        stall_duration_ms: u64,
        current_confidence: u32,
    ) -> LivenessAlert {
        use ed25519_dalek::Signer;

        let alert = LivenessAlert {
            chain_id,
            txid,
            tx_hash_commitment,
            slot_index,
            poll_history,
            current_confidence,
            stall_duration_ms,
            reporter_mn_id: self.address.clone(),
            reporter_signature: vec![],
        };

        let msg = alert.signing_message();
        let signature = self.signing_key.sign(&msg);

        LivenessAlert {
            reporter_signature: signature.to_bytes().to_vec(),
            ..alert
        }
    }

    /// Sign a FinalityProposal with this node's key (§7.6.4)
    fn sign_finality_proposal(
        &self,
        chain_id: u32,
        txid: Hash256,
        tx_hash_commitment: Hash256,
        slot_index: u64,
        decision: FallbackDecision,
        justification: String,
    ) -> FinalityProposal {
        use ed25519_dalek::Signer;

        let proposal = FinalityProposal {
            chain_id,
            txid,
            tx_hash_commitment,
            slot_index,
            decision: decision.clone(),
            justification,
            leader_mn_id: self.address.clone(),
            leader_signature: vec![],
        };

        let msg = proposal.signing_message();
        let signature = self.signing_key.sign(&msg);

        FinalityProposal {
            leader_signature: signature.to_bytes().to_vec(),
            ..proposal
        }
    }

    /// Sign a FallbackVote with this node's key (§7.6.4)
    fn sign_fallback_vote(
        &self,
        chain_id: u32,
        proposal_hash: Hash256,
        vote: FallbackVoteDecision,
        voter_weight: u64,
    ) -> FallbackVote {
        use ed25519_dalek::Signer;

        let fallback_vote = FallbackVote {
            chain_id,
            proposal_hash,
            vote: vote.clone(),
            voter_mn_id: self.address.clone(),
            voter_weight,
            voter_signature: vec![],
        };

        let msg = fallback_vote.signing_message();
        let signature = self.signing_key.sign(&msg);

        FallbackVote {
            voter_signature: signature.to_bytes().to_vec(),
            ..fallback_vote
        }
    }
}

// ============================================================================
// timevote PROTOCOL TYPES
// ============================================================================

/// TimeVote consensus errors
#[derive(Error, Debug)]
#[allow(dead_code)]
pub enum TimeVoteError {
    #[error("Transaction not found")]
    TransactionNotFound,

    #[error("Invalid preference: {0}")]
    InvalidPreference(String),

    #[error("Insufficient confidence: got {got}, need {threshold}")]
    InsufficientConfidence { got: usize, threshold: usize },

    #[error("Query failed: {0}")]
    QueryFailed(String),

    #[error("Chit acquisition failed")]
    ChitAcquisitionFailed,

    #[error("Configuration error: {0}")]
    ConfigError(String),
}

/// Configuration for TimeVote consensus
#[derive(Debug, Clone)]
pub struct TimeVoteConfig {
    /// Number of validators to query per round (k parameter)
    pub sample_size: usize,
    /// Quorum size - minimum votes needed to consider a round (alpha parameter)
    /// Per spec: alpha = 14
    pub quorum_size: usize,
    /// Number of consecutive preference confirms needed for finality (beta)
    /// Per spec: beta = 20
    pub finality_confidence: usize,
    /// Required finality weight threshold as percentage (default 51% for simple majority)
    pub q_finality_percent: u64,
    /// Timeout for query responses (milliseconds)
    pub query_timeout_ms: u64,
    /// Maximum rounds before giving up
    pub max_rounds: usize,
}

impl Default for TimeVoteConfig {
    fn default() -> Self {
        Self {
            sample_size: 20,         // Query 20 validators per round (k)
            quorum_size: 14,         // Need 14+ responses for consensus (alpha)
            finality_confidence: 20, // 20 consecutive confirms for finality (beta)
            q_finality_percent: 67,  // 67% weight threshold for finality (BFT-safe majority)
            query_timeout_ms: 2000,  // 2 second timeout
            max_rounds: 100,
        }
    }
}

/// Preference tracking for a transaction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum Preference {
    Accept,
    Reject,
}

/// Memory usage statistics for consensus engine
#[derive(Debug, Clone)]
pub struct ConsensusMemoryStats {
    pub tx_state_entries: usize,
    pub finalized_txs: usize,
    pub avs_snapshots: usize,
    pub vfp_votes: usize,
}

impl std::fmt::Display for Preference {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Preference::Accept => write!(f, "Accept"),
            Preference::Reject => write!(f, "Reject"),
        }
    }
}

/// Information about a validator for stake-weighted sampling
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidatorInfo {
    pub address: String,
    pub weight: u64, // Sampling weight based on tier
}

/// Transaction voting state - tracks preference for fallback protocol
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct VotingState {
    pub preference: Preference,
    pub last_finalized: Option<Preference>,
}

impl VotingState {
    pub fn new(initial_preference: Preference) -> Self {
        Self {
            preference: initial_preference,
            last_finalized: None,
        }
    }

    /// Record finalization
    pub fn finalize(&mut self) {
        self.last_finalized = Some(self.preference);
    }
}

// ============================================================================
// PHASE 3D/3E: TIMELOCK VOTING ACCUMULATORS
// ============================================================================

/// Accumulates prepare votes for a block (Phase 3D)
/// Pure timevote: Tracks continuous sampling votes until majority consensus
#[derive(Debug)]
pub struct PrepareVoteAccumulator {
    /// block_hash -> Vec<(voter_id, weight)>
    votes: DashMap<Hash256, Vec<(String, u64)>>,
    /// Track which blocks already reached consensus (prevents duplicate actions)
    consensus_signaled: DashSet<Hash256>,
}

impl Default for PrepareVoteAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl PrepareVoteAccumulator {
    pub fn new() -> Self {
        Self {
            votes: DashMap::new(),
            consensus_signaled: DashSet::new(),
        }
    }

    /// Add a prepare vote for a block.
    /// A voter can only vote for ONE block — first vote wins.
    pub fn add_vote(&self, block_hash: Hash256, voter_id: String, weight: u64) {
        // Check if this voter already voted for a DIFFERENT block
        for entry in self.votes.iter() {
            if *entry.key() != block_hash && entry.value().iter().any(|(id, _)| *id == voter_id) {
                tracing::debug!(
                    "⚠️ Ignoring duplicate prepare vote from {} — already voted for different block",
                    voter_id
                );
                return;
            }
        }
        // Also prevent double-voting for the same block
        let mut votes = self.votes.entry(block_hash).or_default();
        if votes.iter().any(|(id, _)| *id == voter_id) {
            return;
        }
        votes.push((voter_id, weight));
    }

    /// Check if timevote consensus reached: majority of participating validator WEIGHT agrees.
    /// Uses accumulated stake weight (not raw vote count) to prevent Free-tier Sybil attacks.
    /// Returns true only ONCE per block hash to prevent duplicate actions.
    pub fn check_consensus(&self, block_hash: Hash256, _sample_size: usize) -> bool {
        // Short-circuit: consensus already signaled for this block
        if self.consensus_signaled.contains(&block_hash) {
            return false;
        }

        // Extract vote data for target block, then DROP the Ref (shard read lock)
        // before calling iter(). This prevents a potential deadlock: if a concurrent
        // add_vote() has a pending write lock on the same shard, holding the get()
        // Ref while calling iter() could deadlock under write-priority RwLock semantics.
        let (vote_count, block_weight) = match self.votes.get(&block_hash) {
            Some(entry) => {
                let count = entry.len();
                let weight: u64 = entry.iter().map(|(_, w)| *w).sum();
                (count, weight)
            }
            None => return false,
        };
        // Ref is now dropped — shard read lock released

        // SECURITY: Require at least 2 unique voters for this block.
        // A solo node must never finalize its own block.
        if vote_count < 2 {
            return false;
        }

        // Accumulate total participating weight across ALL block hashes
        let mut total_weight: u64 = 0;
        let mut seen_voters = std::collections::HashSet::new();
        for entry in self.votes.iter() {
            for (voter_id, w) in entry.value() {
                if seen_voters.insert(voter_id.clone()) {
                    total_weight += w;
                }
            }
        }

        // Majority: block weight must exceed 50% of total participating weight
        let result = total_weight > 0 && block_weight > total_weight / 2;
        if result {
            // Mark as signaled so subsequent checks return false
            self.consensus_signaled.insert(block_hash);
        } else if vote_count >= 2 {
            tracing::debug!(
                "🗳️  Consensus check: block_weight={}, total_weight={}, voters={} → FAIL",
                block_weight,
                total_weight,
                vote_count,
            );
        }
        result
    }

    /// Get accumulated weight for a block
    pub fn get_weight(&self, block_hash: Hash256) -> u64 {
        self.votes
            .get(&block_hash)
            .map(|entry| entry.iter().map(|(_, w)| w).sum())
            .unwrap_or(0)
    }

    /// Get list of voter IDs who voted for this block
    pub fn get_voters(&self, block_hash: Hash256) -> Vec<String> {
        self.votes
            .get(&block_hash)
            .map(|entry| entry.iter().map(|(id, _)| id.clone()).collect())
            .unwrap_or_default()
    }

    /// Remove a voter's vote from all blocks.
    /// Used when a leader needs to re-vote for its own block after the message
    /// handler already voted for a peer's (inferior VRF) proposal at the same height.
    pub fn remove_voter(&self, voter_id: &str) {
        for mut entry in self.votes.iter_mut() {
            entry.value_mut().retain(|(id, _)| id != voter_id);
        }
    }

    /// Clear votes for a block after finalization
    pub fn clear(&self, block_hash: Hash256) {
        self.votes.remove(&block_hash);
        self.consensus_signaled.remove(&block_hash);
    }

    /// Clear ALL votes (used when advancing to a new block height)
    pub fn clear_all(&self) {
        self.votes.clear();
        self.consensus_signaled.clear();
    }

    /// Get all voters across all block hashes (for merging into last_block_voters)
    pub fn get_all_voters(&self) -> Vec<(Hash256, Vec<String>)> {
        self.votes
            .iter()
            .map(|entry| {
                let hash = *entry.key();
                let voters = entry.value().iter().map(|(id, _)| id.clone()).collect();
                (hash, voters)
            })
            .collect()
    }
}

/// Accumulates precommit votes for a block (Phase 3E)
/// Pure timevote: After prepare consensus, validators continue voting for finality
#[derive(Debug)]
pub struct PrecommitVoteAccumulator {
    /// block_hash -> Vec<(voter_id, ed25519_signature_bytes, weight)>
    votes: DashMap<Hash256, Vec<(String, Vec<u8>, u64)>>,
    /// Track which blocks already reached consensus (prevents duplicate actions)
    consensus_signaled: DashSet<Hash256>,
}

impl Default for PrecommitVoteAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl PrecommitVoteAccumulator {
    pub fn new() -> Self {
        Self {
            votes: DashMap::new(),
            consensus_signaled: DashSet::new(),
        }
    }

    /// Add a precommit vote for a block.
    /// A voter can only vote for ONE block — first vote wins.
    pub fn add_vote(&self, block_hash: Hash256, voter_id: String, signature: Vec<u8>, weight: u64) {
        // Check if this voter already voted for a DIFFERENT block
        for entry in self.votes.iter() {
            if *entry.key() != block_hash && entry.value().iter().any(|(id, _, _)| *id == voter_id)
            {
                tracing::debug!(
                    "⚠️ Ignoring duplicate precommit vote from {} — already voted for different block",
                    voter_id
                );
                return;
            }
        }
        // Also prevent double-voting for the same block
        let mut votes = self.votes.entry(block_hash).or_default();
        if votes.iter().any(|(id, _, _)| *id == voter_id) {
            return;
        }
        votes.push((voter_id, signature, weight));
    }

    /// Check if timevote consensus reached: majority of participating validator WEIGHT agrees.
    /// Uses accumulated stake weight (not raw vote count) to prevent Free-tier Sybil attacks.
    /// Returns true only ONCE per block hash to prevent duplicate actions.
    ///
    /// SECURITY: A minimum of 2 unique voters is required to prevent solo finalization.
    pub fn check_consensus(&self, block_hash: Hash256, _sample_size: usize) -> bool {
        // Short-circuit: consensus already signaled for this block
        if self.consensus_signaled.contains(&block_hash) {
            return false;
        }

        // Extract vote data for target block, then DROP the Ref (shard read lock)
        // before calling iter(). Prevents deadlock with concurrent add_vote().
        let (vote_count, block_weight) = match self.votes.get(&block_hash) {
            Some(entry) => {
                let count = entry.len();
                let weight: u64 = entry.iter().map(|(_, _, w)| *w).sum();
                (count, weight)
            }
            None => return false,
        };

        // SECURITY: Require at least 2 unique voters for this block.
        // A solo node must never finalize its own block.
        if vote_count < 2 {
            return false;
        }

        // Accumulate total participating weight across ALL block hashes
        let mut total_weight: u64 = 0;
        let mut seen_voters = std::collections::HashSet::new();
        for entry in self.votes.iter() {
            for (voter_id, _, w) in entry.value() {
                if seen_voters.insert(voter_id.clone()) {
                    total_weight += w;
                }
            }
        }

        // Majority: block weight must exceed 50% of total participating weight
        let result = total_weight > 0 && block_weight > total_weight / 2;
        if result {
            // Mark as signaled so subsequent checks return false
            self.consensus_signaled.insert(block_hash);
        } else if vote_count >= 2 {
            tracing::debug!(
                "🗳️  Precommit consensus check: block_weight={}, total_weight={}, voters={} → FAIL",
                block_weight,
                total_weight,
                vote_count,
            );
        }
        result
    }

    /// Get accumulated weight for a block
    pub fn get_weight(&self, block_hash: Hash256) -> u64 {
        self.votes
            .get(&block_hash)
            .map(|entry| entry.iter().map(|(_, _, w)| w).sum())
            .unwrap_or(0)
    }

    /// Get list of voter IDs who voted for this block
    pub fn get_voters(&self, block_hash: Hash256) -> Vec<String> {
        self.votes
            .get(&block_hash)
            .map(|entry| entry.iter().map(|(id, _, _)| id.clone()).collect())
            .unwrap_or_default()
    }

    /// Get list of (voter_id, signature) pairs for this block
    pub fn get_signatures(&self, block_hash: Hash256) -> Vec<(String, Vec<u8>)> {
        self.votes
            .get(&block_hash)
            .map(|entry| {
                entry
                    .iter()
                    .map(|(id, sig, _)| (id.clone(), sig.clone()))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Clear votes for a block after finalization
    pub fn clear(&self, block_hash: Hash256) {
        self.votes.remove(&block_hash);
        self.consensus_signaled.remove(&block_hash);
    }

    /// Clear ALL votes (used when advancing to a new block height)
    pub fn clear_all(&self) {
        self.votes.clear();
        self.consensus_signaled.clear();
    }

    /// Get all voters across all block hashes (for merging into last_block_voters)
    pub fn get_all_voters(&self) -> Vec<(Hash256, Vec<String>)> {
        self.votes
            .iter()
            .map(|entry| {
                let hash = *entry.key();
                let voters = entry.value().iter().map(|(id, _, _)| id.clone()).collect();
                (hash, voters)
            })
            .collect()
    }
}

/// Core TimeVote consensus engine - Progressive finality with vote accumulation
pub struct TimeVoteConsensus {
    config: TimeVoteConfig,

    /// Reference to masternode registry (single source of truth for validators)
    masternode_registry: Arc<MasternodeRegistry>,

    /// Transaction preference tracking (for fallback protocol)
    tx_state: DashMap<Hash256, Arc<RwLock<VotingState>>>,

    /// Finalized transactions with timestamp for cleanup
    /// Made pub(crate) for atomic finalization guard in network server
    pub(crate) finalized_txs: DashMap<Hash256, (Preference, Instant)>,

    /// AVS (Active Validator Set) snapshots per slot for finality vote verification
    /// slot_index -> AVSSnapshot
    avs_snapshots: DashMap<u64, AVSSnapshot>,

    /// TimeProof vote accumulator (formerly VFP)
    /// txid -> accumulated votes for TimeProof assembly
    timeproof_votes: DashMap<Hash256, Vec<TimeVote>>,

    /// Accumulated weight tracker for efficient finality checking
    /// txid -> accumulated weight (sum of Accept vote weights only)
    accumulated_weight: DashMap<Hash256, u64>,

    /// Phase 3D: Prepare vote accumulator for timevote blocks
    pub prepare_votes: Arc<PrepareVoteAccumulator>,

    /// Phase 3E: Precommit vote accumulator for timevote blocks
    pub precommit_votes: Arc<PrecommitVoteAccumulator>,

    /// Last height for which votes were cast — used to clear stale votes on height advance
    pub last_voted_height: AtomicU64,

    /// §7.6 Liveness Fallback: Transaction status tracking
    /// Per protocol §7.3 and §7.6 - explicit state machine
    tx_status: Arc<DashMap<Hash256, TransactionStatus>>,

    /// §7.6 Liveness Fallback: Stall detection timers
    /// Tracks when transactions entered Voting state for timeout detection
    stall_timers: Arc<DashMap<Hash256, Instant>>,

    /// §7.6 Liveness Fallback: Alert accumulation tracker
    /// txid -> Vec<LivenessAlert> (accumulate alerts from different reporters)
    liveness_alerts: DashMap<Hash256, Vec<LivenessAlert>>,

    /// §7.6 Liveness Fallback: Vote accumulation tracker
    /// proposal_hash -> Vec<FallbackVote> (accumulate votes from AVS members)
    fallback_votes: DashMap<Hash256, Vec<FallbackVote>>,

    /// PRIORITY: Track active vote requests to pause block production
    /// This ensures instant finality is never blocked by block production
    pub active_vote_requests: Arc<AtomicUsize>,

    /// §7.6 Liveness Fallback: Proposal to transaction mapping
    /// proposal_hash -> txid (track which proposal is for which transaction)
    proposal_to_tx: DashMap<Hash256, Hash256>,

    /// §7.6 Liveness Fallback: Fallback round tracking
    /// txid -> (slot_index, round_count, started_at)
    fallback_rounds: DashMap<Hash256, (u64, u32, Instant)>,

    /// §7.6 Security: Byzantine node detection tracker
    /// mn_id -> flagged (track masternodes exhibiting Byzantine behavior)
    byzantine_nodes: DashMap<String, bool>,

    /// Conflicting TimeProof detection (Item 9: Pre-Mainnet Checklist)
    /// txid -> Vec<TimeProof> (all TimeProofs seen for this transaction)
    /// Multiple TimeProofs = partition scenario with conflicting finality
    competing_timeproofs: DashMap<Hash256, Vec<TimeProof>>,

    /// Conflict log for security monitoring
    /// (txid, slot_index, timestamp) -> conflict details for AI anomaly detector
    timeproof_conflicts: DashMap<(Hash256, u64), TimeProofConflictInfo>,

    /// Preserved voters from finalized blocks (block_hash -> voter list)
    /// Saved before cleanup so block production can reference previous block's voters
    last_block_voters: DashMap<Hash256, Vec<String>>,

    /// Notified whenever a prepare or precommit vote is accumulated.
    /// Allows the block producer to react immediately when consensus is reached
    /// rather than sleeping until the fixed timeout expires.
    pub vote_notify: Arc<Notify>,

    /// Metrics
    rounds_executed: AtomicUsize,
    txs_finalized: AtomicUsize,

    /// §7.6 Fallback Metrics (Phase 5)
    fallback_activations: AtomicUsize,
    stall_detections: AtomicUsize,
    timelock_resolutions: AtomicUsize,
    timeproof_conflicts_detected: AtomicUsize,
}

impl TimeVoteConsensus {
    pub fn new(
        config: TimeVoteConfig,
        masternode_registry: Arc<MasternodeRegistry>,
    ) -> Result<Self, TimeVoteError> {
        // Validate config
        if config.sample_size == 0 {
            return Err(TimeVoteError::ConfigError(
                "sample_size must be > 0".to_string(),
            ));
        }
        if config.finality_confidence == 0 {
            return Err(TimeVoteError::ConfigError(
                "finality_confidence must be > 0".to_string(),
            ));
        }

        Ok(Self {
            config,
            masternode_registry,
            tx_state: DashMap::new(),
            finalized_txs: DashMap::new(),
            avs_snapshots: DashMap::new(),
            timeproof_votes: DashMap::new(),
            accumulated_weight: DashMap::new(),
            prepare_votes: Arc::new(PrepareVoteAccumulator::new()),
            precommit_votes: Arc::new(PrecommitVoteAccumulator::new()),
            last_voted_height: AtomicU64::new(0),
            tx_status: Arc::new(DashMap::new()),
            stall_timers: Arc::new(DashMap::new()),
            liveness_alerts: DashMap::new(),
            fallback_votes: DashMap::new(),
            proposal_to_tx: DashMap::new(),
            fallback_rounds: DashMap::new(),
            byzantine_nodes: DashMap::new(),
            competing_timeproofs: DashMap::new(),
            timeproof_conflicts: DashMap::new(),
            last_block_voters: DashMap::new(),
            active_vote_requests: Arc::new(AtomicUsize::new(0)),
            rounds_executed: AtomicUsize::new(0),
            txs_finalized: AtomicUsize::new(0),
            vote_notify: Arc::new(Notify::new()),
            fallback_activations: AtomicUsize::new(0),
            stall_detections: AtomicUsize::new(0),
            timelock_resolutions: AtomicUsize::new(0),
            timeproof_conflicts_detected: AtomicUsize::new(0),
        })
    }

    /// Get current validators (returns Arc to avoid cloning)
    /// Fetches active masternodes from registry and converts to ValidatorInfo
    pub fn get_validators(&self) -> Arc<Vec<ValidatorInfo>> {
        let masternodes = self.masternode_registry.active_masternodes_cached();
        Arc::new(
            masternodes
                .iter()
                .map(|mn| ValidatorInfo {
                    address: mn.masternode.address.clone(),
                    weight: mn.masternode.tier.sampling_weight(),
                })
                .collect(),
        )
    }

    /// Cleanup finalized transactions and associated state older than retention period
    /// This prevents unbounded memory growth in the DashMaps
    pub fn cleanup_old_finalized(&self, retention_secs: u64) -> usize {
        let cutoff = Instant::now() - Duration::from_secs(retention_secs);
        let mut removed_count = 0;

        // Collect transactions to remove
        let to_remove: Vec<Hash256> = self
            .finalized_txs
            .iter()
            .filter(|entry| entry.value().1 < cutoff)
            .map(|entry| *entry.key())
            .collect();

        // Remove from all maps
        for txid in to_remove {
            self.finalized_txs.remove(&txid);
            self.tx_state.remove(&txid);
            self.timeproof_votes.remove(&txid);
            self.accumulated_weight.remove(&txid);
            removed_count += 1;
        }

        if removed_count > 0 {
            tracing::debug!(
                "Cleaned up {} finalized transactions older than {} seconds",
                removed_count,
                retention_secs
            );
        }

        removed_count
    }

    /// Get memory usage statistics
    pub fn memory_stats(&self) -> ConsensusMemoryStats {
        ConsensusMemoryStats {
            tx_state_entries: self.tx_state.len(),
            finalized_txs: self.finalized_txs.len(),
            avs_snapshots: self.avs_snapshots.len(),
            vfp_votes: self.timeproof_votes.len(),
        }
    }

    /// Get validator addresses only (for compatibility)
    pub fn get_validator_addresses(&self) -> Vec<String> {
        self.get_validators()
            .iter()
            .map(|v| v.address.clone())
            .collect()
    }

    /// Initialize tracking for a new transaction's consensus preference
    pub fn initiate_consensus(&self, txid: Hash256, initial_preference: Preference) -> bool {
        if self.finalized_txs.contains_key(&txid) {
            return false; // Already finalized
        }

        if self.tx_state.contains_key(&txid) {
            return false; // Already initiated
        }

        self.tx_state.insert(
            txid,
            Arc::new(RwLock::new(VotingState::new(initial_preference))),
        );

        true
    }

    /// Get current state of a transaction
    pub fn get_tx_state(&self, txid: &Hash256) -> Option<(Preference, bool)> {
        self.tx_state.get(txid).map(|state| {
            let s = state.read();
            let is_finalized = self.finalized_txs.contains_key(txid);
            (s.preference, is_finalized)
        })
    }

    /// Check if transaction is finalized
    pub fn is_finalized(&self, txid: &Hash256) -> bool {
        self.finalized_txs.contains_key(txid)
    }

    /// Get finalization preference
    pub fn get_finalized_preference(&self, txid: &Hash256) -> Option<Preference> {
        self.finalized_txs.get(txid).map(|entry| entry.value().0)
    }

    // ========================================================================
    // AVS SNAPSHOT MANAGEMENT (Per Protocol §8.4)
    // ========================================================================

    /// Create an AVS snapshot for the current slot
    /// Captures the active validator set with their weights for finality vote verification
    pub fn create_avs_snapshot(&self, slot_index: u64) -> AVSSnapshot {
        let validators = self.get_validators();
        let snapshot = AVSSnapshot::new_with_ref(slot_index, validators);

        self.avs_snapshots.insert(slot_index, snapshot.clone());

        // Cleanup old snapshots (retain 100 slots per protocol §8.4)
        const ASS_SNAPSHOT_RETENTION: u64 = 100;
        if slot_index > ASS_SNAPSHOT_RETENTION {
            let old_slot = slot_index - ASS_SNAPSHOT_RETENTION;
            self.avs_snapshots.remove(&old_slot);
        }

        snapshot
    }

    /// Get AVS snapshot for a specific slot
    pub fn get_avs_snapshot(&self, slot_index: u64) -> Option<AVSSnapshot> {
        self.avs_snapshots.get(&slot_index).map(|s| s.clone())
    }

    // ========================================================================
    // TIMEVOTE ACCUMULATION (Per Protocol §8.5)
    // ========================================================================

    /// Accumulate a TimeVote for a transaction (Protocol §8.5)
    ///
    /// This method:
    /// 1. Verifies vote signature
    /// 2. Checks for duplicate voters
    /// 3. Accumulates Accept votes only (Reject votes logged but not counted)
    /// 4. Updates accumulated weight
    ///
    /// Returns Ok(accumulated_weight) if vote accepted, Err if rejected
    pub fn accumulate_timevote(&self, vote: TimeVote) -> Result<u64, String> {
        let txid = vote.txid;

        // Step 1: Verify signature
        // Get masternode info to get public key
        let masternodes = self.masternode_registry.active_masternodes_cached();

        let mn_info = masternodes
            .iter()
            .find(|info| info.masternode.address == vote.voter_mn_id)
            .ok_or_else(|| format!("Voter {} not in active validator set", vote.voter_mn_id))?;

        // Verify signature
        vote.verify(&mn_info.masternode.public_key)
            .map_err(|e| format!("Vote signature verification failed: {}", e))?;

        // Step 2: Check for duplicate voters
        let mut votes = self.timeproof_votes.entry(txid).or_default();

        // Check if this voter already voted
        if votes.iter().any(|v| v.voter_mn_id == vote.voter_mn_id) {
            return Err(format!(
                "Duplicate vote from {} for TX {}",
                vote.voter_mn_id,
                hex::encode(txid)
            ));
        }

        // Step 3: Add vote to accumulator
        votes.push(vote.clone());
        drop(votes); // Release lock

        // Step 4: Update accumulated weight (only for Accept votes)
        let new_weight = if vote.decision == VoteDecision::Accept {
            let mut weight_entry = self.accumulated_weight.entry(txid).or_insert(0);
            *weight_entry = weight_entry
                .checked_add(vote.voter_weight)
                .ok_or_else(|| "Accumulated vote weight overflow".to_string())?;
            *weight_entry
        } else {
            // Reject votes are tracked but don't contribute to weight
            tracing::debug!(
                "Reject vote from {} for TX {} (not counted toward finality)",
                vote.voter_mn_id,
                hex::encode(txid)
            );
            self.accumulated_weight.get(&txid).map(|w| *w).unwrap_or(0)
        };

        tracing::debug!(
            "Accumulated vote from {} for TX {} (decision: {:?}, weight: {}, total: {})",
            vote.voter_mn_id,
            hex::encode(txid),
            vote.decision,
            vote.voter_weight,
            new_weight
        );

        Ok(new_weight)
    }

    /// Legacy method - redirects to accumulate_timevote()
    /// Kept for backward compatibility
    pub fn accumulate_finality_vote(&self, vote: FinalityVote) -> Result<(), String> {
        self.accumulate_timevote(vote).map(|_| ())
    }

    /// Get accumulated votes for a transaction
    pub fn get_accumulated_votes(&self, txid: &Hash256) -> Vec<TimeVote> {
        self.timeproof_votes
            .get(txid)
            .map(|v| v.clone())
            .unwrap_or_default()
    }

    /// Get accumulated weight for a transaction (Accept votes only)
    pub fn get_accumulated_weight(&self, txid: &Hash256) -> u64 {
        self.accumulated_weight.get(txid).map(|w| *w).unwrap_or(0)
    }

    /// Check if transaction meets TimeProof finality threshold (Protocol §8.3).
    /// Monitoring/helper path only — live finalization uses `TimeProof::verify` and
    /// `handle_timevote_response`, which apply the same 67% ceiling rule.
    /// Returns Ok(true) if accumulated Accept weight >= 67% of AVS weight.
    pub fn check_timeproof_finality(
        &self,
        txid: &Hash256,
        snapshot: &AVSSnapshot,
    ) -> Result<bool, String> {
        let votes = self.get_accumulated_votes(txid);

        if votes.is_empty() {
            return Ok(false);
        }

        // Calculate total weight of valid Accept votes (matches assemble_timeproof)
        let mut total_weight = 0u64;
        let mut seen_voters = std::collections::HashSet::new();

        for vote in &votes {
            if vote.decision != VoteDecision::Accept {
                continue;
            }

            // Voter must be in snapshot
            if !snapshot.contains_validator(&vote.voter_mn_id) {
                continue; // Skip votes from non-AVS validators
            }

            // Voter can only vote once
            if seen_voters.contains(&vote.voter_mn_id) {
                return Err("Duplicate voter in TimeProof".to_string());
            }
            seen_voters.insert(vote.voter_mn_id.clone());

            if let Some(weight) = snapshot.get_validator_weight(&vote.voter_mn_id) {
                total_weight = total_weight
                    .checked_add(weight)
                    .ok_or_else(|| "TimeProof finality weight overflow".to_string())?;
            }
        }

        let threshold = snapshot.voting_threshold();
        Ok(total_weight >= threshold)
    }

    /// Legacy alias for check_timeproof_finality
    pub fn check_vfp_finality(
        &self,
        txid: &Hash256,
        snapshot: &AVSSnapshot,
    ) -> Result<bool, String> {
        self.check_timeproof_finality(txid, snapshot)
    }

    /// Clear accumulated votes for a transaction after finality
    pub fn clear_timeproof_votes(&self, txid: &Hash256) {
        self.timeproof_votes.remove(txid);
        self.accumulated_weight.remove(txid);
    }

    /// Legacy alias for clear_timeproof_votes
    pub fn clear_vfp_votes(&self, txid: &Hash256) {
        self.clear_timeproof_votes(txid);
    }

    // ========================================================================
    // TIMEPROOF CONFLICT DETECTION - Pre-Mainnet Checklist Item 9
    // ========================================================================

    /// Detect and log competing TimeProofs for the same transaction
    ///
    /// Called when a new TimeProof is received for a transaction.
    /// If another TimeProof already exists, logs a conflict and performs fork resolution.
    ///
    /// **Per Pre-Mainnet Checklist Item 9:**
    /// - Detects multiple competing TimeProofs (network partition scenario)
    /// - Logs conflicts to anomaly detector for security monitoring
    /// - Resolves via weight comparison (higher weight wins)
    /// - Returns index of winning TimeProof
    ///
    /// FIXME(security): If two conflicting transactions both obtain valid TimeProofs,
    /// the safety assumptions are violated and the protocol has no on-chain recovery
    /// mechanism. A future release should implement an emergency checkpoint process
    /// where a supermajority (≥90% of AVS weight) can sign a recovery block that
    /// definitively resolves the conflict. Without this, a successful Byzantine attack
    /// could leave the network in an unrecoverable state requiring off-chain coordination.
    pub fn detect_competing_timeproof(
        &self,
        new_proof: TimeProof,
        new_proof_weight: u64,
    ) -> Result<usize, String> {
        let txid = new_proof.txid;
        let slot_index = new_proof.slot_index;

        // Get or create competing proofs vector for this transaction
        let mut proofs = self.competing_timeproofs.entry(txid).or_default();

        let mut weights = Vec::with_capacity(proofs.len() + 1);

        // Collect weights of existing proofs
        for existing_proof in proofs.iter() {
            weights.push(self.calculate_timeproof_weight(existing_proof)?);
        }

        // Add new proof
        proofs.push(new_proof);
        weights.push(new_proof_weight);

        let (winning_index, &max_weight) = weights
            .iter()
            .enumerate()
            .max_by_key(|(_, w)| *w)
            .ok_or_else(|| "No competing proof weights".to_string())?;

        // Conflict detected if 2+ proofs exist
        if proofs.len() >= 2 {
            let conflict_key = (txid, slot_index);

            let conflict_info = TimeProofConflictInfo {
                txid,
                slot_index,
                proof_count: proofs.len(),
                proof_weights: weights.clone(),
                max_weight,
                winning_proof_index: winning_index,
                detected_at: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs(),
                resolved: false,
            };

            self.timeproof_conflicts
                .insert(conflict_key, conflict_info.clone());
            self.timeproof_conflicts_detected
                .fetch_add(1, Ordering::Relaxed);

            // Log with full details for security monitoring
            tracing::warn!(
                "⚠️  TIMEPROOF CONFLICT DETECTED for TX {}: {} competing proofs (slot {}) | Weights: {:?} | Winner: index {} (weight {})",
                hex::encode(txid),
                proofs.len(),
                slot_index,
                weights,
                winning_index,
                max_weight
            );

            // Send to anomaly detector if available (via ConsensusEngine)
            // This will be used for alerting and security monitoring
            return Ok(winning_index);
        }

        Ok(winning_index)
    }

    /// Calculate total weight of a TimeProof
    fn calculate_timeproof_weight(&self, proof: &TimeProof) -> Result<u64, String> {
        let mut total = 0u64;
        for vote in &proof.votes {
            total = total
                .checked_add(vote.voter_weight)
                .ok_or_else(|| "Weight overflow".to_string())?;
        }
        Ok(total)
    }

    /// Resolve fork by selecting the TimeProof with highest weight
    ///
    /// Called after partition healing when competing proofs exist.
    /// Returns the winning TimeProof and logs the resolution.
    pub fn resolve_timeproof_fork(&self, txid: Hash256) -> Result<Option<TimeProof>, String> {
        let proofs = self
            .competing_timeproofs
            .get(&txid)
            .map(|entry| entry.clone());

        if let Some(proofs) = proofs {
            if proofs.is_empty() {
                return Ok(None);
            }

            // Find proof with highest weight
            let mut max_weight = 0u64;
            let mut winning_proof = proofs[0].clone();

            for proof in &proofs {
                let weight = self.calculate_timeproof_weight(proof)?;
                if weight > max_weight {
                    max_weight = weight;
                    winning_proof = proof.clone();
                }
            }

            // Mark as resolved
            if let Some(mut conflict) = self
                .timeproof_conflicts
                .get_mut(&(txid, winning_proof.slot_index))
            {
                conflict.resolved = true;
            }

            tracing::info!(
                "✅ TimeProof fork resolved for TX {}: Selected proof with weight {} from {} competing proofs",
                hex::encode(txid),
                max_weight,
                proofs.len()
            );

            Ok(Some(winning_proof))
        } else {
            Ok(None)
        }
    }

    /// Get all competing TimeProofs for a transaction
    pub fn get_competing_timeproofs(&self, txid: Hash256) -> Vec<TimeProof> {
        self.competing_timeproofs
            .get(&txid)
            .map(|entry| entry.clone())
            .unwrap_or_default()
    }

    /// Get conflict details for a transaction
    pub fn get_conflict_info(
        &self,
        txid: Hash256,
        slot_index: u64,
    ) -> Option<TimeProofConflictInfo> {
        self.timeproof_conflicts
            .get(&(txid, slot_index))
            .map(|entry| entry.clone())
    }

    /// Get total number of timeproof conflicts detected
    pub fn conflicts_detected_count(&self) -> usize {
        self.timeproof_conflicts_detected.load(Ordering::Relaxed)
    }

    /// Clear competing proofs for a transaction after resolution
    pub fn clear_competing_timeproofs(&self, txid: Hash256) {
        self.competing_timeproofs.remove(&txid);
    }

    /// Record finalization (called when threshold reached)
    /// Updates internal state tracking
    pub fn record_finalization(&self, txid: Hash256, accumulated_weight: u64) {
        // Record finalization with timestamp
        self.finalized_txs
            .insert(txid, (Preference::Accept, Instant::now()));

        // Update transaction status
        self.tx_status.insert(
            txid,
            TransactionStatus::Finalized {
                finalized_at: chrono::Utc::now().timestamp_millis(),
                vfp_weight: accumulated_weight,
            },
        );

        // Update metrics
        self.txs_finalized.fetch_add(1, Ordering::Relaxed);

        tracing::info!(
            "✅ TX {} finalized with weight {} (total finalized: {})",
            hex::encode(txid),
            accumulated_weight,
            self.txs_finalized.load(Ordering::Relaxed)
        );
    }

    /// Assemble TimeProof for a finalized transaction (Protocol §8.2)
    ///
    /// Collects all Accept votes for the transaction and creates a TimeProof certificate.
    /// This should be called immediately after finalization is recorded.
    ///
    /// Returns Ok(TimeProof) if successful, Err if insufficient votes or invalid votes
    pub fn assemble_timeproof(&self, txid: Hash256) -> Result<TimeProof, String> {
        // Get all accumulated votes for this transaction
        let all_votes = self.get_accumulated_votes(&txid);

        if all_votes.is_empty() {
            return Err(format!("No votes found for TX {}", hex::encode(txid)));
        }

        // Filter to only Accept votes (per Protocol §8.2)
        let accept_votes: Vec<TimeVote> = all_votes
            .into_iter()
            .filter(|v| v.decision == VoteDecision::Accept)
            .collect();

        if accept_votes.is_empty() {
            return Err(format!(
                "No Accept votes found for TX {}",
                hex::encode(txid)
            ));
        }

        // Get slot_index from first vote (all votes must have same slot_index)
        let slot_index = accept_votes[0].slot_index;

        // Verify all votes have the same slot_index
        if !accept_votes.iter().all(|v| v.slot_index == slot_index) {
            return Err(format!(
                "Votes have mismatched slot_index for TX {}",
                hex::encode(txid)
            ));
        }

        // Verify all votes have the same txid and tx_hash_commitment
        let ref_commitment = accept_votes[0].tx_hash_commitment;
        if !accept_votes
            .iter()
            .all(|v| v.txid == txid && v.tx_hash_commitment == ref_commitment)
        {
            return Err(format!(
                "Votes have mismatched txid or commitment for TX {}",
                hex::encode(txid)
            ));
        }

        // Create TimeProof
        let timeproof = TimeProof {
            txid,
            slot_index,
            votes: accept_votes.clone(),
        };

        // Calculate total weight for logging
        let total_weight: u64 = accept_votes.iter().map(|v| v.voter_weight).sum();

        tracing::info!(
            "📜 Assembled TimeProof for TX {} with {} Accept votes (total weight: {})",
            hex::encode(txid),
            accept_votes.len(),
            total_weight
        );

        Ok(timeproof)
    }

    /// Verify a TimeProof certificate (Protocol §8.2)
    ///
    /// This method verifies that a TimeProof is valid by:
    /// 1. Checking all vote signatures
    /// 2. Verifying voters are in AVS
    /// 3. Checking accumulated weight >= 51% threshold
    /// 4. Ensuring vote consistency
    ///
    /// Returns Ok(accumulated_weight) if valid, Err if invalid
    pub fn verify_timeproof(&self, timeproof: &TimeProof) -> Result<u64, String> {
        // Get active masternodes for AVS verification
        let masternodes = self.masternode_registry.active_masternodes_cached();

        // Calculate total AVS weight
        let total_avs_weight: u64 = masternodes
            .iter()
            .map(|info| info.masternode.tier.sampling_weight())
            .sum();

        // Create closure for public key lookup
        let get_pubkey = |voter_mn_id: &str| -> Option<VerifyingKey> {
            masternodes
                .iter()
                .find(|info| info.masternode.address == voter_mn_id)
                .map(|info| info.masternode.public_key)
        };

        // Verify the TimeProof using its built-in verification
        let accumulated_weight = timeproof.verify(total_avs_weight, get_pubkey)?;

        tracing::info!(
            "✅ TimeProof verified for TX {}: weight={}/{} ({}%), {} votes",
            hex::encode(timeproof.txid),
            accumulated_weight,
            total_avs_weight,
            (accumulated_weight * 100) / total_avs_weight,
            timeproof.votes.len()
        );

        Ok(accumulated_weight)
    }

    // ========================================================================
    // PHASE 3D: PREPARE VOTE HANDLING
    // ========================================================================

    /// Generate a prepare vote for a block (Phase 3D.1)
    /// Called when a valid block is received
    pub fn generate_prepare_vote(&self, block_hash: Hash256, voter_id: &str, voter_weight: u64) {
        // Add our own vote to the accumulator
        self.prepare_votes
            .add_vote(block_hash, voter_id.to_string(), voter_weight);

        tracing::debug!(
            "✅ Generated prepare vote for block {} from {} (weight: {})",
            hex::encode(block_hash),
            voter_id,
            voter_weight
        );
    }

    /// Accumulate a prepare vote from a peer (Phase 3D.2)
    pub fn accumulate_prepare_vote(
        &self,
        block_hash: Hash256,
        voter_id: String,
        voter_weight: u64,
    ) {
        self.prepare_votes
            .add_vote(block_hash, voter_id.clone(), voter_weight);

        let current_weight = self.prepare_votes.get_weight(block_hash);
        tracing::debug!(
            "Prepare vote from {} - accumulated weight: {}",
            voter_id,
            current_weight
        );

        // Wake any tasks waiting for vote progress (e.g. block producer)
        self.vote_notify.notify_waiters();
    }

    /// Check if prepare consensus reached (Phase 3D.2)
    /// Pure timevote: majority of participating validators must vote for block
    pub fn check_prepare_consensus(&self, block_hash: Hash256) -> bool {
        let validators = self.get_validators();
        let sample_size = validators.len();

        // BOOTSTRAP FIX: If no active validators, use all registered masternodes
        // as the upper bound. The adaptive quorum in check_consensus() will
        // min() this with actual participants, so non-voting nodes won't block finalization.
        let sample_size = if sample_size == 0 {
            let all_registered = self.masternode_registry.all_masternodes_cached();
            tracing::warn!(
                "⚠️ No active validators for consensus check, using all {} registered masternodes (bootstrap mode)",
                all_registered.len()
            );
            all_registered.len()
        } else {
            sample_size
        };

        self.prepare_votes.check_consensus(block_hash, sample_size)
    }

    /// Get prepare vote weight for a block
    pub fn get_prepare_weight(&self, block_hash: Hash256) -> u64 {
        self.prepare_votes.get_weight(block_hash)
    }

    // ========================================================================
    // PHASE 3E: PRECOMMIT VOTE HANDLING
    // ========================================================================

    /// Generate a precommit vote for a block (Phase 3E.1)
    /// Called after prepare consensus is reached
    pub fn generate_precommit_vote(
        &self,
        block_hash: Hash256,
        voter_id: &str,
        voter_weight: u64,
        signature: Vec<u8>,
    ) {
        // Add our own vote to the accumulator, including the signature
        self.precommit_votes
            .add_vote(block_hash, voter_id.to_string(), signature, voter_weight);

        tracing::debug!(
            "✅ Generated precommit vote for block {} from {} (weight: {})",
            hex::encode(block_hash),
            voter_id,
            voter_weight
        );
    }

    /// Accumulate a precommit vote from a peer (Phase 3E.2)
    pub fn accumulate_precommit_vote(
        &self,
        block_hash: Hash256,
        voter_id: String,
        voter_weight: u64,
        signature: Vec<u8>,
    ) {
        self.precommit_votes
            .add_vote(block_hash, voter_id.clone(), signature, voter_weight);

        let current_weight = self.precommit_votes.get_weight(block_hash);
        tracing::debug!(
            "Precommit vote from {} - accumulated weight: {}",
            voter_id,
            current_weight
        );

        // Wake any tasks waiting for vote progress (e.g. block producer)
        self.vote_notify.notify_waiters();
    }

    /// Check if precommit consensus reached (Phase 3E.2)
    /// Pure timevote: majority of participating validators must vote for block
    pub fn check_precommit_consensus(&self, block_hash: Hash256) -> bool {
        let validators = self.get_validators();
        let sample_size = validators.len();

        // BOOTSTRAP FIX: If no active validators, use all registered masternodes
        // as the upper bound. The adaptive quorum in check_consensus() will
        // min() this with actual participants, so non-voting nodes won't block finalization.
        let sample_size = if sample_size == 0 {
            let all_registered = self.masternode_registry.all_masternodes_cached();
            tracing::warn!(
                "⚠️ No active validators for consensus check, using all {} registered masternodes (bootstrap mode)",
                all_registered.len()
            );
            all_registered.len()
        } else {
            sample_size
        };

        self.precommit_votes
            .check_consensus(block_hash, sample_size)
    }

    /// Get precommit vote weight for a block
    pub fn get_precommit_weight(&self, block_hash: Hash256) -> u64 {
        self.precommit_votes.get_weight(block_hash)
    }

    /// Get all collected (voter_id, signature) pairs for a block's precommit round
    pub fn get_precommit_signatures(&self, block_hash: Hash256) -> Vec<(String, Vec<u8>)> {
        self.precommit_votes.get_signatures(block_hash)
    }

    /// Clean up votes after block finalization (Phase 3E.6)
    /// Preserves voter list before clearing so block production can reference it.
    /// Merges BOTH prepare and precommit voters to maximize participation coverage.
    /// This is critical because fast consensus (e.g., high-weight producer) can
    /// finalize before all peers' precommit votes arrive, causing low bitmap counts.
    pub fn cleanup_block_votes(&self, block_hash: Hash256) {
        // Start with precommit voters
        let mut voters = self.precommit_votes.get_voters(block_hash);
        // Merge prepare voters — these are always more complete since prepare
        // consensus is reached before precommit consensus begins
        for voter in self.prepare_votes.get_voters(block_hash) {
            if !voters.contains(&voter) {
                voters.push(voter);
            }
        }
        if !voters.is_empty() {
            self.last_block_voters.insert(block_hash, voters);
        }
        self.prepare_votes.clear(block_hash);
        self.precommit_votes.clear(block_hash);
    }

    /// Clear all stale votes when advancing to a new block height.
    /// Called when processing a proposal at a height greater than the last voted height.
    /// Without this, votes from previous heights remain in the accumulator and the
    /// "first vote wins" anti-double-voting rule silently rejects all future votes.
    pub fn advance_vote_height(&self, new_height: u64) {
        let prev = self.last_voted_height.swap(new_height, Ordering::SeqCst);
        if new_height > prev {
            // Merge any late-arriving votes (both phases) into last_block_voters
            // before clearing. This captures votes that arrived after
            // cleanup_block_votes saved the initial voter set at finalization.
            for (hash, voters) in self.precommit_votes.get_all_voters() {
                if !voters.is_empty() {
                    self.last_block_voters
                        .entry(hash)
                        .and_modify(|existing| {
                            for voter in &voters {
                                if !existing.contains(voter) {
                                    existing.push(voter.clone());
                                }
                            }
                        })
                        .or_insert(voters);
                }
            }
            for (hash, voters) in self.prepare_votes.get_all_voters() {
                if !voters.is_empty() {
                    self.last_block_voters
                        .entry(hash)
                        .and_modify(|existing| {
                            for voter in &voters {
                                if !existing.contains(voter) {
                                    existing.push(voter.clone());
                                }
                            }
                        })
                        .or_insert(voters);
                }
            }
            self.prepare_votes.clear_all();
            self.precommit_votes.clear_all();
            tracing::debug!(
                "🗳️  Cleared stale votes: height advanced {} → {}",
                prev,
                new_height
            );
        }
    }

    /// Get preserved voters from a finalized block
    pub fn get_finalized_block_voters(&self, block_hash: Hash256) -> Vec<String> {
        self.last_block_voters
            .get(&block_hash)
            .map(|v| v.clone())
            .unwrap_or_default()
    }

    /// Get metrics
    pub fn get_metrics(&self) -> TimeVoteMetrics {
        TimeVoteMetrics {
            rounds_executed: self.rounds_executed.load(Ordering::Relaxed),
            txs_finalized: self.txs_finalized.load(Ordering::Relaxed),
            tracked_txs: self.tx_state.len(),
        }
    }
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TimeVoteMetrics {
    pub rounds_executed: usize,
    pub txs_finalized: usize,
    pub tracked_txs: usize,
}

// ============================================================================
// CONSENSUS ENGINE
// ============================================================================

type FinalityTimeTracker = Arc<DashMap<[u8; 32], (Instant, Option<Instant>)>>;

#[allow(dead_code)]
pub struct ConsensusEngine {
    // Reference to the masternode registry (single source of truth)
    masternode_registry: Arc<MasternodeRegistry>,
    // Set once at startup - use OnceLock
    identity: OnceLock<NodeIdentity>,
    // Wallet key for signing transactions (may differ from identity/consensus key)
    wallet_signing_key: OnceLock<ed25519_dalek::SigningKey>,
    pub utxo_manager: Arc<UTXOStateManager>,
    pub tx_pool: Arc<TransactionPool>,
    pub broadcast_callback: BroadcastCallback,
    pub state_notifier: Arc<StateNotifier>,
    pub timevote: Arc<TimeVoteConsensus>,
    pub finality_proof_mgr: Arc<FinalityProofManager>,
    pub ai_validator: Option<Arc<crate::ai::AITransactionValidator>>,

    /// Track finality times: block_hash -> (received_at, finalized_at)
    finality_times: FinalityTimeTracker,
    /// Rolling average of last 20 finality times (in milliseconds)
    avg_finality_ms: Arc<parking_lot::RwLock<Vec<f64>>>,
    /// Latest known block hash — used to add unpredictability to fallback leader election
    prev_block_hash: Arc<parking_lot::RwLock<Hash256>>,
    /// Broadcast channel for notifying listeners when a transaction reaches finality.
    /// Subscribers (e.g. WebSocket server) receive the txid so they can look up the
    /// transaction and notify wallet clients.
    tx_finalized_sender: tokio::sync::broadcast::Sender<Hash256>,
    /// In-memory payment request store: to_address → Vec<PaymentRequest>
    /// Requests expire after 24 hours and are cleaned up periodically.
    pub payment_requests: Arc<DashMap<String, Vec<crate::network::message::PaymentRequest>>>,
    /// Live fee schedule — may be replaced by governance proposals.
    fee_schedule: Arc<parking_lot::RwLock<FeeSchedule>>,
    /// Deterministic child address registry: address_string → derivation_index.
    /// Populated at startup and updated on each getnewaddress call.
    derived_address_map: DashMap<String, u32>,
}

impl ConsensusEngine {
    pub fn new(
        masternode_registry: Arc<MasternodeRegistry>,
        utxo_manager: Arc<UTXOStateManager>,
    ) -> Self {
        let timevote_config = TimeVoteConfig::default();
        let timevote = TimeVoteConsensus::new(timevote_config, masternode_registry.clone())
            .expect("Failed to initialize TimeVote consensus");

        Self {
            masternode_registry,
            identity: OnceLock::new(),
            wallet_signing_key: OnceLock::new(),
            utxo_manager,
            tx_pool: Arc::new(TransactionPool::new()),
            broadcast_callback: Arc::new(TokioRwLock::new(None)),
            state_notifier: Arc::new(StateNotifier::new()),
            timevote: Arc::new(timevote),
            finality_proof_mgr: Arc::new(FinalityProofManager::new(1)), // chain_id = 1 for mainnet
            ai_validator: None,
            finality_times: Arc::new(DashMap::new()),
            avg_finality_ms: Arc::new(parking_lot::RwLock::new(Vec::new())),
            prev_block_hash: Arc::new(parking_lot::RwLock::new([0u8; 32])),
            tx_finalized_sender: tokio::sync::broadcast::channel(1000).0,
            payment_requests: Arc::new(DashMap::new()),
            fee_schedule: Arc::new(parking_lot::RwLock::new(FeeSchedule::default())),
            derived_address_map: DashMap::new(),
        }
    }

    /// Return the currently active fee schedule (may have been updated by governance).
    pub fn current_fee_schedule(&self) -> FeeSchedule {
        self.fee_schedule.read().clone()
    }

    /// Replace the active fee schedule (called by governance execution path).
    pub fn apply_fee_schedule(&self, new_schedule: FeeSchedule) -> Result<(), String> {
        *self.fee_schedule.write() = new_schedule;
        tracing::info!("🏛️  Governance: fee schedule updated");
        Ok(())
    }

    /// Create a test instance without UTXO manager (for unit tests)
    #[cfg(test)]
    pub fn new_test(timevote_config: TimeVoteConfig) -> Self {
        // Create UTXO manager and masternode registry with in-memory storage
        let utxo_manager = Arc::new(UTXOStateManager::new());
        let db = Arc::new(sled::Config::new().temporary(true).open().unwrap());
        let masternode_registry =
            Arc::new(MasternodeRegistry::new(db, crate::NetworkType::Testnet));

        let timevote = TimeVoteConsensus::new(timevote_config, masternode_registry.clone())
            .expect("Failed to initialize TimeVote consensus");

        Self {
            masternode_registry,
            identity: OnceLock::new(),
            wallet_signing_key: OnceLock::new(),
            utxo_manager,
            tx_pool: Arc::new(TransactionPool::new()),
            broadcast_callback: Arc::new(TokioRwLock::new(None)),
            state_notifier: Arc::new(StateNotifier::new()),
            timevote: Arc::new(timevote),
            finality_proof_mgr: Arc::new(FinalityProofManager::new(1)),
            ai_validator: None,
            finality_times: Arc::new(DashMap::new()),
            avg_finality_ms: Arc::new(parking_lot::RwLock::new(Vec::new())),
            prev_block_hash: Arc::new(parking_lot::RwLock::new([0u8; 32])),
            tx_finalized_sender: tokio::sync::broadcast::channel(1000).0,
            payment_requests: Arc::new(DashMap::new()),
            fee_schedule: Arc::new(parking_lot::RwLock::new(FeeSchedule::default())),
            derived_address_map: DashMap::new(),
        }
    }

    pub fn enable_ai_validation(&mut self, db: Arc<sled::Db>) {
        self.ai_validator = Some(Arc::new(crate::ai::AITransactionValidator::new(db)));
        tracing::info!("🤖 AI transaction validation enabled");
    }

    /// Subscribe to transaction finality notifications.
    /// Returns a receiver that yields txids when transactions reach consensus finality.
    pub fn subscribe_tx_finalized(&self) -> tokio::sync::broadcast::Receiver<Hash256> {
        self.tx_finalized_sender.subscribe()
    }

    /// Signal that a transaction has been finalized (for WS notification).
    pub fn signal_tx_finalized(&self, txid: Hash256) {
        let _ = self.tx_finalized_sender.send(txid);
    }

    /// Update the latest known block hash (called when a new block is finalized)
    pub fn update_prev_block_hash(&self, hash: Hash256) {
        *self.prev_block_hash.write() = hash;
    }

    /// Get the latest known block hash for fallback leader election
    pub fn get_prev_block_hash(&self) -> Hash256 {
        *self.prev_block_hash.read()
    }

    /// Record when a block is received (start of finality tracking)
    pub fn record_block_received(&self, block_hash: [u8; 32]) {
        self.finality_times
            .insert(block_hash, (Instant::now(), None));
    }

    /// Record when a block achieves finality and update average
    pub fn record_block_finalized(&self, block_hash: [u8; 32]) {
        if let Some(mut entry) = self.finality_times.get_mut(&block_hash) {
            let now = Instant::now();
            let (received_at, finalized_at) = entry.value_mut();
            *finalized_at = Some(now);

            let processing_ms = now.duration_since(*received_at).as_secs_f64() * 1000.0;
            tracing::debug!(
                "📊 Block {} processed in {:.2}ms",
                hex::encode(block_hash),
                processing_ms
            );
        }
    }

    /// Start the fallback timeout monitoring task (§7.6.5)
    ///
    /// Monitors fallback resolution rounds and retries with new leaders on timeout.
    /// After MAX_FALLBACK_ROUNDS (5 rounds), marks transactions for TimeLock resolution.
    ///
    /// # Protocol Flow
    /// 1. Every 5 seconds, scan fallback_rounds for timeouts
    /// 2. If round timeout (10s), increment slot and retry with new leader
    /// 3. If exceeded 5 rounds, mark for TimeLock escalation
    ///
    /// # Returns
    /// * `JoinHandle` - Task handle for the background thread
    pub fn start_fallback_timeout_monitor(
        self: Arc<Self>,
        masternode_registry: Arc<MasternodeRegistry>,
    ) -> tokio::task::JoinHandle<()> {
        tracing::info!("⏱️ Starting fallback timeout monitor (§7.6.5)");

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(5));
            interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

            loop {
                interval.tick().await;

                let retry_count = self
                    .check_fallback_timeouts(&masternode_registry, &self.get_prev_block_hash())
                    .await;
                if retry_count > 0 {
                    tracing::info!("⏱️ Processed {} fallback timeouts", retry_count);
                }
            }
        })
    }

    /// Start the fallback resolution background task (§7.6.4)
    ///
    /// Monitors transactions in FallbackResolution state and triggers leader proposals.
    /// When this node is elected as leader, it broadcasts a FinalityProposal.
    ///
    /// # Protocol Flow
    /// 1. Every 3 seconds, scan transactions in FallbackResolution state
    /// 2. For each transaction, check if we are the elected leader
    /// 3. If leader, determine decision and broadcast proposal
    /// 4. Track proposal to avoid duplicates
    ///
    /// # Returns
    /// * `JoinHandle` - Task handle for the background thread
    pub fn start_fallback_resolution(self: Arc<Self>) -> tokio::task::JoinHandle<()> {
        tracing::info!("🎯 Starting fallback resolution task (§7.6.4)");

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(3));
            interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

            loop {
                interval.tick().await;

                // Get current slot index
                let current_slot = self.get_current_slot_index();

                // Get AVS snapshot for this slot
                let avs = self.timevote.get_avs_snapshot(current_slot);
                let avs_snapshot = match avs {
                    Some(snapshot) => snapshot,
                    None => {
                        // No AVS yet, skip this round
                        continue;
                    }
                };

                // Scan all transactions in FallbackResolution state
                let fallback_txs: Vec<Hash256> = self
                    .timevote
                    .tx_status
                    .iter()
                    .filter_map(|entry| match entry.value() {
                        TransactionStatus::FallbackResolution { .. } => Some(*entry.key()),
                        _ => None,
                    })
                    .collect();

                if !fallback_txs.is_empty() {
                    tracing::debug!(
                        "🎯 Checking {} transactions in fallback",
                        fallback_txs.len()
                    );
                }

                for txid in fallback_txs {
                    // Get the round info
                    let (slot_index, round, _started_at) = match self
                        .timevote
                        .fallback_rounds
                        .get(&txid)
                    {
                        Some(entry) => *entry.value(),
                        None => {
                            tracing::warn!("No fallback round info for tx {}", hex::encode(txid));
                            continue;
                        }
                    };

                    // Check if we are the leader for this transaction
                    if self.is_fallback_leader(
                        txid,
                        slot_index,
                        round,
                        &avs_snapshot,
                        &self.get_prev_block_hash(),
                    ) {
                        tracing::info!(
                            "🎯 I am the fallback leader for tx {} (slot: {}, round: {})",
                            hex::encode(&txid[..8]),
                            slot_index,
                            round
                        );

                        // Execute as leader
                        if let Err(e) = self
                            .execute_fallback_as_leader(txid, slot_index, round)
                            .await
                        {
                            tracing::error!(
                                "Failed to execute fallback as leader for tx {}: {}",
                                hex::encode(&txid[..8]),
                                e
                            );
                        }
                    }
                }
            }
        })
    }

    /// Start the stall detection background task (§7.6.1)
    ///
    /// Monitors all transactions in Voting state and detects stalls after STALL_TIMEOUT (30s).
    /// When a stall is detected, broadcasts a LivenessAlert to trigger fallback consensus.
    ///
    /// # Protocol Flow (§7.6.1)
    /// 1. Every 5 seconds, scan all transactions in Voting state
    /// 2. Check elapsed time since voting started
    /// 3. If elapsed > 30s, broadcast LivenessAlert
    /// 4. Continue monitoring until transaction finalizes or enters FallbackResolution
    ///
    /// # Returns
    /// * `JoinHandle` - Task handle for the background thread
    ///
    /// # Example
    /// ```ignore
    /// let stall_task = consensus.start_stall_detection();
    /// // Task runs indefinitely until dropped
    /// ```
    pub fn start_stall_detection(self: Arc<Self>) -> tokio::task::JoinHandle<()> {
        tracing::info!("🔍 Starting stall detection task (§7.6.1)");

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(5));
            interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

            loop {
                interval.tick().await;

                // Get current slot index for alert signing
                let current_slot = self.get_current_slot_index();

                // Scan all transactions for stalls
                let stalled_txs = self.detect_stalled_transactions();

                if !stalled_txs.is_empty() {
                    tracing::debug!("🔍 Detected {} stalled transactions", stalled_txs.len());
                }

                // Broadcast alerts for stalled transactions
                for txid in stalled_txs {
                    if let Err(e) = self.broadcast_liveness_alert(txid, current_slot).await {
                        tracing::warn!(
                            "Failed to broadcast LivenessAlert for tx {}: {}",
                            hex::encode(txid),
                            e
                        );
                    }
                }
            }
        })
    }

    /// Detect transactions that have been stalled in Voting state (§7.6.1)
    ///
    /// Scans all transactions and identifies those that:
    /// 1. Are in Voting state
    /// 2. Have been voting for > STALL_TIMEOUT (30 seconds)
    /// 3. Are not already in FallbackResolution state
    /// 4. Are still valid (not conflicting with finalized transactions)
    ///
    /// # Returns
    /// * `Vec<Hash256>` - List of transaction IDs that are stalled
    fn detect_stalled_transactions(&self) -> Vec<Hash256> {
        let mut stalled = Vec::new();
        let now = chrono::Utc::now().timestamp_millis();

        for entry in self.timevote.tx_status.iter() {
            let txid = *entry.key();
            let status = entry.value();

            match status {
                TransactionStatus::Voting { started_at, .. } => {
                    let elapsed_ms = now - started_at;
                    let elapsed_secs = elapsed_ms / 1000;

                    // Check if transaction has stalled
                    if elapsed_secs >= STALL_TIMEOUT.as_secs() as i64 {
                        // Verify transaction is still valid before alerting
                        if self.is_transaction_still_valid(&txid) {
                            stalled.push(txid);
                            // Phase 5: Record stall detection metric
                            self.record_stall_detection();
                        } else {
                            tracing::debug!(
                                "Skipping stall alert for invalid tx {}",
                                hex::encode(txid)
                            );
                        }
                    }
                }
                TransactionStatus::FallbackResolution { .. } => {
                    // Already in fallback, don't re-alert
                    continue;
                }
                _ => {
                    // Not in voting state, skip
                    continue;
                }
            }
        }

        stalled
    }

    /// Check if a transaction is still valid for fallback resolution
    ///
    /// A transaction is invalid if:
    /// - It conflicts with a finalized transaction
    /// - Its inputs have been spent by a finalized transaction
    /// - It has been explicitly rejected
    ///
    /// # Arguments
    /// * `txid` - Transaction to check
    ///
    /// # Returns
    /// * `bool` - true if transaction is still valid
    fn is_transaction_still_valid(&self, txid: &Hash256) -> bool {
        // Check if transaction exists in pool
        let tx = match self.tx_pool.get_pending(txid) {
            Some(tx) => tx,
            None => {
                // Transaction no longer in pool
                return false;
            }
        };

        // Check if any inputs are spent by finalized transactions
        for input in &tx.inputs {
            if let Some(state) = self.utxo_manager.get_state(&input.previous_output) {
                match state {
                    UTXOState::SpentFinalized { .. } => {
                        // Input already spent by finalized tx
                        return false;
                    }
                    UTXOState::Archived { .. } => {
                        // Input spent and archived in block
                        return false;
                    }
                    _ => {
                        // Still valid
                        continue;
                    }
                }
            }
        }

        // Check if transaction has been explicitly rejected
        if let Some(status) = self.timevote.tx_status.get(txid) {
            if matches!(status.value(), TransactionStatus::Rejected { .. }) {
                return false;
            }
        }

        true
    }

    /// Get current slot index (10-minute epochs since genesis)
    ///
    /// Used for deterministic leader election in fallback protocol.
    /// Slot 0 = genesis time, increments every 10 minutes.
    ///
    /// # Returns
    /// * `u64` - Current slot index
    fn get_current_slot_index(&self) -> u64 {
        let now = chrono::Utc::now().timestamp();
        let genesis_time = 1735689600; // 2025-01-01 00:00:00 UTC
        let slot_duration = 600; // 10 minutes in seconds

        ((now - genesis_time).max(0) / slot_duration) as u64
    }

    /// Get average finality time in milliseconds
    pub fn get_avg_finality_time_ms(&self) -> u64 {
        let avg = self.avg_finality_ms.read();
        if avg.is_empty() {
            return 750; // Default value if no measurements yet
        }
        let sum: f64 = avg.iter().sum();
        (sum / avg.len() as f64) as u64
    }

    pub fn set_identity(
        &self,
        address: String,
        signing_key: ed25519_dalek::SigningKey,
    ) -> Result<(), String> {
        self.identity
            .set(NodeIdentity {
                address,
                signing_key,
            })
            .map_err(|_| "Identity already set".to_string())
    }

    /// Set the wallet signing key used to authorize spending of UTXOs.
    /// This is separate from the identity/consensus key (`set_identity`) which signs
    /// votes and blocks.  When `masternodeprivkey` is configured in time.conf the two
    /// keys differ; transaction signing must always use the wallet key so that the
    /// derived address matches the `script_pubkey` stored in the UTXOs.
    pub fn set_wallet_signing_key(&self, key: ed25519_dalek::SigningKey) -> Result<(), String> {
        self.wallet_signing_key
            .set(key)
            .map_err(|_| "Wallet signing key already set".to_string())
    }

    /// Get the signing key for this node (for VRF generation in block production)
    pub fn get_signing_key(&self) -> Option<ed25519_dalek::SigningKey> {
        self.identity.get().map(|id| id.signing_key.clone())
    }

    /// Sign all inputs of a transaction using this node's wallet key.
    /// Each input's script_sig is set to [32-byte pubkey || 64-byte Ed25519 signature].
    pub fn sign_transaction(&self, tx: &mut Transaction) -> Result<(), String> {
        // Use the dedicated wallet signing key when available.  Fall back to the
        // identity key only for nodes that have not called set_wallet_signing_key
        // (e.g. unit-test instances).  This ensures the derived address in the
        // signature always matches the UTXO's script_pubkey (wallet address).
        let signing_key = self
            .wallet_signing_key
            .get()
            .cloned()
            .or_else(|| self.get_signing_key())
            .ok_or("No signing key available — node identity not set")?;
        let pubkey_bytes = signing_key.verifying_key().to_bytes();

        for idx in 0..tx.inputs.len() {
            let message = self.create_signature_message(tx, idx)?;
            let signature = signing_key.sign(&message);
            let mut script_sig = Vec::with_capacity(96);
            script_sig.extend_from_slice(&pubkey_bytes);
            script_sig.extend_from_slice(&signature.to_bytes());
            tx.inputs[idx].script_sig = script_sig;
        }

        Ok(())
    }

    /// Get the wallet signing key (for memo encryption/decryption).
    pub fn get_wallet_signing_key(&self) -> Option<ed25519_dalek::SigningKey> {
        self.wallet_signing_key
            .get()
            .cloned()
            .or_else(|| self.get_signing_key())
    }

    /// Derive a child signing key deterministically from the master wallet key.
    /// Uses SHA-512 domain separation: H("TIMECOIN-KEY-DERIVATION" || master || index_le)[0..32].
    pub fn derive_child_key_at(&self, index: u32) -> Option<ed25519_dalek::SigningKey> {
        let master = self.wallet_signing_key.get()?;
        let master_bytes = master.to_bytes();
        let mut hasher = Sha512::new();
        hasher.update(b"TIMECOIN-KEY-DERIVATION");
        hasher.update(master_bytes);
        hasher.update(index.to_le_bytes());
        let output = hasher.finalize();
        let mut child_secret = [0u8; 32];
        child_secret.copy_from_slice(&output[..32]);
        Some(ed25519_dalek::SigningKey::from_bytes(&child_secret))
    }

    /// Register a derived address so it can be found for spending.
    pub fn register_derived_address(&self, address: String, index: u32) {
        self.derived_address_map.insert(address, index);
    }

    /// Pre-populate the derived address map from disk state on startup.
    /// Call once after set_wallet_signing_key with the persisted next_index.
    pub fn preload_derived_addresses(&self, count: u32, network: crate::network_type::NetworkType) {
        use crate::address::Address;
        for i in 0..count {
            if let Some(key) = self.derive_child_key_at(i) {
                let addr =
                    Address::from_public_key(key.verifying_key().as_bytes(), network).to_string();
                self.derived_address_map.insert(addr, i);
            }
        }
    }

    /// Return all derived addresses sorted by derivation index.
    pub fn list_derived_addresses(&self) -> Vec<(u32, String)> {
        let mut entries: Vec<(u32, String)> = self
            .derived_address_map
            .iter()
            .map(|e| (*e.value(), e.key().clone()))
            .collect();
        entries.sort_by_key(|(idx, _)| *idx);
        entries
    }

    /// Return the signing key that controls the given address.
    /// Checks derived addresses first (O(1)), then falls back to the master wallet key.
    pub fn get_signing_key_for_address(&self, address: &str) -> Option<ed25519_dalek::SigningKey> {
        if let Some(idx) = self.derived_address_map.get(address) {
            return self.derive_child_key_at(*idx);
        }
        self.wallet_signing_key
            .get()
            .cloned()
            .or_else(|| self.get_signing_key())
    }

    /// Return true if `address` is one of this node's derived child addresses.
    /// Used by `send_coins` as part of the self-send check; the master wallet address
    /// is handled separately by the caller via `to_address == from_address`.
    pub fn is_derived_address(&self, address: &str) -> bool {
        self.derived_address_map.contains_key(address)
    }

    /// Sign all transaction inputs with the key that controls `from_address`.
    pub fn sign_transaction_for_address(
        &self,
        tx: &mut Transaction,
        from_address: &str,
    ) -> Result<(), String> {
        let signing_key = self
            .get_signing_key_for_address(from_address)
            .ok_or_else(|| format!("No signing key for address {}", from_address))?;
        let pubkey_bytes = signing_key.verifying_key().to_bytes();
        for idx in 0..tx.inputs.len() {
            let message = self.create_signature_message(tx, idx)?;
            let signature = signing_key.sign(&message);
            let mut script_sig = Vec::with_capacity(96);
            script_sig.extend_from_slice(&pubkey_bytes);
            script_sig.extend_from_slice(&signature.to_bytes());
            tx.inputs[idx].script_sig = script_sig;
        }
        Ok(())
    }

    /// Encrypt a memo for a self-send (consolidation, merge).
    /// Uses the wallet's own public key as the recipient.
    pub fn encrypt_memo_for_self(&self, plaintext: &str) -> Result<Vec<u8>, String> {
        let signing_key = self
            .get_wallet_signing_key()
            .ok_or("No signing key available")?;
        let pubkey = signing_key.verifying_key().to_bytes();
        crate::memo::encrypt_memo(&signing_key, &pubkey, plaintext)
            .map_err(|e| format!("Memo encryption failed: {}", e))
    }

    /// Encrypt a memo for a send to another address.
    /// Looks up the recipient's Ed25519 public key from on-chain data.
    pub fn encrypt_memo_for_address(
        &self,
        plaintext: &str,
        recipient_address: &str,
    ) -> Result<Vec<u8>, String> {
        let signing_key = self
            .get_wallet_signing_key()
            .ok_or("No signing key available")?;

        // Look up recipient's Ed25519 pubkey from script_sig of a TX they signed
        let recipient_pubkey = self
            .utxo_manager
            .find_pubkey_for_address(recipient_address)
            .ok_or_else(|| {
                format!(
                    "Cannot encrypt memo: no known public key for address {}. \
                     The recipient must have at least one on-chain transaction.",
                    recipient_address
                )
            })?;

        crate::memo::encrypt_memo(&signing_key, &recipient_pubkey, plaintext)
            .map_err(|e| format!("Memo encryption failed: {}", e))
    }

    /// Try to decrypt a memo from a transaction. Returns None if we don't hold the key.
    pub fn decrypt_memo(&self, encrypted: &[u8]) -> Option<String> {
        let signing_key = self.get_wallet_signing_key()?;
        match crate::memo::decrypt_memo(&signing_key, encrypted) {
            Ok(result) => result,
            Err(e) => {
                tracing::debug!("Memo decryption failed: {}", e);
                None
            }
        }
    }

    // ========================================================================
    // FINALITY VOTE GENERATION (Per Protocol §8.5)
    // ========================================================================

    /// Generate a finality vote for a transaction if this validator is AVS-active
    /// Called when this validator responds with "Valid" during TimeVote consensus
    pub fn generate_finality_vote(
        &self,
        txid: Hash256,
        tx: &Transaction,
        slot_index: u64,
        snapshot: &AVSSnapshot,
    ) -> Option<FinalityVote> {
        // Get identity (returns None if not set)
        let identity = self.identity.get()?;
        let voter_mn_id = identity.address.clone();

        // Only generate vote if voter is in the AVS snapshot for this slot
        if !snapshot.contains_validator(&voter_mn_id) {
            return None;
        }

        // Get voter weight from snapshot
        let voter_weight = snapshot.get_validator_weight(&voter_mn_id)?;

        // Compute transaction hash commitment (SHA256 hash of canonical tx bytes)
        let tx_bytes = bincode::serialize(tx).ok()?;
        let tx_hash: [u8; 32] = Sha256::digest(&tx_bytes).into();

        let tx_hash_commitment: Hash256 = tx_hash;

        // Sign and create the vote using identity
        let vote = identity.sign_finality_vote(
            1, // TODO: Make chain_id configurable
            txid,
            tx_hash_commitment,
            slot_index,
            VoteDecision::Accept, // This vote is for a valid/preferred transaction
            voter_mn_id,
            voter_weight,
        );

        Some(vote)
    }

    /// Broadcast a finality vote to all peer masternodes
    /// Used by consensus to propagate votes across the network
    pub fn broadcast_finality_vote(&self, vote: FinalityVote) -> NetworkMessage {
        NetworkMessage::FinalityVoteBroadcast { vote }
    }

    /// Sign a TimeVote for a transaction (simplified version for vote request handling)
    /// Used when responding to TimeVoteRequest messages
    /// Returns None if node identity not set or node is not a masternode
    pub fn sign_timevote(
        &self,
        txid: Hash256,
        tx_hash_commitment: Hash256,
        slot_index: u64,
        decision: VoteDecision,
    ) -> Option<TimeVote> {
        // Get node identity
        let identity = self.identity.get()?;
        let voter_mn_id = identity.address.clone();

        // Get masternode info to determine weight
        let masternodes = self.get_masternodes();
        let mn = masternodes.iter().find(|mn| mn.address == voter_mn_id)?;
        let voter_weight = mn.tier.sampling_weight();

        // Sign and create the vote
        let vote = identity.sign_finality_vote(
            1, // TODO: Make chain_id configurable
            txid,
            tx_hash_commitment,
            slot_index,
            decision,
            voter_mn_id,
            voter_weight,
        );

        Some(vote)
    }

    // ========================================================================
    // MASTERNODE HELPERS
    // ========================================================================

    // Lock-free read of masternodes from registry
    fn get_masternodes(&self) -> Vec<Masternode> {
        // Get active masternodes from the registry (single source of truth)
        let active = self.masternode_registry.active_masternodes_cached();
        active.iter().map(|info| info.masternode.clone()).collect()
    }

    // Returns (Masternode, reward_address) pairs for block reward distribution
    fn get_masternodes_with_rewards(&self) -> Vec<(Masternode, String)> {
        let active = self.masternode_registry.active_masternodes_cached();
        active
            .iter()
            .map(|info| (info.masternode.clone(), info.reward_address.clone()))
            .collect()
    }

    fn is_masternode(&self, address: &str) -> bool {
        let masternodes = self.get_masternodes();
        masternodes.iter().any(|mn| mn.address == address)
    }

    #[allow(dead_code)]
    pub async fn set_broadcast_callback<F>(&self, callback: F)
    where
        F: Fn(NetworkMessage) + Send + Sync + 'static,
    {
        *self.broadcast_callback.write().await = Some(Arc::new(callback));
    }

    async fn broadcast(&self, msg: NetworkMessage) {
        if let Some(callback) = self.broadcast_callback.read().await.as_ref() {
            callback(msg);
        } else {
            tracing::error!("❌ Broadcast attempted but callback not set!");
        }
    }

    /// Broadcast TimeProof to all network peers (Protocol §8.2)
    pub async fn broadcast_timeproof(&self, proof: TimeProof) {
        tracing::info!(
            "📡 Broadcasting TimeProof for TX {} to network",
            hex::encode(proof.txid)
        );
        self.broadcast(NetworkMessage::TimeProofBroadcast { proof })
            .await;
    }

    /// Broadcast a payment request to all peers
    pub async fn broadcast_payment_request(
        &self,
        request: crate::network::message::PaymentRequest,
    ) {
        tracing::info!(
            "📡 Broadcasting PaymentRequest {} from {} to {}",
            &request.id[..std::cmp::min(16, request.id.len())],
            request.from_address,
            request.to_address,
        );
        self.broadcast(NetworkMessage::PaymentRequestRelay(request))
            .await;
    }

    /// Broadcast a payment request response to all peers.
    pub async fn broadcast_payment_request_response(
        &self,
        id: String,
        requester_address: String,
        payer_address: String,
        accepted: bool,
        txid: Option<String>,
    ) {
        self.broadcast(NetworkMessage::PaymentRequestResponse {
            id,
            requester_address,
            payer_address,
            accepted,
            txid,
        })
        .await;
    }

    /// Broadcast a payment request cancellation to all peers.
    pub async fn broadcast_payment_request_cancelled(&self, id: String, requester_address: String) {
        self.broadcast(NetworkMessage::PaymentRequestCancelled {
            id,
            requester_address,
        })
        .await;
    }

    /// Broadcast a payment-request-viewed notification to all peers.
    pub async fn broadcast_payment_request_viewed(
        &self,
        id: String,
        requester_address: String,
        payer_address: String,
    ) {
        self.broadcast(NetworkMessage::PaymentRequestViewed {
            id,
            requester_address,
            payer_address,
        })
        .await;
    }

    /// Store a payment request, enforcing per-address limits and dedup.
    /// Returns true if stored (new), false if duplicate or limit reached.
    pub fn store_payment_request(&self, request: crate::network::message::PaymentRequest) -> bool {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64;

        // Reject expired requests
        if request.expires <= now {
            return false;
        }

        let mut entry = self
            .payment_requests
            .entry(request.to_address.clone())
            .or_default();

        // Dedup by id
        if entry.iter().any(|r| r.id == request.id) {
            return false;
        }

        // Max 100 pending requests per address
        if entry.len() >= 100 {
            return false;
        }

        entry.push(request);
        true
    }

    /// Remove expired payment requests from the store
    pub fn cleanup_expired_payment_requests(&self) {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64;

        let mut empty_keys = Vec::new();
        for mut entry in self.payment_requests.iter_mut() {
            entry.value_mut().retain(|r| r.expires > now);
            if entry.value().is_empty() {
                empty_keys.push(entry.key().clone());
            }
        }
        for key in empty_keys {
            self.payment_requests.remove(&key);
        }
    }

    /// Get pending payment requests for a set of addresses
    pub fn get_payment_requests_for(
        &self,
        addresses: &[String],
    ) -> Vec<crate::network::message::PaymentRequest> {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64;

        let mut results = Vec::new();
        for addr in addresses {
            if let Some(reqs) = self.payment_requests.get(addr) {
                for r in reqs.iter() {
                    if r.expires > now {
                        results.push(r.clone());
                    }
                }
            }
        }
        results
    }

    /// Return the payer address (to_address) for a payment request, if it exists.
    pub fn get_payment_request_payer(&self, request_id: &str) -> Option<String> {
        for entry in self.payment_requests.iter() {
            if let Some(r) = entry.value().iter().find(|r| r.id == request_id) {
                return Some(r.to_address.clone());
            }
        }
        None
    }

    /// Return the requester address (from_address) for a payment request, if it exists.
    pub fn get_payment_request_requester(&self, request_id: &str) -> Option<String> {
        for entry in self.payment_requests.iter() {
            if let Some(r) = entry.value().iter().find(|r| r.id == request_id) {
                return Some(r.from_address.clone());
            }
        }
        None
    }

    /// Remove a payment request by id
    pub fn remove_payment_request(&self, request_id: &str) -> bool {
        for mut entry in self.payment_requests.iter_mut() {
            if let Some(pos) = entry.value().iter().position(|r| r.id == request_id) {
                entry.value_mut().remove(pos);
                return true;
            }
        }
        false
    }

    pub async fn validate_transaction(&self, tx: &Transaction) -> Result<(), String> {
        self.validate_transaction_with_locks(tx, tx.txid())
            .await
            .map(|_| ())
    }

    /// Validate transaction, allowing UTXOs locked by the specified txid
    /// Returns the calculated fee on success.
    async fn validate_transaction_with_locks(
        &self,
        tx: &Transaction,
        our_txid: Hash256,
    ) -> Result<u64, String> {
        // 0. AI-powered validation first (if enabled)
        if let Some(ai_validator) = &self.ai_validator {
            ai_validator.validate_with_ai(tx).await?;
        }

        // 1. Check transaction size limit
        let tx_size = bincode::serialize(tx)
            .map_err(|e| format!("Failed to serialize transaction: {}", e))?
            .len();

        if tx_size > MAX_TX_SIZE {
            return Err(format!(
                "Transaction too large: {} bytes (max {} bytes)",
                tx_size, MAX_TX_SIZE
            ));
        }

        // 1b. Special no-value transactions (MasternodeReg, CollateralUnlock) carry no
        // inputs or outputs — they are control messages, not value transfers.  Skip all
        // economic checks (input/output balance, dust, minimum send, fee) for these.
        // Structural / signature validity is enforced in blockchain.rs when the containing
        // block is applied, so we just accept them here without further checks.
        //
        // AV41: validate special_data fields before accepting into the mempool.
        // An attacker can craft a TX with MasternodeRegistration { empty fields } that
        // satisfies is_masternode_reg() but carries no meaningful payload.  Without this
        // check such ghost TXs would pass all guards and sit in the mempool indefinitely.
        if tx.is_masternode_reg() || tx.is_masternode_dereg() {
            if let Some(ref sd) = tx.special_data {
                if let Err(reason) = sd.validate_fields() {
                    return Err(format!("Invalid special_data fields (AV41): {}", reason));
                }
            }
            return Ok(0);
        }
        if let Some(ref sd) = tx.special_data {
            if let Err(reason) = sd.validate_fields() {
                return Err(format!("Invalid special_data fields (AV41): {}", reason));
            }
        }

        // 2. Check inputs exist and are unspent (or locked/finalized by this tx).
        // Track whether every input is already finalized so we can skip fee/signature
        // re-validation for TXs that were already processed by TimeVote consensus.
        // After finalization, input UTXOs are tombstoned (removed from sled) so the
        // normal get_utxo path would return "UTXO not found" — causing false rejections
        // of valid block proposals containing finalized transactions.
        let mut all_inputs_finalized = !tx.inputs.is_empty();
        for input in &tx.inputs {
            // Check if UTXO is locked as masternode collateral (separate from UTXO state)
            if self
                .utxo_manager
                .is_collateral_locked(&input.previous_output)
            {
                return Err(format!(
                    "UTXO {} is locked as masternode collateral",
                    input.previous_output
                ));
            }

            let is_tombstoned = self.utxo_manager.is_tombstoned(&input.previous_output);
            match self.utxo_manager.get_state(&input.previous_output) {
                Some(UTXOState::Unspent) => {
                    all_inputs_finalized = false;
                }
                Some(UTXOState::Locked { txid, .. }) if txid == our_txid => {
                    // OK - locked by this transaction
                    all_inputs_finalized = false;
                }
                Some(UTXOState::SpentPending { txid, .. }) if txid == our_txid => {
                    // OK - voting in progress for this transaction
                    all_inputs_finalized = false;
                }
                Some(UTXOState::SpentFinalized { txid, .. }) if txid == our_txid => {
                    // OK - already finalized by this transaction; UTXO is tombstoned
                }
                None if is_tombstoned => {
                    // After restart, DashMap is empty but tombstone survives in sled.
                    // Tombstone = UTXO was finalized and removed; valid for block inclusion.
                }
                Some(state) => {
                    return Err(format!("UTXO not unspent: {}", state));
                }
                None => {
                    // Not in DashMap and not tombstoned. Unspent UTXOs on nodes that
                    // never explicitly locked this input only exist in sled — check there
                    // before declaring it missing.
                    if self
                        .utxo_manager
                        .get_utxo(&input.previous_output)
                        .await
                        .is_err()
                    {
                        return Err("UTXO not found".to_string());
                    }
                    all_inputs_finalized = false;
                }
            }
        }

        // All inputs are tombstoned/finalized — the TX was fully validated during
        // TimeVote finalization (fee, balance, signatures). Skip re-validation since
        // the UTXOs are no longer in sled and get_utxo would return errors.
        if all_inputs_finalized {
            return Ok(0);
        }

        // 3. Check input values >= output values (no inflation)
        let mut input_sum = 0u64;
        let mut input_address: Option<String> = None;
        let mut single_input_address = true;
        for input in &tx.inputs {
            if let Ok(utxo) = self.utxo_manager.get_utxo(&input.previous_output).await {
                input_sum += utxo.value;
                match &input_address {
                    None => input_address = Some(utxo.address.clone()),
                    Some(a) if *a != utxo.address => single_input_address = false,
                    _ => {}
                }
            } else {
                return Err("UTXO not found".to_string());
            }
        }
        // True self-send: all inputs from one address, all outputs back to that same address.
        // Used to exempt consolidations from the proportional fee check.
        let is_self_send_consolidation = single_input_address
            && input_address.as_deref().is_some_and(|addr| {
                tx.outputs.iter().all(|o| {
                    std::str::from_utf8(&o.script_pubkey)
                        .map(|s| s == addr)
                        .unwrap_or(false)
                })
            });

        let output_sum: u64 = tx.outputs.iter().map(|o| o.value).sum();

        // 4. Dust prevention - reject outputs below threshold
        for output in &tx.outputs {
            if output.value > 0 && output.value < DUST_THRESHOLD {
                return Err(format!(
                    "Dust output detected: {} satoshis (minimum {})",
                    output.value, DUST_THRESHOLD
                ));
            }
        }

        // 4b. Minimum send amount: 1 TIME (100_000_000 satoshis).
        {
            let send_amount = output_sum;
            if send_amount < SATOSHIS_PER_TIME {
                return Err(format!(
                    "Send amount too small: {} satoshis (minimum 1 TIME = {} satoshis)",
                    send_amount, SATOSHIS_PER_TIME
                ));
            }
        }

        // 5. Calculate and validate fee
        let actual_fee = input_sum.saturating_sub(output_sum);

        // Require minimum absolute fee
        if actual_fee < MIN_TX_FEE {
            return Err(format!(
                "Transaction fee too low: {} satoshis (minimum {})",
                actual_fee, MIN_TX_FEE
            ));
        }

        // Check tiered proportional fee (governance-adjustable schedule).
        // Consolidations (all inputs and outputs share the same address) are exempt and
        // only need to cover MIN_TX_FEE — already checked above.
        if !is_self_send_consolidation {
            let fee_schedule = self.current_fee_schedule();
            let send_amount = tx.outputs.first().map(|o| o.value).unwrap_or(output_sum);
            let min_proportional_fee = fee_schedule.required_fee(send_amount);

            if actual_fee < min_proportional_fee {
                return Err(format!(
                    "Insufficient fee: {} satoshis < {} satoshis required for send amount {}",
                    actual_fee, min_proportional_fee, send_amount
                ));
            }
        }

        if input_sum < output_sum {
            return Err(format!(
                "Insufficient funds: {} < {}",
                input_sum, output_sum
            ));
        }

        // ===== CRITICAL FIX #1: VERIFY SIGNATURES ON ALL INPUTS =====
        // Reject transactions with unsigned inputs — all inputs must have signatures
        for (idx, input) in tx.inputs.iter().enumerate() {
            if input.script_sig.is_empty() {
                return Err(format!(
                    "Input {} has empty script_sig — unsigned transactions are not allowed",
                    idx
                ));
            }
            self.verify_input_signature(tx, idx).await?;
        }

        tracing::debug!(
            "✅ Transaction signatures verified: {} inputs, {} outputs",
            tx.inputs.len(),
            tx.outputs.len()
        );

        Ok(actual_fee)
    }

    /// Create the message that should be signed for a transaction input
    /// Message format: SHA256(txid || input_index || outputs_hash)
    /// This prevents signature reuse and output tampering attacks
    fn create_signature_message(
        &self,
        tx: &Transaction,
        input_idx: usize,
    ) -> Result<Vec<u8>, String> {
        // Compute transaction hash with script_sigs cleared to avoid
        // chicken-and-egg: signer has empty sigs, verifier has filled sigs.
        // encrypted_memo is also excluded so that attaching a memo after
        // signing does not invalidate the signature (memo is metadata, not
        // part of the UTXO commitment). This matches the wallet's hash().
        let mut signing_tx = tx.clone();
        for input in &mut signing_tx.inputs {
            input.script_sig = vec![];
        }
        signing_tx.encrypted_memo = None;
        let tx_hash = signing_tx.txid();

        // Create message.
        //   v1: txid || input_index || outputs_hash
        //   v2: CHAIN_ID(4 LE) || txid || input_index || outputs_hash
        // v2 activates at REPLAY_PROTECTION_ACTIVATION_HEIGHT (AV-REPLAY).
        let mut message = Vec::new();

        if tx.version >= 2 {
            message.extend_from_slice(&crate::constants::CHAIN_ID.to_le_bytes());
        }

        // Add transaction hash (32 bytes)
        message.extend_from_slice(&tx_hash);

        // Add input index (4 bytes, little-endian)
        message.extend_from_slice(&(input_idx as u32).to_le_bytes());

        // Add hash of all outputs (prevents output amount tampering)
        let outputs_bytes = bincode::serialize(&tx.outputs)
            .map_err(|e| format!("Failed to serialize outputs: {}", e))?;
        let outputs_hash = Sha256::digest(&outputs_bytes);
        message.extend_from_slice(&outputs_hash);

        Ok(message)
    }

    /// Verify a single input's cryptographic signature
    /// script_sig format: [32-byte Ed25519 pubkey || 64-byte signature]
    /// The pubkey is verified against the UTXO's address (script_pubkey stores address bytes)
    async fn verify_input_signature(
        &self,
        tx: &Transaction,
        input_idx: usize,
    ) -> Result<(), String> {
        // Get the input
        let input = tx.inputs.get(input_idx).ok_or("Input index out of range")?;

        // Get the UTXO being spent (async operation)
        let utxo = self
            .utxo_manager
            .get_utxo(&input.previous_output)
            .await
            .map_err(|e| format!("UTXO not found: {:?} - {}", input.previous_output, e))?;

        // Create the message that should have been signed
        let message = self.create_signature_message(tx, input_idx)?;

        // Clone data needed for blocking task
        let addr_bytes = utxo.script_pubkey.clone();
        let script_sig = input.script_sig.clone();

        // Move CPU-intensive signature verification to blocking pool
        tokio::task::spawn_blocking(move || {
            use ed25519_dalek::Signature;

            // script_sig = [32-byte Ed25519 pubkey || 64-byte signature]
            if script_sig.len() != 96 {
                return Err(format!(
                    "Invalid script_sig length: {} (expected 96: 32-byte pubkey + 64-byte signature)",
                    script_sig.len()
                ));
            }

            let pubkey_bytes: [u8; 32] = script_sig[..32]
                .try_into()
                .map_err(|_| "Failed to extract public key bytes")?;
            let sig_bytes: [u8; 64] = script_sig[32..96]
                .try_into()
                .map_err(|_| "Failed to extract signature bytes")?;

            // Parse Ed25519 public key
            let public_key = ed25519_dalek::VerifyingKey::from_bytes(&pubkey_bytes)
                .map_err(|e| format!("Invalid public key: {}", e))?;

            // Verify public key matches UTXO's address
            let addr_str = String::from_utf8(addr_bytes.clone())
                .map_err(|_| "Invalid UTF-8 in UTXO script_pubkey")?;
            let network = if addr_str.starts_with("TIME0") {
                crate::NetworkType::Testnet
            } else if addr_str.starts_with("TIME1") {
                crate::NetworkType::Mainnet
            } else {
                return Err("Invalid address prefix in UTXO script_pubkey".to_string());
            };
            let derived_addr =
                crate::address::Address::from_public_key(pubkey_bytes.as_slice(), network)
                    .to_string();
            if derived_addr.as_bytes() != addr_bytes.as_slice() {
                return Err(format!(
                    "Public key doesn't match UTXO address: derived {} vs stored {}",
                    derived_addr, addr_str
                ));
            }

            // Verify Ed25519 signature
            let signature = Signature::from_bytes(&sig_bytes);
            public_key.verify_strict(&message, &signature).map_err(|_| {
                format!(
                    "Signature verification FAILED for input {}: signature doesn't match message",
                    input_idx
                )
            })?;

            Ok::<(), String>(())
        })
        .await
        .map_err(|e| format!("Signature verification task failed: {}", e))?
        .map_err(|e| {
            tracing::warn!(
                "Signature verification failed for input {}: {}",
                input_idx,
                e
            );
            e
        })?;

        // Cache the verified pubkey for memo encryption lookup
        let input = &tx.inputs[input_idx];
        if input.script_sig.len() >= 32 {
            let pubkey_bytes: [u8; 32] = input.script_sig[..32].try_into().unwrap_or([0u8; 32]);
            let utxo = self.utxo_manager.get_utxo(&input.previous_output).await;
            if let Ok(utxo) = utxo {
                self.utxo_manager
                    .register_pubkey(&utxo.address, pubkey_bytes);
            }
        }

        tracing::debug!("✅ Signature verified for input {}", input_idx);

        Ok(())
    }

    /// Returns true when another in-pool transaction (pending or confirmed) spends an
    /// overlapping input, or a peer has locked/spent an input for a different TX.
    pub fn has_double_spend_conflict(&self, inputs: &[TxInput], exclude_txid: &Hash256) -> bool {
        if self
            .tx_pool
            .has_conflicting_transaction(inputs, exclude_txid)
        {
            return true;
        }

        for input in inputs {
            let outpoint = &input.previous_output;
            if matches!(
                self.utxo_manager.get_state(outpoint),
                Some(UTXOState::Locked { txid, .. })
                    | Some(UTXOState::SpentPending { txid, .. })
                    | Some(UTXOState::SpentFinalized { txid, .. })
                    | Some(UTXOState::Archived { txid, .. })
                    if txid != *exclude_txid
            ) {
                return true;
            }
        }

        false
    }

    /// Returns true when any input is already spent/finalized by a different transaction.
    /// Unlike `has_double_spend_conflict`, this is a hard reject (no TimeVote resolution).
    pub fn inputs_already_spent_by_other(&self, inputs: &[TxInput], our_txid: &Hash256) -> bool {
        for input in inputs {
            let outpoint = &input.previous_output;
            match self.utxo_manager.get_state(outpoint) {
                Some(UTXOState::SpentFinalized { txid, .. })
                | Some(UTXOState::SpentPending { txid, .. })
                | Some(UTXOState::Archived { txid, .. })
                    if txid != *our_txid =>
                {
                    return true;
                }
                _ => {}
            }

            if self.utxo_manager.is_tombstoned(outpoint) {
                match self.utxo_manager.get_state(outpoint) {
                    Some(UTXOState::SpentFinalized { txid, .. }) if txid == *our_txid => {}
                    _ => return true,
                }
            }
        }

        false
    }

    /// Submit a new transaction to the network with lock-based double-spend prevention.
    /// Returns the validated fee on success.
    ///
    /// This implements the instant finality protocol:
    /// 1. ATOMICALLY lock UTXOs and validate transaction
    /// 2. Broadcast to network
    /// 3. Collect votes from masternodes
    /// 4. Finalize (simple majority) or reject
    #[allow(dead_code)]
    pub async fn lock_and_validate_transaction(&self, tx: &Transaction) -> Result<u64, String> {
        let txid = tx.txid();
        let now = chrono::Utc::now().timestamp();

        // CRITICAL: Attempt to lock ALL inputs BEFORE validation
        // This is atomic from the perspective of the consensus engine
        for input in &tx.inputs {
            self.utxo_manager
                .lock_utxo(&input.previous_output, txid)
                .map_err(|e| format!("UTXO double-spend prevented: {}", e))?;
        }

        // Now validate knowing inputs are locked (pass txid so validation knows these locks are ours)
        let fee = match self.validate_transaction_with_locks(tx, txid).await {
            Ok(fee) => fee,
            Err(e) => {
                // Validation failed - unlock everything
                for input in &tx.inputs {
                    self.utxo_manager
                        .update_state(&input.previous_output, UTXOState::Unspent);
                }
                return Err(e);
            }
        };

        // Notify clients of locks
        for input in &tx.inputs {
            let old_state = Some(UTXOState::Unspent);
            let new_state = UTXOState::Locked {
                txid,
                locked_at: now,
            };
            self.state_notifier
                .notify_state_change(input.previous_output.clone(), old_state, new_state)
                .await;

            // Also broadcast lock state to network
            self.broadcast(NetworkMessage::UTXOStateUpdate {
                outpoint: input.previous_output.clone(),
                state: UTXOState::Locked {
                    txid,
                    locked_at: now,
                },
            })
            .await;
        }

        Ok(fee)
    }

    /// Submit a new transaction to the network
    /// This implements the instant finality protocol:
    /// 1. Validate transaction
    /// 2. Lock UTXOs
    /// 3. Broadcast to network
    /// 4. Collect votes from masternodes
    /// 5. Finalize (simple majority) or reject
    pub async fn submit_transaction(&self, tx: Transaction) -> Result<Hash256, String> {
        let txid = tx.txid();
        let txid_hex = hex::encode(txid);

        tracing::info!("🔍 Validating transaction {}...", &txid_hex[..16]);

        // FIX: Check broadcast callback early - fail fast if not available
        // This prevents transactions from being locked and then stuck forever
        {
            let callback_guard = self.broadcast_callback.read().await;
            if callback_guard.is_none() {
                tracing::error!("❌ No broadcast callback available - cannot process transactions");
                return Err(
                    "Network not initialized - broadcast callback not available".to_string()
                );
            }
        }

        // Step 1: Atomically lock and validate (returns the validated fee)
        let validated_fee = match self.lock_and_validate_transaction(&tx).await {
            Ok(fee) => fee,
            Err(e) => {
                tracing::error!(
                    "❌ Transaction {} validation FAILED: {}",
                    &txid_hex[..16],
                    e
                );
                // If lock_and_validate fails, UTXOs may be locked - unlock them
                self.unlock_transaction_inputs(&tx, &txid).await;
                return Err(e);
            }
        };

        tracing::info!("✅ Transaction {} validation passed", &txid_hex[..16]);

        // Step 2: Broadcast transaction to network FIRST
        // This ensures validators receive the TX before vote requests
        self.broadcast(NetworkMessage::TransactionBroadcast(tx.clone()))
            .await;
        tracing::info!("📡 Broadcast transaction {} to network", &txid_hex[..16]);

        // Step 3: Process transaction through consensus locally (this adds to pool)
        // AND broadcasts vote request - validators will have received TX by now
        tracing::debug!("🗳️  Starting consensus for transaction {}", &txid_hex[..16]);
        if let Err(e) = self
            .process_transaction(tx.clone(), Some(validated_fee))
            .await
        {
            tracing::error!(
                "❌ Transaction {} consensus processing FAILED: {}",
                &txid_hex[..16],
                e
            );
            // If processing fails, unlock the inputs
            self.unlock_transaction_inputs(&tx, &txid).await;
            return Err(e);
        }

        Ok(txid)
    }

    /// Remove a TX from the pending pool, unlock its inputs, and mark it Rejected.
    pub async fn reject_failed_voting_transaction(&self, txid: Hash256, reason: String) {
        let tx = self.tx_pool.get_pending(&txid);
        self.tx_pool.reject_transaction(txid, reason.clone());
        if let Some(tx) = tx {
            self.unlock_transaction_inputs(&tx, &txid).await;
        }
        self.transition_to_rejected(txid, reason);
    }

    /// Helper to unlock transaction inputs
    async fn unlock_transaction_inputs(&self, tx: &Transaction, txid: &Hash256) {
        for input in &tx.inputs {
            // Only unlock if it's still locked by this transaction
            if let Some(UTXOState::Locked {
                txid: locked_txid, ..
            }) = self.utxo_manager.get_state(&input.previous_output)
            {
                if locked_txid == *txid {
                    self.utxo_manager
                        .update_state(&input.previous_output, UTXOState::Unspent);
                    tracing::debug!(
                        "Unlocked UTXO {:?} after transaction failure",
                        input.previous_output
                    );
                }
            }
        }
    }

    pub async fn process_transaction(
        &self,
        tx: Transaction,
        validated_fee: Option<u64>,
    ) -> Result<(), String> {
        let txid = tx.txid();
        let masternodes = self.get_masternodes();
        let n = masternodes.len() as u32;

        if n == 0 {
            return Err("No masternodes available".to_string());
        }

        // AV39/AV41: Reject structurally null transactions before touching any state.
        // Masternode reg/dereg TXs legitimately have no inputs/outputs (they carry
        // special_data instead), but the special_data must pass full validation.
        // Ghost TXs exploit the is_some() check by setting invalid special_data.
        if tx.inputs.is_empty() && tx.outputs.is_empty() {
            let valid = tx.special_data.as_ref().is_some_and(|sd| {
                sd.validate_fields().is_ok()
                    && sd.verify_signature().is_ok()
                    && sd.verify_address_binding().is_ok()
            });
            if !valid {
                return Err(
                    "Ghost TX rejected: no inputs/outputs and no valid special_data".to_string(),
                );
            }
        } else {
            if tx.inputs.is_empty() && tx.special_data.is_none() {
                return Err("Transaction has no inputs".to_string());
            }
            if tx.outputs.is_empty() && tx.special_data.is_none() {
                return Err("Transaction has no outputs".to_string());
            }
        }

        // Reject new v1 transactions: the wallet now generates v2 (CHAIN_ID-prefixed sigs).
        // v1 TXs that were finalized before this fix are handled by produce_block_at_height
        // via a legacy exception; new ones must not enter the pool.
        if !tx.inputs.is_empty() && tx.version < 2 {
            return Err(format!(
                "Transaction {} rejected: version 1 is no longer accepted (upgrade your wallet to generate v2 transactions)",
                hex::encode(txid)
            ));
        }

        if !tx.inputs.is_empty() && self.inputs_already_spent_by_other(&tx.inputs, &txid) {
            return Err(format!(
                "Transaction {} rejected: input already spent by another transaction",
                hex::encode(txid)
            ));
        }

        // UTXOs are already in Locked state - DO NOT transition to SpentPending here
        // That transition happens when voting actually starts (after broadcast)

        // Use the validated fee if provided (from lock_and_validate_transaction),
        // otherwise recalculate from UTXOs (network-received transactions).
        let fee = if let Some(f) = validated_fee {
            f
        } else {
            let input_sum: u64 = {
                let mut sum = 0u64;
                let mut missing = 0u32;
                for input in &tx.inputs {
                    if let Ok(utxo) = self.utxo_manager.get_utxo(&input.previous_output).await {
                        sum += utxo.value;
                    } else {
                        missing += 1;
                    }
                }
                if missing > 0 {
                    tracing::warn!(
                        "⚠️ Fee calculation for TX {}: {} of {} input UTXOs not found",
                        hex::encode(txid),
                        missing,
                        tx.inputs.len()
                    );
                }
                sum
            };
            let output_sum: u64 = tx.outputs.iter().map(|o| o.value).sum();
            let computed = input_sum.saturating_sub(output_sum);
            // If all UTXOs were tombstoned (inputs spent before this peer received the
            // broadcast), fall back to the fee already recorded in the pool — the TX
            // was validated with the correct fee on an earlier pass or via mempool sync.
            if computed == 0 && input_sum == 0 && !tx.inputs.is_empty() {
                self.tx_pool.get_fee(&txid).unwrap_or(0)
            } else {
                computed
            }
        };

        // Check mempool limits before adding
        let pending_count = self.tx_pool.pending_count();
        if pending_count >= MAX_MEMPOOL_TRANSACTIONS {
            return Err(format!(
                "Mempool full: {} transactions (max {})",
                pending_count, MAX_MEMPOOL_TRANSACTIONS
            ));
        }

        // Note: TransactionPool.add_pending() handles byte-size tracking internally
        self.tx_pool
            .add_pending(tx.clone(), fee)
            .map_err(|e| format!("Failed to add to pool: {}", e))?;

        // ===== timevote CONSENSUS INTEGRATION =====
        // Conflict-only voting: check pool + UTXO lock/spent state for competing TXs.
        // If no conflict, auto-finalize immediately — 67% consensus is only needed when two
        // transactions compete for the same UTXO (genuine double-spend scenario).
        // Special TXs (masternode ops) have no inputs and are always conflict-free.
        let has_conflict = self.has_double_spend_conflict(&tx.inputs, &txid);

        if has_conflict {
            tracing::warn!(
                "⚠️ TX {} conflicts with another double-spend — initiating TimeVote consensus",
                hex::encode(txid)
            );
        } else {
            tracing::info!(
                "✅ TX {} has no competing double-spend — auto-finalizing (conflict-only voting)",
                hex::encode(txid)
            );
        }

        // Auto-finalize only when uncontested. Conflicts always enter TimeVote even if
        // validator count is low — never auto-finalize competing TXs.
        if !has_conflict {
            // Move directly to finalized pool
            // Get TX before finalizing since PoolEntry is private
            let tx_for_broadcast = tx.clone();
            self.tx_pool.finalize_transaction(txid); // Drop private return type

            if self.tx_pool.is_finalized(&txid) {
                tracing::info!("✅ TX {} auto-finalized", hex::encode(txid));

                // CRITICAL: Transition UTXOs from Locked → SpentFinalized
                // Without this, other nodes reject blocks containing this TX
                // because the UTXOs are still in Locked state.
                // mark_timevote_finalized also removes from sled so they don't
                // resurrect as Unspent after a node restart.
                for input in &tx.inputs {
                    self.utxo_manager
                        .mark_timevote_finalized(&input.previous_output, txid)
                        .await;
                }

                // Create new UTXOs from transaction outputs (change + recipient)
                for (idx, output) in tx.outputs.iter().enumerate() {
                    let outpoint = OutPoint {
                        txid,
                        vout: idx as u32,
                    };
                    let utxo = UTXO {
                        outpoint: outpoint.clone(),
                        value: output.value,
                        script_pubkey: output.script_pubkey.clone(),
                        address: String::from_utf8(output.script_pubkey.clone())
                            .unwrap_or_default(),
                        masternode_key: None,
                    };
                    if let Err(e) = self.utxo_manager.add_utxo(utxo).await {
                        tracing::warn!("Failed to add output UTXO vout={}: {}", idx, e);
                    }
                    self.utxo_manager
                        .update_state(&outpoint, UTXOState::Unspent);
                }

                // Broadcast finalization to all nodes so they also finalize it
                // Include the transaction itself so nodes can add it if they don't have it
                self.broadcast(NetworkMessage::TransactionFinalized {
                    txid,
                    tx: tx_for_broadcast,
                })
                .await;
                tracing::info!(
                    "📡 Broadcast TransactionFinalized for {:?}",
                    hex::encode(txid)
                );
            }

            // Record finalization
            self.timevote
                .finalized_txs
                .insert(txid, (Preference::Accept, Instant::now()));

            // Update status to Finalized
            self.timevote.tx_status.insert(
                txid,
                TransactionStatus::Finalized {
                    finalized_at: chrono::Utc::now().timestamp_millis(),
                    vfp_weight: 0,
                },
            );

            // Notify WS subscribers about finalized transaction
            self.signal_tx_finalized(txid);

            return Ok(());
        }

        // Initiate consensus tracking for fallback protocol
        let tx_state = Arc::new(RwLock::new(VotingState::new(Preference::Accept)));
        self.timevote.tx_state.insert(txid, tx_state);

        // §7.6 Integration: Set initial transaction status to Voting
        // Calculate transaction hash commitment (Protocol §8.1)
        let tx_hash_commitment = TimeVote::calculate_tx_commitment(&tx);

        // Get slot_index for replay protection and AVS snapshot lookup
        // Per Protocol §9.1: slot_time = slot_index * 600 (BLOCK_INTERVAL)
        // TODO: Use blockchain height once blockchain reference is added to ConsensusEngine
        // For now, derive from current timestamp: slot_index = timestamp / BLOCK_INTERVAL
        const BLOCK_INTERVAL: u64 = 600; // 10 minutes
        let slot_index = chrono::Utc::now().timestamp() as u64 / BLOCK_INTERVAL;

        // Create TimeVoteRequest message with all required fields
        // FIX: Include transaction data so validators can process immediately
        // This eliminates the need for a delay waiting for broadcast propagation
        let vote_request_msg = NetworkMessage::TimeVoteRequest {
            txid,
            tx_hash_commitment,
            slot_index,
            tx: Some(tx.clone()), // Include TX so validators have it immediately
        };

        // FIX: No delay needed! Validators will have TX from the vote request itself
        // This makes finality truly event-driven and eliminates arbitrary timing

        if let Some(callback) = self.broadcast_callback.read().await.as_ref() {
            tracing::info!(
                "📡 Broadcasting TimeVoteRequest for TX {} (slot {}) to all validators",
                hex::encode(txid),
                slot_index
            );
            callback(vote_request_msg.clone());
        }
        // NOTE: No else branch needed - we check broadcast_callback at start of submit_transaction()

        self.transition_to_voting(txid);

        // Spawn consensus monitoring task
        let consensus = self.timevote.clone();
        let tx_pool = self.tx_pool.clone();
        let consensus_engine_clone = Arc::new(ConsensusEngine {
            masternode_registry: self.masternode_registry.clone(),
            identity: OnceLock::new(),
            wallet_signing_key: OnceLock::new(),
            utxo_manager: self.utxo_manager.clone(),
            tx_pool: self.tx_pool.clone(),
            broadcast_callback: self.broadcast_callback.clone(),
            state_notifier: self.state_notifier.clone(),
            timevote: self.timevote.clone(),
            finality_proof_mgr: self.finality_proof_mgr.clone(),
            ai_validator: self.ai_validator.clone(),
            finality_times: self.finality_times.clone(),
            avg_finality_ms: self.avg_finality_ms.clone(),
            prev_block_hash: self.prev_block_hash.clone(),
            tx_finalized_sender: self.tx_finalized_sender.clone(),
            payment_requests: self.payment_requests.clone(),
            fee_schedule: self.fee_schedule.clone(),
            derived_address_map: DashMap::new(),
        });
        let tx_status_map = self.timevote.tx_status.clone();
        let finalized_signal = self.tx_finalized_sender.clone();

        // PRIORITY: Spawn with high priority for instant finality
        tokio::spawn(async move {
            // The TimeVoteResponse handler finalizes when the 67% threshold is met.
            // This loop monitors for that finalization; on timeout it only
            // auto-finalizes if quorum was actually reached — otherwise rejects.
            let initial_deadline = Duration::from_secs(5);
            let max_deadline = Duration::from_secs(15);
            let poll_interval = Duration::from_millis(50);
            let start = Instant::now();
            let mut vote_deadline = initial_deadline;

            loop {
                // Check if already finalized (by server.rs TimeVoteResponse handler)
                if consensus.finalized_txs.contains_key(&txid) {
                    tracing::debug!(
                        "✅ TX {} finalized via TimeVote (detected by voting loop)",
                        hex::encode(txid)
                    );
                    break;
                }

                if tx_pool.is_finalized(&txid) {
                    tracing::debug!("✅ TX {} already in finalized pool", hex::encode(txid));
                    break;
                }

                if !consensus_engine_clone.is_transaction_still_valid(&txid) {
                    tracing::info!(
                        "🧹 TX {} no longer valid/present in mempool — stopping voting loop",
                        hex::encode(txid)
                    );
                    break;
                }

                if start.elapsed() >= vote_deadline {
                    // Timeout: check accumulated weight from server.rs handler
                    let weight = consensus
                        .accumulated_weight
                        .get(&txid)
                        .map(|w| *w.value())
                        .unwrap_or(0);

                    let preference = consensus
                        .tx_state
                        .get(&txid)
                        .map(|s| s.read().preference)
                        .unwrap_or(Preference::Accept);

                    // Require minimum 25% of threshold weight before auto-finalizing.
                    // If below floor, extend deadline to allow more votes to arrive.
                    let total_avs_weight: u64 = consensus_engine_clone
                        .get_active_masternodes()
                        .iter()
                        .map(|mn| mn.tier.sampling_weight())
                        .sum();
                    let elapsed_secs = start.elapsed().as_secs();
                    let q_percent = if elapsed_secs >= 30 { 51u64 } else { 67u64 };
                    let (threshold, min_weight_floor) =
                        vote_finality_threshold(total_avs_weight, elapsed_secs);

                    if q_percent == 51 {
                        tracing::warn!(
                            "⚠️ TX {} stalled >30s — liveness fallback to 51% threshold",
                            hex::encode(txid)
                        );
                    }

                    if weight < min_weight_floor && vote_deadline < max_deadline {
                        vote_deadline += Duration::from_secs(5);
                        tracing::info!(
                            "⏳ TX {} weight {} < floor {} — extending deadline to {}s",
                            hex::encode(txid),
                            weight,
                            min_weight_floor,
                            vote_deadline.as_secs()
                        );
                        continue;
                    }

                    if preference != Preference::Accept {
                        tracing::warn!(
                            "❌ TX {} timed out after {}s with Reject preference — dropping",
                            hex::encode(txid),
                            vote_deadline.as_secs()
                        );
                        consensus_engine_clone
                            .reject_failed_voting_transaction(
                                txid,
                                "TimeVote rejected by validators".to_string(),
                            )
                            .await;
                        break;
                    }

                    if weight < threshold {
                        tracing::warn!(
                            "❌ TX {} vote timeout after {}s: weight {} < threshold {} ({}%) — rejecting",
                            hex::encode(txid),
                            vote_deadline.as_secs(),
                            weight,
                            threshold,
                            q_percent
                        );
                        consensus_engine_clone
                            .reject_failed_voting_transaction(
                                txid,
                                format!(
                                    "TimeVote quorum not reached: {} < {} ({}% of AVS)",
                                    weight, threshold, q_percent
                                ),
                            )
                            .await;
                        break;
                    }

                    tracing::warn!(
                        "⚠️ TX {} timed out after {}s but met quorum (weight: {} >= {}). Auto-finalizing",
                        hex::encode(txid),
                        vote_deadline.as_secs(),
                        weight,
                        threshold
                    );

                    let tx_for_broadcast = tx_pool.get_pending(&txid);
                    tx_pool.finalize_transaction(txid);

                    if tx_pool.is_finalized(&txid) {
                        tracing::info!(
                            "✅ TX {} auto-finalized after vote timeout (weight: {})",
                            hex::encode(txid),
                            weight
                        );

                        // Transition input UTXOs from Locked → SpentFinalized
                        // and create output UTXOs as Unspent
                        if let Some(ref tx_data) = tx_for_broadcast {
                            for input in &tx_data.inputs {
                                consensus_engine_clone
                                    .utxo_manager
                                    .mark_timevote_finalized(&input.previous_output, txid)
                                    .await;
                            }
                            for (idx, output) in tx_data.outputs.iter().enumerate() {
                                let outpoint = OutPoint {
                                    txid,
                                    vout: idx as u32,
                                };
                                let utxo = UTXO {
                                    outpoint: outpoint.clone(),
                                    value: output.value,
                                    script_pubkey: output.script_pubkey.clone(),
                                    address: String::from_utf8(output.script_pubkey.clone())
                                        .unwrap_or_default(),
                                    masternode_key: None,
                                };
                                if let Err(e) =
                                    consensus_engine_clone.utxo_manager.add_utxo(utxo).await
                                {
                                    tracing::warn!("Failed to add output UTXO vout={}: {}", idx, e);
                                }
                                consensus_engine_clone
                                    .utxo_manager
                                    .update_state(&outpoint, UTXOState::Unspent);
                            }
                        }

                        match consensus.assemble_timeproof(txid) {
                            Ok(proof) => {
                                tracing::info!(
                                    "📜 TimeProof assembled for TX {} with {} votes",
                                    hex::encode(txid),
                                    proof.votes.len()
                                );
                                let _ = consensus_engine_clone
                                    .finality_proof_mgr
                                    .store_timeproof(proof.clone());
                                consensus_engine_clone.broadcast_timeproof(proof).await;
                            }
                            Err(_) => {
                                tracing::debug!(
                                    "No votes available for TimeProof assembly on TX {}",
                                    hex::encode(txid)
                                );
                            }
                        }

                        if let Some(tx_data) = tx_for_broadcast {
                            consensus_engine_clone
                                .broadcast(NetworkMessage::TransactionFinalized {
                                    txid,
                                    tx: tx_data,
                                })
                                .await;
                        }
                    }
                    consensus
                        .finalized_txs
                        .insert(txid, (Preference::Accept, Instant::now()));

                    tx_status_map.insert(
                        txid,
                        TransactionStatus::Finalized {
                            finalized_at: chrono::Utc::now().timestamp_millis(),
                            vfp_weight: weight,
                        },
                    );

                    let _ = finalized_signal.send(txid);
                    break;
                }

                tokio::time::sleep(poll_interval).await;
            }

            // Cleanup
            consensus.tx_state.remove(&txid);
            tracing::debug!("🧹 Cleaned up consensus state for TX {}", hex::encode(txid));
        });

        Ok(())
    }

    pub fn get_finalized_transactions_for_block(&self) -> Vec<Transaction> {
        self.tx_pool.get_finalized_transactions()
    }

    pub fn get_finalized_transactions_with_fees_for_block(&self) -> Vec<(Transaction, u64)> {
        self.tx_pool.get_finalized_transactions_with_fees()
    }

    /// Get finalized transactions older than `min_age` for re-broadcast.
    pub fn get_stale_finalized(&self, min_age: std::time::Duration) -> Vec<(Hash256, Transaction)> {
        self.tx_pool.get_stale_finalized(min_age)
    }

    /// Immediately re-broadcast a specific finalized transaction to all connected peers.
    /// Returns true if the txid was found in the finalized pool and the broadcast was sent.
    pub async fn rebroadcast_transaction(&self, txid: Hash256) -> bool {
        let tx = match self.tx_pool.get_transaction(&txid) {
            Some(tx) => tx,
            None => return false,
        };
        if !self.tx_pool.is_finalized(&txid) {
            return false;
        }
        let cb = self.broadcast_callback.read().await;
        if let Some(ref broadcast) = *cb {
            broadcast(crate::network::message::NetworkMessage::TransactionFinalized { txid, tx });
            true
        } else {
            false
        }
    }

    #[allow(dead_code)]
    pub fn clear_finalized_transactions(&self) {
        self.tx_pool.clear_finalized();
    }

    /// Clear only specific finalized transactions that were included in a block
    pub fn clear_finalized_txs(&self, txids: &[Hash256]) {
        self.tx_pool.clear_finalized_txs(txids);
    }

    #[allow(dead_code)]
    pub fn get_mempool_info(&self) -> (usize, usize) {
        let pending = self.tx_pool.pending_count();
        let finalized = self.tx_pool.finalized_count();
        (pending, finalized)
    }

    /// Collect all mempool entries (pending + finalized) for peer sync.
    pub fn get_all_for_sync(&self) -> Vec<crate::network::message::MempoolSyncEntry> {
        self.tx_pool.get_all_for_sync()
    }

    /// Add a pre-finalized transaction directly to the finalized pool.
    /// Used when restoring from a peer's `MempoolSyncResponse` or from sled persistence.
    pub fn add_finalized_direct(&self, tx: Transaction, fee: u64) {
        self.tx_pool.add_finalized_direct(tx, fee);
    }

    /// Persist the mempool to sled so it survives restarts.
    pub fn save_mempool_to_sled(&self, db: &sled::Db) {
        self.tx_pool.save_to_sled(db);
    }

    /// Enable write-through mempool persistence. After this call, every
    /// transaction add/remove is mirrored to sled in real time.
    pub fn enable_mempool_persistence(&self, db: &sled::Db) {
        self.tx_pool.enable_persistence(db);
    }

    /// Restore the mempool from sled written by `save_mempool_to_sled`.
    /// Returns the number of entries restored.
    pub fn load_mempool_from_sled(&self, db: &sled::Db) -> usize {
        self.tx_pool.load_from_sled(db)
    }

    /// Walk the finalized pool and evict any TX whose inputs are not all
    /// present on-chain.  Such TXs were finalized before input-existence
    /// validation was hardened and can never be included in a block, so they
    /// permanently block block production for the holder.
    ///
    /// For each evicted TX:
    ///   - inputs that DO exist and are in a spent/locked state are restored
    ///     to `Unspent` (collateral-locked entries are skipped)
    ///   - phantom output UTXOs that were synthesized at finalize time are
    ///     removed from the local UTXO set
    ///   - the TX is dropped from the finalized pool and sled mempool tree
    ///
    /// Returns the number of TXs evicted.
    pub async fn evict_finalized_with_missing_inputs(&self) -> usize {
        let finalized = self.tx_pool.get_finalized_transactions();
        if finalized.is_empty() {
            return 0;
        }

        let mut evicted = 0usize;
        for tx in finalized {
            let txid = tx.txid();

            let mut any_missing = false;
            let mut existing_inputs = Vec::new();
            for input in &tx.inputs {
                match self.utxo_manager.get_utxo(&input.previous_output).await {
                    Ok(_) => existing_inputs.push(input.previous_output.clone()),
                    Err(_) => {
                        // A tombstone means this UTXO was legitimately spent (sled entry
                        // removed during finalization). Only flag as missing when there is
                        // no tombstone — that is the true phantom-input case.
                        if !self.utxo_manager.is_tombstoned(&input.previous_output) {
                            any_missing = true;
                        }
                    }
                }
            }
            if !any_missing {
                continue;
            }

            for outpoint in &existing_inputs {
                if self.utxo_manager.is_collateral_locked(outpoint) {
                    continue;
                }
                if matches!(
                    self.utxo_manager.get_state(outpoint),
                    Some(
                        crate::types::UTXOState::SpentFinalized { .. }
                            | crate::types::UTXOState::SpentPending { .. }
                            | crate::types::UTXOState::Locked { .. }
                    )
                ) {
                    self.utxo_manager
                        .update_state(outpoint, crate::types::UTXOState::Unspent);
                }
            }

            for (idx, _) in tx.outputs.iter().enumerate() {
                let outpoint = OutPoint {
                    txid,
                    vout: idx as u32,
                };
                if self.utxo_manager.get_state(&outpoint).is_some() {
                    let _ = self.utxo_manager.remove_utxo(&outpoint).await;
                }
            }

            self.tx_pool.drop_banned(&txid);
            evicted += 1;
            tracing::warn!(
                "🧹 Evicted finalized TX {} from pool — at least one input UTXO is missing on-chain",
                hex::encode(txid)
            );
        }
        evicted
    }

    /// Tombstone input UTXOs for confirmed-pool TXs whose inputs are still in sled.
    ///
    /// This fixes the crash window between `finalize_transaction` and
    /// `mark_timevote_finalized`: if the daemon crashed in that gap, the TX
    /// ends up in the confirmed pool (sled-persisted) but its inputs were never
    /// removed from sled or tombstoned.  After restart, `initialize_states`
    /// loads those inputs as `Unspent`, and `produce_block_at_height` evicts
    /// the TX every block because inputs are in the wrong state.
    ///
    /// Must be called AFTER `evict_finalized_with_missing_inputs` so that the
    /// pool only contains TXs with all inputs accounted for.
    ///
    /// Returns the number of input UTXOs tombstoned.
    pub async fn tombstone_confirmed_inputs_on_startup(&self) -> usize {
        let confirmed = self.tx_pool.get_finalized_transactions_with_fees();
        if confirmed.is_empty() {
            return 0;
        }
        let mut tombstoned = 0usize;
        for (tx, _) in confirmed {
            let txid = tx.txid();
            for input in &tx.inputs {
                if self.utxo_manager.is_tombstoned(&input.previous_output) {
                    continue; // already properly tombstoned
                }
                // Input is still in sled — tombstone it now so block assembly
                // sees it as legitimately spent rather than erroneously evicting
                // this finalized TX.
                if self
                    .utxo_manager
                    .get_utxo(&input.previous_output)
                    .await
                    .is_ok()
                {
                    self.utxo_manager
                        .mark_timevote_finalized(&input.previous_output, txid)
                        .await;
                    tombstoned += 1;
                }
            }
        }
        tombstoned
    }

    /// Apply the hardcoded phantom-finalized banlist (`crate::purge_list`).
    ///
    /// For each banned txid:
    ///   1. Restore real input UTXOs from `SpentFinalized`/`SpentPending`/`Locked`
    ///      back to `Unspent` (skip collateral-locked entries).
    ///   2. Remove phantom output UTXOs from the local UTXO set.
    ///   3. Drop the TX from the in-memory pending and finalized pools.
    ///
    /// Idempotent: missing UTXOs and missing pool entries are skipped silently.
    /// Returns the number of banlist records that touched local state.
    pub async fn purge_banned_transactions(&self) -> usize {
        let mut touched = 0usize;
        for (txid, real_inputs, phantom_outputs, reason) in crate::purge_list::iter_records() {
            let mut did_work = false;

            for outpoint in &real_inputs {
                if self.utxo_manager.is_collateral_locked(outpoint) {
                    tracing::warn!(
                        "🛡️ Skipping collateral-locked input {} during phantom-TX purge",
                        outpoint
                    );
                    continue;
                }
                if matches!(
                    self.utxo_manager.get_state(outpoint),
                    Some(
                        crate::types::UTXOState::SpentFinalized { .. }
                            | crate::types::UTXOState::SpentPending { .. }
                            | crate::types::UTXOState::Locked { .. }
                    )
                ) {
                    self.utxo_manager
                        .update_state(outpoint, crate::types::UTXOState::Unspent);
                    did_work = true;
                }
            }

            for outpoint in &phantom_outputs {
                if self.utxo_manager.get_state(outpoint).is_some() {
                    if let Err(e) = self.utxo_manager.remove_utxo(outpoint).await {
                        tracing::warn!(
                            "⚠️ Failed to remove phantom output {} during purge: {}",
                            outpoint,
                            e
                        );
                    } else {
                        did_work = true;
                    }
                }
            }

            if self.tx_pool.drop_banned(&txid) {
                did_work = true;
            }

            if did_work {
                touched += 1;
                tracing::warn!("🛡️ Purged phantom TX {}: {}", hex::encode(txid), reason);
            }
        }
        touched
    }

    /// Reprocess pending transactions that never completed finality.
    ///
    /// Common causes of stuck pending entries:
    /// 1. Restored from sled on startup without re-running `process_transaction`
    ///    (locks are in-memory only; after restart UTXOs are Unspent again)
    /// 2. Inserted via TimeVoteRequest with `add_pending` only (no auto-finalize)
    /// 3. Zero/invalid fee or spent inputs that can never finalize
    ///
    /// For each pending TX this method will:
    /// - Reject if validation fails or inputs are already spent by another TX
    /// - Auto-finalize if uncontested (same path as conflict-free submit)
    /// - Leave contested TXs alone so TimeVote / rebroadcast can resolve them
    ///
    /// Returns `(finalized_count, rejected_count)`.
    pub async fn retry_stuck_pending_transactions(&self) -> (usize, usize) {
        let mut pending = self.tx_pool.get_all_pending_with_metadata();
        if pending.is_empty() {
            return (0, 0);
        }

        // Higher fee first, then older first — prefer better / earlier TXs when
        // multiple pending entries compete for the same inputs.
        pending.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.3.cmp(&b.3)));

        let mut finalized = 0usize;
        let mut rejected = 0usize;

        for (tx, stored_fee, _, _) in pending {
            let txid = tx.txid();

            // May have been finalized/rejected by an earlier iteration
            if !self.tx_pool.is_pending(&txid) {
                continue;
            }

            // Hard reject: inputs already spent/finalized by a different TX
            if self.inputs_already_spent_by_other(&tx.inputs, &txid) {
                tracing::warn!(
                    "🧹 Stuck pending TX {} — inputs already spent by another TX; rejecting",
                    hex::encode(txid)
                );
                self.reject_failed_voting_transaction(
                    txid,
                    "Inputs already spent by another transaction".to_string(),
                )
                .await;
                rejected += 1;
                continue;
            }

            // Re-lock Unspent inputs so finalization can mark them SpentFinalized.
            // After a restart locks are lost (in-memory only).
            for input in &tx.inputs {
                match self.utxo_manager.get_state(&input.previous_output) {
                    Some(UTXOState::Unspent) | None => {
                        if let Err(e) = self.utxo_manager.lock_utxo(&input.previous_output, txid) {
                            tracing::debug!(
                                "Could not re-lock {} for stuck TX {}: {}",
                                input.previous_output,
                                hex::encode(txid),
                                e
                            );
                        }
                    }
                    Some(UTXOState::Locked {
                        txid: locked_txid, ..
                    }) if locked_txid == txid => {}
                    Some(UTXOState::SpentPending {
                        txid: pending_txid, ..
                    }) if pending_txid == txid => {}
                    _ => {}
                }
            }

            // Re-validate (fee, signatures, UTXO availability)
            let validated_fee = match self.validate_transaction_with_locks(&tx, txid).await {
                Ok(fee) => fee,
                Err(e) => {
                    tracing::warn!(
                        "🧹 Stuck pending TX {} failed re-validation: {} — rejecting",
                        hex::encode(txid),
                        e
                    );
                    self.reject_failed_voting_transaction(txid, e).await;
                    rejected += 1;
                    continue;
                }
            };

            // Repair fee recorded as 0 (TimeVoteRequest path / missing UTXOs at insert)
            if stored_fee == 0 && validated_fee > 0 {
                self.tx_pool.update_pending_fee(&txid, validated_fee);
            }

            // External conflict: another TX already owns the UTXO lock/spend state,
            // or a confirmed pool entry already spends these inputs — cannot finalize.
            let utxo_owned_by_other = tx.inputs.iter().any(|input| {
                matches!(
                    self.utxo_manager.get_state(&input.previous_output),
                    Some(UTXOState::Locked { txid: other, .. })
                        | Some(UTXOState::SpentPending { txid: other, .. })
                        | Some(UTXOState::SpentFinalized { txid: other, .. })
                        | Some(UTXOState::Archived { txid: other, .. })
                        if other != txid
                )
            });
            if utxo_owned_by_other || self.tx_pool.has_conflicting_confirmed(&tx.inputs, &txid) {
                tracing::debug!(
                    "⏳ Stuck pending TX {} has external double-spend conflict — skipping",
                    hex::encode(txid)
                );
                continue;
            }

            // Pending-vs-pending conflict: we process highest fee first, so this TX
            // wins. Reject lower-fee / later competitors so they cannot block forever.
            let competitors = self.tx_pool.get_conflicting_pending(&tx.inputs, &txid);
            for (comp_txid, _) in competitors {
                tracing::warn!(
                    "🧹 Rejecting pending TX {} — superseded by higher-priority stuck TX {}",
                    hex::encode(comp_txid),
                    hex::encode(txid)
                );
                self.reject_failed_voting_transaction(
                    comp_txid,
                    format!(
                        "Superseded by higher-priority pending transaction {}",
                        hex::encode(txid)
                    ),
                )
                .await;
                rejected += 1;
            }

            // Uncontested (or won pending conflict) — auto-finalize
            let tx_for_broadcast = tx.clone();
            if !self.tx_pool.finalize_transaction(txid) {
                tracing::warn!(
                    "⚠️ Stuck pending TX {} disappeared before finalize",
                    hex::encode(txid)
                );
                continue;
            }

            for input in &tx.inputs {
                self.utxo_manager
                    .mark_timevote_finalized(&input.previous_output, txid)
                    .await;
            }

            for (idx, output) in tx.outputs.iter().enumerate() {
                let outpoint = OutPoint {
                    txid,
                    vout: idx as u32,
                };
                let utxo = UTXO {
                    outpoint: outpoint.clone(),
                    value: output.value,
                    script_pubkey: output.script_pubkey.clone(),
                    address: String::from_utf8(output.script_pubkey.clone()).unwrap_or_default(),
                    masternode_key: None,
                };
                if let Err(e) = self.utxo_manager.add_utxo(utxo).await {
                    tracing::warn!(
                        "Failed to add output UTXO vout={} for recovered TX {}: {}",
                        idx,
                        hex::encode(txid),
                        e
                    );
                }
                self.utxo_manager
                    .update_state(&outpoint, UTXOState::Unspent);
            }

            self.broadcast(NetworkMessage::TransactionFinalized {
                txid,
                tx: tx_for_broadcast,
            })
            .await;

            self.timevote
                .finalized_txs
                .insert(txid, (Preference::Accept, Instant::now()));
            self.timevote.tx_status.insert(
                txid,
                TransactionStatus::Finalized {
                    finalized_at: chrono::Utc::now().timestamp_millis(),
                    vfp_weight: 0,
                },
            );
            self.signal_tx_finalized(txid);

            tracing::info!(
                "✅ Recovered stuck pending TX {} — auto-finalized (fee={})",
                hex::encode(txid),
                validated_fee
            );
            finalized += 1;
        }

        if finalized > 0 || rejected > 0 {
            tracing::info!(
                "🧹 Pending TX recovery: finalized={}, rejected={}, remaining={}",
                finalized,
                rejected,
                self.tx_pool.pending_count()
            );
        }

        (finalized, rejected)
    }

    /// Evict pending transactions that have been stuck longer than `max_age`.
    ///
    /// This is a policy/mempool cleanup path only: it releases local UTXO reservations
    /// and clears in-memory voting state so the node stops carrying transactions that
    /// never made it into a block. It does not alter any on-chain state.
    pub async fn evict_stale_pending_transactions(&self, max_age: Duration) -> usize {
        let evicted = self.tx_pool.cleanup_stale_pending(max_age);
        if evicted.is_empty() {
            return 0;
        }

        let evicted_count = evicted.len();
        let mut restored_inputs = 0usize;

        for tx in evicted {
            let txid = tx.txid();

            for input in &tx.inputs {
                if self
                    .utxo_manager
                    .is_collateral_locked(&input.previous_output)
                {
                    tracing::warn!(
                        "⚠️ Skipping collateral UTXO {} while evicting stale pending TX {}",
                        input.previous_output,
                        hex::encode(txid)
                    );
                    continue;
                }

                let should_restore = matches!(
                    self.utxo_manager.get_state(&input.previous_output),
                    Some(UTXOState::Locked { txid: locked_txid, .. }) if locked_txid == txid
                ) || matches!(
                    self.utxo_manager.get_state(&input.previous_output),
                    Some(UTXOState::SpentPending { txid: pending_txid, .. }) if pending_txid == txid
                );

                if should_restore {
                    self.utxo_manager
                        .update_state(&input.previous_output, UTXOState::Unspent);
                    restored_inputs += 1;
                }
            }

            self.transition_to_rejected(
                txid,
                format!(
                    "Pending transaction evicted after exceeding stale age ({}s)",
                    max_age.as_secs()
                ),
            );
            self.timevote.tx_state.remove(&txid);
            self.timevote.timeproof_votes.remove(&txid);
            self.timevote.accumulated_weight.remove(&txid);
            self.timevote.finalized_txs.remove(&txid);
            self.timevote.fallback_votes.remove(&txid);
            self.timevote
                .proposal_to_tx
                .retain(|_, tracked_txid| *tracked_txid != txid);
        }

        tracing::warn!(
            "🧹 Evicted {} stale pending transaction(s) older than {}s and restored {} input UTXO(s)",
            evicted_count,
            max_age.as_secs(),
            restored_inputs
        );

        evicted_count
    }

    #[allow(dead_code)]
    pub fn get_active_masternodes(&self) -> Vec<Masternode> {
        self.get_masternodes()
    }

    /// Submit a transaction to the consensus engine (called from RPC)
    pub async fn add_transaction(&self, tx: Transaction) -> Result<Hash256, String> {
        self.submit_transaction(tx).await
    }

    /// Submit a batch of transactions concurrently.  Non-conflicting transactions
    /// (different UTXO inputs) are finalized in parallel rather than serially,
    /// collapsing N × ~750 ms into a single ~750 ms round for independent payments.
    ///
    /// Results are returned in the same order as the input slice.  Conflicting
    /// transactions (double-spends) still fail — the UTXO lock rejects the
    /// second attempt with the same error as a single-TX submission.
    pub async fn batch_submit_transactions(
        engine: Arc<Self>,
        txs: Vec<Transaction>,
    ) -> Vec<Result<Hash256, String>> {
        if txs.is_empty() {
            return vec![];
        }

        let n = txs.len();
        tracing::info!("🚀 batch_submit: {} transactions", n);

        let indexed_handles: Vec<(usize, tokio::task::JoinHandle<Result<Hash256, String>>)> = txs
            .into_iter()
            .enumerate()
            .map(|(idx, tx)| {
                let engine = Arc::clone(&engine);
                (
                    idx,
                    tokio::spawn(async move { engine.submit_transaction(tx).await }),
                )
            })
            .collect();

        let mut results: Vec<Result<Hash256, String>> =
            (0..n).map(|_| Err("not submitted".to_string())).collect();

        for (idx, handle) in indexed_handles {
            results[idx] = handle
                .await
                .unwrap_or_else(|e| Err(format!("task panicked: {}", e)));
        }
        results
    }

    /// Cleanup old finalized transactions from TimeVote consensus
    /// Prevents unbounded memory growth by removing old finalized state
    pub fn cleanup_old_finalized(&self, retention_secs: u64) -> usize {
        self.timevote.cleanup_old_finalized(retention_secs)
    }

    // ========================================================================
    // §7.6 LIVENESS FALLBACK PROTOCOL - State Management
    // ========================================================================

    /// Start monitoring a transaction for stall detection (§7.6.1)
    /// Call this when a transaction enters Voting state
    pub fn start_stall_timer(&self, txid: Hash256) {
        self.timevote.stall_timers.insert(txid, Instant::now());
        tracing::debug!("Started stall timer for transaction {}", hex::encode(txid));
    }

    /// Check if a transaction has exceeded the stall timeout (§7.6.1)
    /// Returns true if transaction has been in Voting for > STALL_TIMEOUT
    pub fn check_stall_timeout(&self, txid: &Hash256) -> bool {
        self.timevote
            .stall_timers
            .get(txid)
            .is_some_and(|entry| entry.value().elapsed() > STALL_TIMEOUT)
    }

    /// Stop monitoring a transaction (remove stall timer)
    /// Call when transaction reaches terminal state
    pub fn stop_stall_timer(&self, txid: &Hash256) {
        self.timevote.stall_timers.remove(txid);
    }

    /// Set transaction status (§7.3 state machine)
    pub fn set_tx_status(&self, txid: Hash256, status: TransactionStatus) {
        self.timevote.tx_status.insert(txid, status);
    }

    /// Get transaction status
    pub fn get_tx_status(&self, txid: &Hash256) -> Option<TransactionStatus> {
        self.timevote.tx_status.get(txid).map(|r| r.clone())
    }

    /// Transition transaction to Voting state (§7.3)
    pub fn transition_to_voting(&self, txid: Hash256) {
        let status = TransactionStatus::Voting {
            confidence: 0,
            counter: 0,
            started_at: chrono::Utc::now().timestamp_millis(),
        };
        self.set_tx_status(txid, status);
        self.start_stall_timer(txid);

        // FIX: Transition UTXOs from Locked to SpentPending when voting starts
        // This is the correct place per protocol: Unspent → Locked → SpentPending
        if let Some(tx) = self.tx_pool.get_pending(&txid) {
            let now = chrono::Utc::now().timestamp();
            let n = self.get_masternodes().len() as u32;

            for input in &tx.inputs {
                let new_state = UTXOState::SpentPending {
                    txid,
                    votes: 0,
                    total_nodes: n,
                    spent_at: now,
                };
                self.utxo_manager
                    .update_state(&input.previous_output, new_state.clone());

                tracing::debug!(
                    "UTXO {} → SpentPending (txid: {})",
                    input.previous_output,
                    hex::encode(txid)
                );
            }
        }

        tracing::debug!("Transaction {} → Voting", hex::encode(txid));
    }

    /// Transition transaction to Finalized state (§8)
    pub fn transition_to_finalized(&self, txid: Hash256, vfp_weight: u64) {
        let finalized_at_ms = chrono::Utc::now().timestamp_millis();

        // Measure TX finality: voting start → finalized.
        // Only record for the direct Voting → Finalized path; fallback-resolved
        // TXs are rare and would skew the average high, so they are excluded.
        if let Some(entry) = self.timevote.tx_status.get(&txid) {
            if let TransactionStatus::Voting { started_at, .. } = entry.value() {
                let finality_ms = (finalized_at_ms - started_at).max(0) as f64;
                tracing::debug!(
                    "⚡ TX {} finalized in {:.0}ms",
                    hex::encode(txid),
                    finality_ms
                );
                let mut avg = self.avg_finality_ms.write();
                avg.push(finality_ms);
                if avg.len() > 50 {
                    avg.remove(0);
                }
            }
        }

        let status = TransactionStatus::Finalized {
            finalized_at: finalized_at_ms,
            vfp_weight,
        };
        self.set_tx_status(txid, status);
        self.stop_stall_timer(&txid);

        // §7.6 Week 5-6 Part 4: Clean up fallback tracking
        self.timevote.fallback_rounds.remove(&txid);
        self.timevote.liveness_alerts.remove(&txid);

        tracing::info!(
            "Transaction {} → Finalized (weight: {})",
            hex::encode(txid),
            vfp_weight
        );
    }

    /// Transition transaction to FallbackResolution state (§7.6.4)
    pub fn transition_to_fallback_resolution(&self, txid: Hash256, alerts_count: u32) {
        let status = TransactionStatus::FallbackResolution {
            started_at: chrono::Utc::now().timestamp_millis(),
            round: 0,
            alerts_count,
        };
        self.set_tx_status(txid, status);
        self.stop_stall_timer(&txid);

        // §7.6 Week 5-6 Part 4: Initialize fallback round tracking
        // Start with slot_index 0, round_count 0
        let current_slot = (chrono::Utc::now().timestamp() as u64) / 600; // 10-minute slots
        self.timevote
            .fallback_rounds
            .insert(txid, (current_slot, 0, Instant::now()));

        tracing::warn!(
            "Transaction {} → FallbackResolution (alerts: {}, slot: {})",
            hex::encode(txid),
            alerts_count,
            current_slot
        );
    }

    /// Transition transaction to Rejected state
    pub fn transition_to_rejected(&self, txid: Hash256, reason: String) {
        let status = TransactionStatus::Rejected {
            rejected_at: chrono::Utc::now().timestamp_millis(),
            reason: reason.clone(),
        };
        self.set_tx_status(txid, status);
        self.stop_stall_timer(&txid);

        // §7.6 Week 5-6 Part 4: Clean up fallback tracking
        self.timevote.fallback_rounds.remove(&txid);
        self.timevote.liveness_alerts.remove(&txid);

        tracing::info!("Transaction {} → Rejected: {}", hex::encode(txid), reason);
    }

    /// Get all transactions in a specific status
    pub fn get_transactions_by_status(&self, target_status: &TransactionStatus) -> Vec<Hash256> {
        self.timevote
            .tx_status
            .iter()
            .filter_map(|entry| {
                let (txid, status) = entry.pair();
                if std::mem::discriminant(status) == std::mem::discriminant(target_status) {
                    Some(*txid)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get all stalled transactions (in Voting for > STALL_TIMEOUT)
    pub fn get_stalled_transactions(&self) -> Vec<Hash256> {
        self.timevote
            .stall_timers
            .iter()
            .filter_map(|entry| {
                let (txid, start_time) = entry.pair();
                if start_time.elapsed() > STALL_TIMEOUT {
                    Some(*txid)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get memory usage statistics from consensus engine
    pub fn memory_stats(&self) -> ConsensusMemoryStats {
        self.timevote.memory_stats()
    }

    // ========================================================================
    // §7.6 LIVENESS FALLBACK PROTOCOL - ALERT & VOTE ACCUMULATION
    // ========================================================================

    /// Accumulate a LivenessAlert and check if f+1 threshold reached (§7.6.2-7.6.3)
    ///
    /// Returns true if fallback should be triggered (f+1 unique reporters)
    pub fn accumulate_liveness_alert(
        &self,
        alert: LivenessAlert,
        total_masternodes: usize,
    ) -> bool {
        let txid = alert.txid;

        // Add alert to tracker
        self.timevote
            .liveness_alerts
            .entry(txid)
            .or_default()
            .push(alert);

        // Count unique reporters (collect into Vec to avoid lifetime issues)
        let alerts_vec: Vec<String> = self
            .timevote
            .liveness_alerts
            .get(&txid)
            .map(|alerts| alerts.iter().map(|a| a.reporter_mn_id.clone()).collect())
            .unwrap_or_default();

        let unique_reporters: std::collections::HashSet<_> = alerts_vec.iter().collect();

        // Calculate f+1 threshold
        let f = (total_masternodes.saturating_sub(1)) / 3;
        let threshold = f + 1;

        let threshold_reached = unique_reporters.len() >= threshold;

        // Phase 5: Record fallback activation if threshold just reached
        if threshold_reached && unique_reporters.len() == threshold {
            self.record_fallback_activation();
        }

        threshold_reached
    }

    /// Get count of unique alert reporters for a transaction
    pub fn get_alert_count(&self, txid: &Hash256) -> usize {
        self.timevote
            .liveness_alerts
            .get(txid)
            .map(|alerts| {
                let unique: std::collections::HashSet<_> =
                    alerts.iter().map(|a| &a.reporter_mn_id).collect();
                unique.len()
            })
            .unwrap_or(0)
    }

    /// Accumulate a FallbackVote and check if Q_finality threshold reached (§7.6.4)
    ///
    /// Returns Some(decision) if quorum reached, None otherwise
    pub fn accumulate_fallback_vote(
        &self,
        vote: FallbackVote,
        total_avs_weight: u64,
    ) -> Option<FallbackVoteDecision> {
        let proposal_hash = vote.proposal_hash;

        // Add vote to tracker, then calculate weighted totals from the same
        // entry handle (avoids a redundant lookup and an unwrap on a value
        // that was just inserted).
        let mut votes = self
            .timevote
            .fallback_votes
            .entry(proposal_hash)
            .or_default();
        votes.push(vote);

        let mut approve_weight = 0u64;
        let mut reject_weight = 0u64;

        for v in votes.iter() {
            match v.vote {
                FallbackVoteDecision::Approve => approve_weight += v.voter_weight,
                FallbackVoteDecision::Reject => reject_weight += v.voter_weight,
            }
        }

        // Calculate Q_finality (simple majority (>50%) of total AVS weight)
        let q_finality = (total_avs_weight * 2) / 3;

        // Check if threshold reached
        if approve_weight >= q_finality {
            Some(FallbackVoteDecision::Approve)
        } else if reject_weight >= q_finality {
            Some(FallbackVoteDecision::Reject)
        } else {
            None
        }
    }

    /// Get current vote status for a proposal (for logging/debugging)
    pub fn get_vote_status(&self, proposal_hash: &Hash256) -> Option<(u64, u64, usize)> {
        self.timevote
            .fallback_votes
            .get(proposal_hash)
            .map(|votes| {
                let mut approve_weight = 0u64;
                let mut reject_weight = 0u64;

                for v in votes.iter() {
                    match v.vote {
                        FallbackVoteDecision::Approve => approve_weight += v.voter_weight,
                        FallbackVoteDecision::Reject => reject_weight += v.voter_weight,
                    }
                }

                (approve_weight, reject_weight, votes.len())
            })
    }

    /// Register a proposal for a transaction (tracking proposal_hash -> txid)
    pub fn register_proposal(&self, proposal_hash: Hash256, txid: Hash256) {
        self.timevote.proposal_to_tx.insert(proposal_hash, txid);
    }

    /// Get transaction ID for a proposal hash
    pub fn get_proposal_txid(&self, proposal_hash: &Hash256) -> Option<Hash256> {
        self.timevote.proposal_to_tx.get(proposal_hash).map(|v| *v)
    }

    /// Finalize transaction based on fallback vote result (§7.6.4)
    pub fn finalize_from_fallback(
        &self,
        txid: Hash256,
        decision: FallbackVoteDecision,
        total_weight: u64,
    ) {
        match decision {
            FallbackVoteDecision::Approve => {
                // Transition to Finalized state
                self.transition_to_finalized(txid, total_weight);
                tracing::info!(
                    "✅ Transaction {} finalized via fallback (Approved with weight {})",
                    hex::encode(txid),
                    total_weight
                );
            }
            FallbackVoteDecision::Reject => {
                // Transition to Rejected state
                self.transition_to_rejected(txid, "Fallback consensus rejected".to_string());
                tracing::warn!(
                    "❌ Transaction {} rejected via fallback (weight {})",
                    hex::encode(txid),
                    total_weight
                );
            }
        }
    }

    // ===== Phase 4: Validation & Safety Functions (§7.6 Security) =====

    /// Detect equivocation: Check if a masternode sent conflicting alerts/votes (§7.6 Security)
    pub fn detect_alert_equivocation(&self, txid: &Hash256, reporter: &str) -> bool {
        if let Some(alerts) = self.timevote.liveness_alerts.get(txid) {
            let reporter_alerts: Vec<_> = alerts
                .iter()
                .filter(|a| a.reporter_mn_id == reporter)
                .collect();

            if reporter_alerts.len() > 1 {
                tracing::warn!(
                    "⚠️ Equivocation detected: {} sent {} alerts for tx {}",
                    reporter,
                    reporter_alerts.len(),
                    hex::encode(txid)
                );
                return true;
            }
        }
        false
    }

    /// Detect vote equivocation: Check if a voter cast multiple different votes for same proposal
    pub fn detect_vote_equivocation(&self, proposal_hash: &Hash256, voter: &str) -> bool {
        if let Some(votes) = self.timevote.fallback_votes.get(proposal_hash) {
            let voter_votes: Vec<_> = votes.iter().filter(|v| v.voter_mn_id == voter).collect();

            if voter_votes.len() > 1 {
                // Check if votes conflict
                let first_decision = &voter_votes[0].vote;
                let has_conflict = voter_votes.iter().any(|v| &v.vote != first_decision);

                if has_conflict {
                    tracing::warn!(
                        "⚠️ Vote equivocation detected: {} cast conflicting votes for proposal {}",
                        voter,
                        hex::encode(proposal_hash)
                    );
                    return true;
                }
            }
        }
        false
    }

    /// Detect Byzantine behavior: Multiple proposals for same transaction
    pub fn detect_multiple_proposals(&self, txid: &Hash256) -> Vec<Hash256> {
        let mut proposals = Vec::new();
        for entry in self.timevote.proposal_to_tx.iter() {
            if entry.value() == txid {
                proposals.push(*entry.key());
            }
        }

        if proposals.len() > 1 {
            tracing::warn!(
                "⚠️ Byzantine behavior: {} proposals detected for tx {}",
                proposals.len(),
                hex::encode(txid)
            );
        }

        proposals
    }

    /// Validate threshold requirements before processing (§7.6 Security)
    pub fn validate_alert_threshold(
        &self,
        txid: &Hash256,
        total_masternodes: usize,
    ) -> Result<bool, String> {
        if total_masternodes == 0 {
            return Err("No masternodes in network".to_string());
        }

        let f = (total_masternodes.saturating_sub(1)) / 3;
        let threshold = f + 1;

        if threshold > total_masternodes {
            return Err(format!(
                "Invalid threshold: f+1={} exceeds total={}",
                threshold, total_masternodes
            ));
        }

        let alert_count = self.get_alert_count(txid);
        Ok(alert_count >= threshold)
    }

    /// Validate vote weight doesn't exceed total AVS weight (Byzantine detection)
    pub fn validate_vote_weight(
        &self,
        proposal_hash: &Hash256,
        total_avs_weight: u64,
    ) -> Result<(), String> {
        if let Some(votes) = self.timevote.fallback_votes.get(proposal_hash) {
            let mut total_voted_weight = 0u64;
            let mut unique_voters = std::collections::HashSet::new();

            for vote in votes.iter() {
                // Check for duplicate voters
                if !unique_voters.insert(&vote.voter_mn_id) {
                    tracing::warn!(
                        "⚠️ Duplicate vote detected from {} for proposal {}",
                        vote.voter_mn_id,
                        hex::encode(proposal_hash)
                    );
                }

                total_voted_weight = total_voted_weight.saturating_add(vote.voter_weight);
            }

            // Allow slight overflow due to rounding, but flag excessive weight
            if total_voted_weight > total_avs_weight * 11 / 10 {
                // >110% is suspicious
                return Err(format!(
                    "Vote weight {} exceeds total AVS weight {} by >10%",
                    total_voted_weight, total_avs_weight
                ));
            }
        }

        Ok(())
    }

    /// Check if a masternode has been flagged for Byzantine behavior
    pub fn is_byzantine_flagged(&self, mn_id: &str) -> bool {
        // For now, simple in-memory tracking
        // TODO: Persistent storage and slashing integration
        self.timevote
            .byzantine_nodes
            .get(mn_id)
            .map(|entry| *entry.value())
            .unwrap_or(false)
    }

    /// Flag a masternode for Byzantine behavior
    pub fn flag_byzantine(&self, mn_id: &str, reason: &str) {
        tracing::error!("🚨 Flagging {} as Byzantine: {}", mn_id, reason);
        self.timevote
            .byzantine_nodes
            .insert(mn_id.to_string(), true);
        // TODO: Emit event for slashing mechanism
    }

    /// Get count of Byzantine-flagged nodes
    pub fn get_byzantine_count(&self) -> usize {
        self.timevote
            .byzantine_nodes
            .iter()
            .filter(|entry| *entry.value())
            .count()
    }

    // ===== Phase 5: Monitoring & Metrics Functions =====

    /// Increment fallback activation counter (when f+1 alerts trigger fallback)
    pub fn record_fallback_activation(&self) {
        self.timevote
            .fallback_activations
            .fetch_add(1, Ordering::Relaxed);
        tracing::info!(
            "📊 Fallback activation count: {}",
            self.get_fallback_activations()
        );
    }

    /// Increment stall detection counter
    pub fn record_stall_detection(&self) {
        self.timevote
            .stall_detections
            .fetch_add(1, Ordering::Relaxed);
    }

    /// Increment TimeLock resolution counter
    pub fn record_timelock_resolution(&self) {
        self.timevote
            .timelock_resolutions
            .fetch_add(1, Ordering::Relaxed);
        tracing::info!(
            "📊 TimeLock resolution count: {}",
            self.get_timelock_resolutions()
        );
    }

    /// Get fallback activation metrics
    pub fn get_fallback_activations(&self) -> usize {
        self.timevote.fallback_activations.load(Ordering::Relaxed)
    }

    /// Get stall detection metrics
    pub fn get_stall_detections(&self) -> usize {
        self.timevote.stall_detections.load(Ordering::Relaxed)
    }

    /// Get TimeLock resolution metrics
    pub fn get_timelock_resolutions(&self) -> usize {
        self.timevote.timelock_resolutions.load(Ordering::Relaxed)
    }

    /// Get comprehensive fallback metrics snapshot (§7.6 Monitoring)
    pub fn get_fallback_metrics(&self) -> FallbackMetrics {
        FallbackMetrics {
            total_fallback_activations: self.get_fallback_activations(),
            total_stall_detections: self.get_stall_detections(),
            total_timelock_resolutions: self.get_timelock_resolutions(),
            active_stalled_txs: self.timevote.liveness_alerts.len(),
            active_fallback_rounds: self.timevote.fallback_rounds.len(),
            byzantine_nodes_flagged: self.get_byzantine_count(),
            pending_proposals: self.timevote.proposal_to_tx.len(),
            total_fallback_votes: self
                .timevote
                .fallback_votes
                .iter()
                .map(|entry| entry.value().len())
                .sum(),
        }
    }

    /// Log comprehensive fallback status (for debugging and monitoring)
    pub fn log_fallback_status(&self) {
        let metrics = self.get_fallback_metrics();
        tracing::info!(
            "📊 Fallback Status: activations={}, stalls={}, timelock={}, active_stalls={}, rounds={}, byzantine={}, proposals={}, votes={}",
            metrics.total_fallback_activations,
            metrics.total_stall_detections,
            metrics.total_timelock_resolutions,
            metrics.active_stalled_txs,
            metrics.active_fallback_rounds,
            metrics.byzantine_nodes_flagged,
            metrics.pending_proposals,
            metrics.total_fallback_votes
        );
    }

    /// Decide how to vote on a fallback finality proposal (§7.6.4)
    ///
    /// Evaluates transaction state and determines whether to vote Approve or Reject.
    /// This implements the voting decision logic for the liveness fallback protocol.
    ///
    /// # Decision Logic
    /// - **Approve**: Transaction is in Voting or FallbackResolution state (pending)
    /// - **Reject**: Transaction is already Finalized, Rejected, or not found
    ///
    /// The reasoning is that if a transaction is pending fallback resolution,
    /// we should vote to approve its finalization. If it's already resolved or
    /// doesn't exist, we vote to reject the proposal.
    ///
    /// # Arguments
    /// * `txid` - Transaction identifier to evaluate
    ///
    /// # Returns
    /// Vote decision: either Approve or Reject
    ///
    /// # Example
    /// ```ignore
    /// let decision = consensus.decide_fallback_vote(&tx_hash);
    /// match decision {
    ///     FallbackVoteDecision::Approve => { /* cast approve vote */ }
    ///     FallbackVoteDecision::Reject => { /* cast reject vote */ }
    /// }
    /// ```
    pub fn decide_fallback_vote(&self, txid: &Hash256) -> FallbackVoteDecision {
        match self.get_tx_status(txid) {
            Some(TransactionStatus::Voting { .. })
            | Some(TransactionStatus::FallbackResolution { .. }) => {
                // Transaction is pending, vote to approve finalization
                FallbackVoteDecision::Approve
            }
            _ => {
                // Transaction is already resolved, not found, or in invalid state
                FallbackVoteDecision::Reject
            }
        }
    }

    /// Resolve all stalled transactions via TimeLock block (§7.6.5)
    ///
    /// Called when producing a TimeLock block. This is the ultimate fallback mechanism
    /// that deterministically resolves all transactions that have been in FallbackResolution
    /// state for too long or have exceeded MAX_FALLBACK_ROUNDS.
    ///
    /// # Protocol Flow (§7.6.5)
    /// 1. Scan all transactions in FallbackResolution state
    /// 2. For each transaction, make deterministic decision based on current state
    /// 3. Finalize with Accept or Reject
    /// 4. Clean up fallback tracking
    /// 5. Return true if any transactions were resolved
    ///
    /// # Decision Logic
    /// - If transaction preference is Accept and still valid → Accept
    /// - Otherwise → Reject
    ///
    /// # Returns
    /// * `bool` - true if any transactions were resolved (set liveness_recovery flag)
    ///
    /// # Example
    /// ```ignore
    /// // When producing TimeLock block
    /// let had_stalls = consensus.resolve_stalls_via_timelock();
    /// block.liveness_recovery = had_stalls;
    /// ```
    pub fn resolve_stalls_via_timelock(&self) -> bool {
        // Get all transactions in FallbackResolution state
        let stalled_txs: Vec<Hash256> = self
            .timevote
            .tx_status
            .iter()
            .filter_map(|entry| match entry.value() {
                TransactionStatus::FallbackResolution { .. } => Some(*entry.key()),
                _ => None,
            })
            .collect();

        if stalled_txs.is_empty() {
            return false;
        }

        // Phase 5: Record TimeLock resolution metric
        self.record_timelock_resolution();

        tracing::warn!(
            "🔄 TimeLock block resolving {} stalled transactions (§7.6.5)",
            stalled_txs.len()
        );

        for txid in &stalled_txs {
            // Get the transaction's current preference
            let decision = if let Some(voting_state) = self.timevote.tx_state.get(txid) {
                let state = voting_state.value().read();
                match state.preference {
                    Preference::Accept => {
                        // Check if still valid
                        if self.is_transaction_still_valid(txid) {
                            FallbackDecision::Accept
                        } else {
                            FallbackDecision::Reject
                        }
                    }
                    Preference::Reject => FallbackDecision::Reject,
                }
            } else {
                // No voting state, default to Reject
                FallbackDecision::Reject
            };

            tracing::info!(
                "🔒 TimeLock resolving tx {}: {:?}",
                hex::encode(&txid[..8]),
                decision
            );

            // Apply the decision
            match decision {
                FallbackDecision::Accept => {
                    self.transition_to_finalized(*txid, 0); // weight=0 for TimeLock resolution
                }
                FallbackDecision::Reject => {
                    self.transition_to_rejected(*txid, "TimeLock fallback rejected".to_string());
                }
            }

            // Clean up tracking
            self.timevote.fallback_rounds.remove(txid);
            self.timevote.liveness_alerts.remove(txid);
            self.timevote.fallback_votes.retain(|k, _| {
                // Remove votes for proposals related to this transaction
                self.timevote
                    .proposal_to_tx
                    .get(k)
                    .map(|v| *v != *txid)
                    .unwrap_or(true)
            });
        }

        true // Transactions were resolved
    }

    /// Check if there are any transactions requiring liveness recovery
    ///
    /// Used to determine if the liveness_recovery flag should be set on the next TimeLock block.
    ///
    /// # Returns
    /// * `bool` - true if there are transactions in FallbackResolution state
    pub fn has_pending_fallback_transactions(&self) -> bool {
        self.timevote
            .tx_status
            .iter()
            .any(|entry| matches!(entry.value(), TransactionStatus::FallbackResolution { .. }))
    }

    // ========================================================================
    // §7.6 LIVENESS FALLBACK PROTOCOL - DETERMINISTIC LEADER ELECTION
    // ========================================================================

    /// Elect deterministic fallback leader (§7.6.4 Step 1)
    ///
    /// Computes the deterministic leader for a specific transaction and round using
    /// a hash-based selection algorithm. All honest nodes compute the same leader
    /// independently without coordination.
    ///
    /// # Algorithm (§7.6.4)
    /// ```text
    /// For each masternode in AVS:
    ///   hash = H(txid || slot_index || round || mn_pubkey)
    ///   
    /// Leader = Masternode with minimum hash value
    /// ```
    ///
    /// # Properties
    /// - **Deterministic**: Same inputs always produce same leader
    /// - **Unpredictable**: Cannot predict leader in advance without all inputs
    /// - **Fair**: Each masternode has equal probability over many elections
    /// - **Byzantine-safe**: Cannot be manipulated by adversaries
    ///
    /// # Arguments
    /// * `txid` - Transaction identifier
    /// * `slot_index` - Current slot (10-minute epoch)
    /// * `round` - Fallback round number (0-4)
    /// * `avs` - Active Validator Set snapshot
    ///
    /// # Returns
    /// * `Option<String>` - Masternode ID of elected leader, or None if AVS empty
    ///
    /// # Example
    /// ```ignore
    /// let avs = consensus.get_avs_snapshot(slot_index)?;
    /// let leader = consensus.elect_fallback_leader(txid, slot_index, 0, &avs, &prev_block_hash)?;
    ///
    /// if leader == my_masternode_id {
    ///     // I am the leader, broadcast proposal
    ///     consensus.broadcast_finality_proposal(txid, slot_index, decision).await?;
    /// }
    /// ```
    pub fn elect_fallback_leader(
        &self,
        txid: Hash256,
        slot_index: u64,
        round: u32,
        avs: &AVSSnapshot,
        prev_block_hash: &Hash256,
    ) -> Option<String> {
        if avs.validators.is_empty() && avs.validators_ref.is_none() {
            tracing::warn!("Cannot elect fallback leader: AVS is empty");
            return None;
        }

        let mut min_hash = [0xff; 32];
        let mut elected_leader: Option<String> = None;

        // Get validators - use validators_ref if available, otherwise validators
        if let Some(ref validators_arc) = avs.validators_ref {
            // Use the shared reference
            for validator in validators_arc.iter() {
                // Compute deterministic hash: H(txid || slot_index || round || prev_block_hash || mn_pubkey)
                // Including prev_block_hash prevents prediction of leader before latest block is produced
                let mut hasher = Sha256::new();
                hasher.update(txid);
                hasher.update(slot_index.to_le_bytes());
                hasher.update(round.to_le_bytes());
                hasher.update(prev_block_hash);
                hasher.update(validator.address.as_bytes());

                let hash: [u8; 32] = hasher.finalize().into();

                // Track minimum hash
                if hash < min_hash {
                    min_hash = hash;
                    elected_leader = Some(validator.address.clone());
                }
            }
        } else {
            // Use the serialized validators
            for (validator_id, _weight) in &avs.validators {
                // Compute deterministic hash: H(txid || slot_index || round || prev_block_hash || mn_pubkey)
                let mut hasher = Sha256::new();
                hasher.update(txid);
                hasher.update(slot_index.to_le_bytes());
                hasher.update(round.to_le_bytes());
                hasher.update(prev_block_hash);
                hasher.update(validator_id.as_bytes());

                let hash: [u8; 32] = hasher.finalize().into();

                // Track minimum hash
                if hash < min_hash {
                    min_hash = hash;
                    elected_leader = Some(validator_id.clone());
                }
            }
        }

        if let Some(ref leader) = elected_leader {
            tracing::debug!(
                "🎯 Elected fallback leader for tx {} (slot {}, round {}): {}",
                hex::encode(&txid[..8]),
                slot_index,
                round,
                leader
            );
        }

        elected_leader
    }

    /// Check if this node is the fallback leader for a transaction
    ///
    /// Convenience method that combines leader election with identity check.
    ///
    /// # Arguments
    /// * `txid` - Transaction identifier
    /// * `slot_index` - Current slot
    /// * `round` - Fallback round number
    /// * `avs` - Active Validator Set snapshot
    ///
    /// # Returns
    /// * `bool` - true if this node is the elected leader
    pub fn is_fallback_leader(
        &self,
        txid: Hash256,
        slot_index: u64,
        round: u32,
        avs: &AVSSnapshot,
        prev_block_hash: &Hash256,
    ) -> bool {
        let identity = match self.identity.get() {
            Some(id) => id,
            None => return false,
        };

        let leader = match self.elect_fallback_leader(txid, slot_index, round, avs, prev_block_hash)
        {
            Some(l) => l,
            None => return false,
        };

        identity.address == leader
    }

    // ========================================================================
    // §7.6 LIVENESS FALLBACK PROTOCOL - TIMEOUT & RETRY
    // ========================================================================

    /// Check for timed-out fallback rounds and retry with new leader (§7.6.3)
    ///
    /// This method is called periodically to detect fallback rounds that have
    /// exceeded FALLBACK_ROUND_TIMEOUT without reaching Q_finality. When a timeout
    /// is detected, the slot_index is incremented to deterministically select a
    /// new leader, and the fallback process retries.
    ///
    /// # Protocol Flow
    /// 1. Scan all transactions in FallbackResolution state
    /// 2. Check if round_started_at + FALLBACK_ROUND_TIMEOUT < now
    /// 3. If timed out:
    ///    a. Increment slot_index (deterministic leader rotation)
    ///    b. Check if round_count < MAX_FALLBACK_ROUNDS
    ///    c. If under limit: retry with new leader
    ///    d. If exceeded: escalate to TimeLock checkpoint sync
    ///
    /// # Arguments
    /// * `masternode_registry` - For computing next leader
    ///
    /// # Returns
    /// Number of timed-out rounds that were retried or escalated
    ///
    /// # Example
    /// ```ignore
    /// // Called every 5 seconds by background task
    /// let retry_count = consensus.check_fallback_timeouts(&registry, &prev_block_hash).await;
    /// if retry_count > 0 {
    ///     info!("Retried {} timed-out fallback rounds", retry_count);
    /// }
    /// ```
    pub async fn check_fallback_timeouts(
        &self,
        masternode_registry: &MasternodeRegistry,
        prev_block_hash: &Hash256,
    ) -> usize {
        let now = Instant::now();
        let mut retried_count = 0;

        // Collect timed-out transactions
        let timed_out: Vec<(Hash256, u64, u32, Instant)> = self
            .timevote
            .fallback_rounds
            .iter()
            .filter_map(|entry| {
                let (txid, (slot_index, round_count, started_at)) = entry.pair();
                let elapsed = now.duration_since(*started_at);

                if elapsed >= FALLBACK_ROUND_TIMEOUT {
                    Some((*txid, *slot_index, *round_count, *started_at))
                } else {
                    None
                }
            })
            .collect();

        // Handle each timeout
        for (txid, slot_index, round_count, _started_at) in timed_out {
            if round_count >= MAX_FALLBACK_ROUNDS {
                // Exceeded max rounds - escalate to TimeLock
                tracing::error!(
                    "❌ Transaction {} exceeded MAX_FALLBACK_ROUNDS ({}), escalating to TimeLock",
                    hex::encode(txid),
                    MAX_FALLBACK_ROUNDS
                );

                // Mark for TimeLock escalation
                self.transition_to_rejected(
                    txid,
                    format!(
                        "Fallback failed after {} rounds, awaiting TimeLock sync",
                        MAX_FALLBACK_ROUNDS
                    ),
                );

                // Remove from fallback tracking
                self.timevote.fallback_rounds.remove(&txid);
                retried_count += 1;
            } else {
                // Retry with new leader (increment slot_index)
                let new_slot_index = slot_index + 1;
                let new_round_count = round_count + 1;

                tracing::warn!(
                    "⏱️ Fallback round timeout for tx {} (slot {}, round {}/{}), retrying with slot {}",
                    hex::encode(txid),
                    slot_index,
                    round_count,
                    MAX_FALLBACK_ROUNDS,
                    new_slot_index
                );

                // Update fallback round tracker
                self.timevote
                    .fallback_rounds
                    .insert(txid, (new_slot_index, new_round_count, Instant::now()));

                // Compute new leader
                let masternodes = masternode_registry.list_all().await;
                let avs: Vec<Masternode> = masternodes
                    .iter()
                    .filter(|mn| mn.is_active)
                    .map(|mn| mn.masternode.clone())
                    .collect();

                if let Some(new_leader_id) =
                    compute_fallback_leader(&txid, new_slot_index, &avs, prev_block_hash)
                {
                    tracing::info!(
                        "🔄 New leader for tx {}: {} (slot {})",
                        hex::encode(txid),
                        new_leader_id,
                        new_slot_index
                    );

                    // If we are the new leader, broadcast proposal
                    if let Some(identity) = self.identity.get() {
                        if identity.address == new_leader_id {
                            tracing::info!(
                                "✅ We are the new leader for tx {} (slot {}), broadcasting proposal",
                                hex::encode(txid),
                                new_slot_index
                            );

                            // Decide proposal vote
                            let decision = match self.get_tx_status(&txid) {
                                Some(TransactionStatus::FallbackResolution { .. }) => {
                                    FallbackDecision::Accept
                                }
                                _ => FallbackDecision::Reject,
                            };

                            // Broadcast the proposal
                            if let Err(e) = self
                                .broadcast_finality_proposal(txid, new_slot_index, decision)
                                .await
                            {
                                tracing::error!(
                                    "Failed to broadcast retry proposal for tx {}: {}",
                                    hex::encode(txid),
                                    e
                                );
                            }
                        }
                    }

                    retried_count += 1;
                } else {
                    tracing::error!(
                        "Could not compute new leader for tx {} (empty AVS?)",
                        hex::encode(txid)
                    );
                }
            }
        }

        retried_count
    }

    /// Start a background task that periodically checks for fallback round timeouts (§7.6.3)
    ///
    /// This spawns a tokio task that runs every `check_interval_secs` seconds
    /// to detect and handle timed-out fallback rounds.
    ///
    /// # Arguments
    /// * `consensus` - Arc reference to ConsensusEngine
    /// * `masternode_registry` - For computing new leaders
    /// * `check_interval_secs` - How often to check (recommended: 5 seconds)
    ///
    /// # Returns
    /// JoinHandle for the background task
    ///
    /// # Example
    /// ```ignore
    /// let timeout_checker = ConsensusEngine::start_fallback_timeout_checker(
    ///     consensus.clone(),
    ///     registry.clone(),
    ///     5, // Check every 5 seconds
    /// );
    /// ```
    pub fn start_fallback_timeout_checker(
        consensus: Arc<Self>,
        masternode_registry: Arc<MasternodeRegistry>,
        check_interval_secs: u64,
    ) -> tokio::task::JoinHandle<()> {
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(check_interval_secs));
            interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

            loop {
                interval.tick().await;

                // Check for timed-out fallback rounds
                let retry_count = consensus
                    .check_fallback_timeouts(&masternode_registry, &consensus.get_prev_block_hash())
                    .await;

                if retry_count > 0 {
                    tracing::info!(
                        "§7.6 Timeout checker handled {} fallback round timeouts",
                        retry_count
                    );
                }
            }
        })
    }

    // ========================================================================
    // §7.6 LIVENESS FALLBACK PROTOCOL - BROADCASTING
    // ========================================================================

    /// Broadcast a LivenessAlert for a stalled transaction (§7.6.2)
    ///
    /// Called when a local node detects a transaction has been in Sampling state
    /// for longer than STALL_TIMEOUT (30 seconds) without reaching finality.
    ///
    /// # Protocol Flow
    /// 1. Extracts transaction state (confidence, stall duration)
    /// 2. Signs alert with node's Ed25519 key
    /// 3. Broadcasts to all peers via gossip protocol
    /// 4. Peers will accumulate alerts and trigger fallback when f+1 threshold reached
    ///
    /// # Arguments
    /// * `txid` - Transaction identifier that is stalled
    /// * `slot_index` - Current TimeLock slot index (10-minute epochs)
    ///
    /// # Returns
    /// * `Ok(())` - Alert signed and broadcast successfully
    /// * `Err(String)` - If identity not set, transaction not found, or not in Sampling state
    ///
    /// # Example
    /// ```ignore
    /// // Called periodically by stall checker
    /// if consensus.check_stall_timeout(&txid) {
    ///     consensus.broadcast_liveness_alert(txid, current_slot).await?;
    /// }
    /// ```
    /// Called when local node detects a transaction has stalled
    pub async fn broadcast_liveness_alert(
        &self,
        txid: Hash256,
        slot_index: u64,
    ) -> Result<(), String> {
        // Require identity to sign alerts
        let identity = self
            .identity
            .get()
            .ok_or_else(|| "Node identity not set".to_string())?;

        // Get current transaction state
        let tx_status = self
            .timevote
            .tx_status
            .get(&txid)
            .ok_or_else(|| format!("Transaction {} not found", hex::encode(txid)))?;

        // Extract confidence and stall duration
        let (current_confidence, stall_duration_ms) = match tx_status.value() {
            TransactionStatus::Voting {
                confidence,
                started_at,
                ..
            } => {
                let elapsed = chrono::Utc::now().timestamp_millis() - started_at;
                (*confidence, elapsed.max(0) as u64)
            }
            _ => {
                return Err(format!(
                    "Transaction {} not in Voting state",
                    hex::encode(txid)
                ))
            }
        };

        // Get tx_hash_commitment (use txid for now, will be transaction hash in full implementation)
        let tx_hash_commitment = txid;

        // Get poll history (empty for now, will be populated from vote accumulation)
        let poll_history = Vec::new();

        // Sign and create the alert
        let alert = identity.sign_liveness_alert(
            1, // chain_id = 1 for mainnet
            txid,
            tx_hash_commitment,
            slot_index,
            poll_history,
            stall_duration_ms,
            current_confidence,
        );

        tracing::warn!(
            "Broadcasting LivenessAlert for tx {} (stall: {}ms, confidence: {})",
            hex::encode(txid),
            stall_duration_ms,
            current_confidence
        );

        // Broadcast to network
        self.broadcast(NetworkMessage::LivenessAlert { alert })
            .await;

        Ok(())
    }

    /// Determine fallback decision based on TimeVote state (§7.6.4 Step 2)
    ///
    /// Leader analyzes the transaction's current TimeVote state to decide whether
    /// to propose Accept or Reject in the fallback consensus round.
    ///
    /// # Decision Logic (§7.6.4)
    /// ```text
    /// IF counter[Accept] > counter[Reject]:
    ///   → Decision = Accept (transaction has majority support)
    /// ELSE:
    ///   → Decision = Reject (transaction lacks consensus)
    /// ```
    ///
    /// # Arguments
    /// * `txid` - Transaction to evaluate
    ///
    /// # Returns
    /// * `FallbackDecision` - Either Accept or Reject
    ///
    /// # Example
    /// ```ignore
    /// // Leader elected, now decide what to propose
    /// let decision = consensus.determine_fallback_decision(&txid);
    /// consensus.broadcast_finality_proposal(txid, slot, decision).await?;
    /// ```
    pub fn determine_fallback_decision(&self, txid: &Hash256) -> FallbackDecision {
        // Get the voting state for this transaction
        if let Some(voting_state) = self.timevote.tx_state.get(txid) {
            let state = voting_state.value().read();

            let preference = state.preference;

            tracing::debug!(
                "Fallback decision for tx {}: preference={:?}",
                hex::encode(&txid[..8]),
                preference
            );

            match preference {
                Preference::Accept => FallbackDecision::Accept,
                Preference::Reject => FallbackDecision::Reject,
            }
        } else {
            // No voting state found, default to Reject
            tracing::warn!(
                "No voting state found for tx {}, defaulting to Reject",
                hex::encode(&txid[..8])
            );
            FallbackDecision::Reject
        }
    }

    /// Execute fallback resolution as elected leader (§7.6.4 Steps 1-3)
    ///
    /// Called when this node has been deterministically elected as the fallback leader
    /// for a stalled transaction. The leader:
    /// 1. Determines decision based on vote counters
    /// 2. Signs and broadcasts FinalityProposal
    /// 3. Waits for Q_finality votes from AVS
    ///
    /// # Arguments
    /// * `txid` - Transaction to resolve
    /// * `slot_index` - Current slot (for leader election)
    /// * `round` - Fallback round number (0-4)
    ///
    /// # Returns
    /// * `Ok(())` - Proposal broadcast successfully
    /// * `Err(String)` - If not leader or broadcast failed
    ///
    /// # Example
    /// ```ignore
    /// let avs = consensus.get_avs_snapshot(slot)?;
    /// if consensus.is_fallback_leader(txid, slot, 0, &avs, &prev_block_hash) {
    ///     consensus.execute_fallback_as_leader(txid, slot, 0).await?;
    /// }
    /// ```
    pub async fn execute_fallback_as_leader(
        &self,
        txid: Hash256,
        slot_index: u64,
        round: u32,
    ) -> Result<(), String> {
        tracing::info!(
            "🎯 Executing fallback as leader for tx {} (slot: {}, round: {})",
            hex::encode(&txid[..8]),
            slot_index,
            round
        );

        // Determine decision based on vote state
        let decision = self.determine_fallback_decision(&txid);

        tracing::info!(
            "📋 Leader decided: {:?} for tx {}",
            decision,
            hex::encode(&txid[..8])
        );

        // Broadcast proposal to AVS
        self.broadcast_finality_proposal(txid, slot_index, decision)
            .await?;

        // Track this round
        self.timevote
            .fallback_rounds
            .insert(txid, (slot_index, round, Instant::now()));

        Ok(())
    }

    /// Broadcast a FinalityProposal as deterministic leader (§7.6.4 Step 3)
    ///
    /// Called when this node has been elected as the deterministic fallback leader
    /// and must propose an Accept/Reject decision for a stalled transaction.
    ///
    /// # Protocol Flow (§7.6.4)
    /// 1. Node computes itself as leader via `elect_fallback_leader(txid, slot, AVS, prev_block_hash)`
    /// 2. Signs proposal with decision (Accept or Reject)
    /// 3. Broadcasts to all AVS members
    /// 4. AVS members vote on the proposal
    /// 5. Transaction finalized if Q_finality votes received
    ///
    /// # Leader Election
    /// Leader is deterministic: `leader = MN with minimum H(txid || slot_index || mn_pubkey)`
    /// All nodes compute same leader independently without coordination.
    ///
    /// # Arguments
    /// * `txid` - Transaction being proposed for finalization
    /// * `slot_index` - Current slot (increments on timeout for new leader)
    /// * `decision` - FallbackDecision::Accept or FallbackDecision::Reject
    ///
    /// # Returns
    /// * `Ok(())` - Proposal signed and broadcast successfully
    /// * `Err(String)` - If identity not set
    ///
    /// # Example
    /// ```ignore
    /// let leader = consensus.compute_fallback_leader(&txid, slot, &avs_members, &prev_block_hash)?;
    /// if leader.address == my_address {
    ///     consensus.broadcast_finality_proposal(txid, slot, FallbackDecision::Accept).await?;
    /// }
    /// ```
    pub async fn broadcast_finality_proposal(
        &self,
        txid: Hash256,
        slot_index: u64,
        decision: FallbackDecision,
    ) -> Result<(), String> {
        // Require identity to sign proposals
        let identity = self
            .identity
            .get()
            .ok_or_else(|| "Node identity not set".to_string())?;

        // Get tx_hash_commitment (use txid for now)
        let tx_hash_commitment = txid;

        // Create justification string
        let justification = format!("Fallback decision for slot {}", slot_index);

        // Sign and create the proposal
        let proposal = identity.sign_finality_proposal(
            1, // chain_id = 1 for mainnet
            txid,
            tx_hash_commitment,
            slot_index,
            decision.clone(),
            justification,
        );

        tracing::info!(
            "Broadcasting FinalityProposal for tx {} (decision: {:?})",
            hex::encode(txid),
            decision
        );

        // Broadcast to network
        self.broadcast(NetworkMessage::FinalityProposal { proposal })
            .await;

        Ok(())
    }

    /// Broadcast a FallbackVote on a leader's proposal (§7.6.4 Step 4)
    ///
    /// Called when an AVS member node receives a FinalityProposal and must vote.
    ///
    /// # Protocol Flow
    /// 1. Receive FinalityProposal from deterministic leader
    /// 2. Validate proposal (correct leader, valid decision)
    /// 3. Vote Approve or Reject based on local view
    /// 4. Broadcast vote to all AVS members
    /// 5. Accumulate votes until Q_finality threshold reached
    ///
    /// # Arguments
    /// * `proposal_hash` - Hash of the FinalityProposal being voted on
    /// * `vote` - FallbackVoteDecision::Approve or FallbackVoteDecision::Reject
    /// * `voter_weight` - Stake weight of this masternode
    ///
    /// # Returns
    /// * `Ok(())` - Vote signed and broadcast successfully
    /// * `Err(String)` - If identity not set
    ///
    /// # Example
    /// ```ignore
    /// // On receiving FinalityProposal
    /// let vote_decision = validate_proposal(&proposal)?;
    /// let my_weight = get_my_stake_weight();
    /// consensus.broadcast_fallback_vote(proposal.hash(), vote_decision, my_weight).await?;
    /// ```
    pub async fn broadcast_fallback_vote(
        &self,
        proposal_hash: Hash256,
        vote: FallbackVoteDecision,
        voter_weight: u64,
    ) -> Result<(), String> {
        // Require identity to sign votes
        let identity = self
            .identity
            .get()
            .ok_or_else(|| "Node identity not set".to_string())?;

        // Sign and create the vote
        let fallback_vote = identity.sign_fallback_vote(
            1, // chain_id = 1 for mainnet
            proposal_hash,
            vote.clone(),
            voter_weight,
        );

        tracing::debug!(
            "Broadcasting FallbackVote for proposal {} (vote: {:?}, weight: {})",
            hex::encode(proposal_hash),
            vote,
            voter_weight
        );

        // Broadcast to network
        self.broadcast(NetworkMessage::FallbackVote {
            vote: fallback_vote,
        })
        .await;

        Ok(())
    }

    /// Check for stalled transactions and broadcast alerts (§7.6.1-7.6.2)
    ///
    /// Scans all active transactions for stalls (Sampling > STALL_TIMEOUT)
    /// and broadcasts LivenessAlerts for each one found.
    ///
    /// # Timing
    /// Should be called periodically (e.g., every 5-10 seconds) via background task.
    /// See `start_stall_checker()` for automated periodic checking.
    ///
    /// # Arguments
    /// * `current_slot` - Current TimeLock slot index for alert timestamp
    ///
    /// # Returns
    /// * Number of stalled transactions found and alerted
    ///
    /// # Performance
    /// * Time complexity: O(N) where N = active transactions
    /// * Typical duration: < 1ms for N < 1000
    ///
    /// # Example
    /// ```ignore
    /// // Manual check
    /// let slot = get_current_slot();
    /// let stalled_count = consensus.check_and_broadcast_stalls(slot).await;
    /// if stalled_count > 0 {
    ///     warn!("Found {} stalled transactions", stalled_count);
    /// }
    /// ```
    pub async fn check_and_broadcast_stalls(&self, current_slot: u64) -> usize {
        let stalled = self.get_stalled_transactions();
        let count = stalled.len();

        for txid in stalled {
            if let Err(e) = self.broadcast_liveness_alert(txid, current_slot).await {
                tracing::error!("Failed to broadcast LivenessAlert: {}", e);
            }
        }

        if count > 0 {
            tracing::warn!(
                "Detected and broadcast alerts for {} stalled transactions",
                count
            );
        }

        count
    }

    /// Resume timevote sampling after fallback completes (§7.6.5)
    ///
    /// Transitions transaction from FallbackResolution back to Sampling state.
    /// Used when fallback times out or otherwise fails to finalize.
    ///
    /// # Protocol Flow (§7.6.5)
    /// 1. Fallback round times out (no Q_finality votes received in 10s)
    /// 2. Increment slot_index → new deterministic leader
    /// 3. If MAX_FALLBACK_ROUNDS exceeded, resume timevote sampling
    /// 4. Transaction gets fresh stall timer, returns to normal consensus
    ///
    /// # Arguments
    /// * `txid` - Transaction to resume sampling for
    ///
    /// # Returns
    /// * `Ok(())` - Successfully transitioned back to Sampling
    /// * `Err(String)` - If transaction not found or not in FallbackResolution state
    ///
    /// # State Transitions
    /// ```text
    /// FallbackResolution → Sampling (with fresh timer)
    /// ```
    ///
    /// # Example
    /// ```ignore
    /// // After fallback timeout
    /// if fallback_round_failed && round_count >= MAX_FALLBACK_ROUNDS {
    ///     consensus.resume_sampling_after_fallback(txid)?;
    ///     info!("Resumed timevote sampling for tx {}", hex::encode(txid));
    /// }
    /// ```
    pub fn resume_sampling_after_fallback(&self, txid: Hash256) -> Result<(), String> {
        // Check current status
        let current_status = self
            .timevote
            .tx_status
            .get(&txid)
            .ok_or_else(|| format!("Transaction {} not found", hex::encode(txid)))?;

        // Only resume if in FallbackResolution
        if !matches!(
            current_status.value(),
            TransactionStatus::FallbackResolution { .. }
        ) {
            return Err(format!(
                "Transaction {} not in FallbackResolution state",
                hex::encode(txid)
            ));
        }

        drop(current_status);

        // Reset to Voting state with fresh timer
        self.transition_to_voting(txid);

        tracing::info!(
            "Resumed TimeVote voting for TX {} after fallback",
            hex::encode(txid)
        );

        Ok(())
    }

    /// Start background task for periodic stall checking (§7.6)
    ///
    /// Spawns a Tokio task that continuously monitors for stalled transactions
    /// and automatically broadcasts LivenessAlerts.
    ///
    /// # Usage
    /// Call once during node initialization, after ConsensusEngine is ready:
    /// ```ignore
    /// let consensus = Arc::new(consensus_engine);
    /// let handle = ConsensusEngine::start_stall_checker(consensus.clone(), 10);
    /// // Keep handle if you need to cancel checker later
    /// ```
    ///
    /// # Arguments
    /// * `consensus` - Arc reference to ConsensusEngine (required for 'static lifetime)
    /// * `check_interval_secs` - Seconds between stall checks (recommended: 5-10)
    ///
    /// # Returns
    /// * `JoinHandle<()>` - Handle to the background task (can be cancelled if needed)
    ///
    /// # Protocol Timing
    /// * Stall detection: 30 seconds (STALL_TIMEOUT)
    /// * Check interval: configurable (default 10s in production)
    /// * Max alert delay: check_interval_secs + network propagation (~11s typical)
    ///
    /// # Performance
    /// * CPU: ~0.1ms per check (O(N) scan of active transactions)
    /// * Memory: No additional allocation (uses existing state)
    /// * Network: Only broadcasts when stalls detected (rare in normal operation)
    ///
    /// # Example
    /// ```ignore
    /// // In main.rs or node initialization
    /// let consensus = Arc::new(consensus_engine);
    /// let stall_checker_handle = ConsensusEngine::start_stall_checker(
    ///     consensus.clone(),
    ///     10, // Check every 10 seconds
    /// );
    /// info!("§7.6 Stall checker started");
    /// ```
    pub fn start_stall_checker(
        consensus: Arc<Self>,
        check_interval_secs: u64,
    ) -> tokio::task::JoinHandle<()> {
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(check_interval_secs));
            interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

            loop {
                interval.tick().await;

                // Get current slot index (placeholder - will be integrated with TimeLock)
                let current_slot = (chrono::Utc::now().timestamp() as u64) / 600; // 10-minute slots

                // Check for stalled transactions and broadcast alerts
                let stalled_count = consensus.check_and_broadcast_stalls(current_slot).await;

                if stalled_count > 0 {
                    tracing::warn!(
                        "§7.6 Stall checker found {} stalled transactions",
                        stalled_count
                    );
                }
            }
        })
    }

    #[allow(dead_code)]
    pub async fn generate_deterministic_block(&self, height: u64, _timestamp: i64) -> Block {
        use crate::block::generator::DeterministicBlockGenerator;

        let finalized = self.get_finalized_transactions_with_fees_for_block();
        let (finalized_txs, fees): (Vec<_>, Vec<_>) = finalized.into_iter().unzip();
        let masternodes = self.get_masternodes_with_rewards();
        let previous_hash = [0u8; 32];
        let base_reward = 100;

        DeterministicBlockGenerator::generate(
            height,
            previous_hash,
            finalized_txs,
            fees,
            masternodes,
            base_reward,
        )
    }

    #[allow(dead_code)]
    pub async fn generate_deterministic_block_with_eligible(
        &self,
        height: u64,
        _timestamp: i64,
        eligible: Vec<(Masternode, String)>,
    ) -> Block {
        use crate::block::generator::DeterministicBlockGenerator;

        let finalized = self.get_finalized_transactions_with_fees_for_block();
        let (finalized_txs, fees): (Vec<_>, Vec<_>) = finalized.into_iter().unzip();
        let previous_hash = [0u8; 32];
        let base_reward = 100;

        DeterministicBlockGenerator::generate(
            height,
            previous_hash,
            finalized_txs,
            fees,
            eligible,
            base_reward,
        )
    }

    #[allow(dead_code)]
    pub async fn generate_deterministic_block_with_masternodes(
        &self,
        height: u64,
        _timestamp: i64,
        masternodes: Vec<(Masternode, String)>,
    ) -> Block {
        use crate::block::generator::DeterministicBlockGenerator;

        let finalized = self.get_finalized_transactions_with_fees_for_block();
        let (finalized_txs, fees): (Vec<_>, Vec<_>) = finalized.into_iter().unzip();
        let previous_hash = [0u8; 32];
        let base_reward = 100;

        DeterministicBlockGenerator::generate(
            height,
            previous_hash,
            finalized_txs,
            fees,
            masternodes,
            base_reward,
        )
    }
}

/// Partition a list of transactions into groups of mutually non-conflicting sets.
///
/// Within each returned group every transaction has a disjoint set of UTXO inputs,
/// so the entire group can be submitted concurrently via `batch_submit_transactions`
/// without any UTXO lock contention.  Transactions that share inputs (potential
/// double-spends) are placed in separate groups so callers can detect or order them.
pub fn partition_non_conflicting(txs: Vec<Transaction>) -> Vec<Vec<Transaction>> {
    let mut groups: Vec<Vec<Transaction>> = Vec::new();
    let mut group_inputs: Vec<std::collections::HashSet<OutPoint>> = Vec::new();

    'next_tx: for tx in txs {
        let tx_inputs: std::collections::HashSet<OutPoint> = tx
            .inputs
            .iter()
            .map(|i| i.previous_output.clone())
            .collect();

        for (i, existing) in group_inputs.iter_mut().enumerate() {
            if existing.is_disjoint(&tx_inputs) {
                existing.extend(tx_inputs);
                groups[i].push(tx);
                continue 'next_tx;
            }
        }

        // No compatible group found — open a new one
        group_inputs.push(tx_inputs);
        groups.push(vec![tx]);
    }

    groups
}

/// Returns `(finality_threshold, min_weight_floor)` for TimeVote timeout handling.
/// Uses 67% of AVS weight; falls back to 51% after 30s stall (Protocol §7.6).
pub(crate) fn vote_finality_threshold(total_avs_weight: u64, elapsed_secs: u64) -> (u64, u64) {
    let q_percent = if elapsed_secs >= 30 { 51u64 } else { 67u64 };
    let threshold = (total_avs_weight * q_percent).div_ceil(100);
    (threshold, threshold.div_ceil(4))
}

#[cfg(test)]
fn create_test_registry() -> Arc<MasternodeRegistry> {
    let db = Arc::new(sled::Config::new().temporary(true).open().unwrap());
    Arc::new(MasternodeRegistry::new(db, crate::NetworkType::Testnet))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_txid(byte: u8) -> Hash256 {
        [byte; 32]
    }

    fn make_tx(inputs: &[(u8, u32)]) -> Transaction {
        Transaction {
            version: 1,
            inputs: inputs
                .iter()
                .map(|(txid_byte, vout)| TxInput {
                    previous_output: OutPoint {
                        txid: [*txid_byte; 32],
                        vout: *vout,
                    },
                    script_sig: vec![],
                    sequence: 0,
                })
                .collect(),
            outputs: vec![],
            lock_time: 0,
            timestamp: 0,
            special_data: None,
            encrypted_memo: None,
        }
    }

    #[test]
    fn test_partition_all_independent() {
        // A, B, C each spend different UTXOs → all land in one group
        let txs = vec![make_tx(&[(1, 0)]), make_tx(&[(2, 0)]), make_tx(&[(3, 0)])];
        let groups = partition_non_conflicting(txs);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].len(), 3);
    }

    #[test]
    fn test_partition_conflict_splits_groups() {
        // A and B both spend UTXO (1, 0) → must land in different groups
        let tx_a = make_tx(&[(1, 0)]);
        let tx_b = make_tx(&[(1, 0)]);
        let tx_c = make_tx(&[(2, 0)]);
        let groups = partition_non_conflicting(vec![tx_a, tx_b, tx_c]);
        assert_eq!(groups.len(), 2);
        // Group 0 gets A and C (C is disjoint from A); Group 1 gets B
        assert_eq!(groups[0].len(), 2);
        assert_eq!(groups[1].len(), 1);
    }

    #[test]
    fn test_partition_empty() {
        let groups = partition_non_conflicting(vec![]);
        assert!(groups.is_empty());
    }

    #[test]
    fn test_partition_single_tx() {
        let groups = partition_non_conflicting(vec![make_tx(&[(1, 0)])]);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].len(), 1);
    }

    #[test]
    fn test_partition_multi_input_tx() {
        // TX A spends (1,0) and (2,0); TX B spends (3,0) → no conflict → one group
        let tx_a = make_tx(&[(1, 0), (2, 0)]);
        let tx_b = make_tx(&[(3, 0)]);
        let groups = partition_non_conflicting(vec![tx_a, tx_b]);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].len(), 2);
    }

    #[test]
    fn test_partition_multi_input_conflict() {
        // TX A spends (1,0) and (2,0); TX B spends (2,0) → conflict on (2,0)
        let tx_a = make_tx(&[(1, 0), (2, 0)]);
        let tx_b = make_tx(&[(2, 0)]);
        let groups = partition_non_conflicting(vec![tx_a, tx_b]);
        assert_eq!(groups.len(), 2);
    }

    #[test]
    fn test_vote_finality_threshold_requires_quorum() {
        let (threshold, floor) = vote_finality_threshold(1000, 0);
        assert_eq!(threshold, 670);
        assert_eq!(floor, 168);
        assert!(0 < threshold, "zero votes must not satisfy quorum");
        assert!(669 < threshold);
        assert!(670 >= threshold);

        let (fallback, _) = vote_finality_threshold(1000, 30);
        assert_eq!(fallback, 510);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn test_timevote_init() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let _av = TimeVoteConsensus::new(config, registry.clone()).unwrap();
        // Verify empty registry has no active masternodes (use async path directly
        // to avoid block_in_place + tokio::sync::RwLock deadlock in test context)
        assert_eq!(registry.list_active().await.len(), 0);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn test_validator_management() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let _av = TimeVoteConsensus::new(config, registry.clone()).unwrap();
        // Validators come from masternode registry; verify empty registry works
        assert_eq!(registry.list_active().await.len(), 0);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn test_initiate_consensus() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let av = TimeVoteConsensus::new(config, registry).unwrap();
        let txid = test_txid(1);

        assert!(av.initiate_consensus(txid, Preference::Accept));
        assert!(!av.initiate_consensus(txid, Preference::Accept)); // Already initiated

        let (pref, finalized) = av.get_tx_state(&txid).unwrap();
        assert_eq!(pref, Preference::Accept);
        assert!(!finalized);
    }

    #[tokio::test]
    async fn test_invalid_config() {
        let registry = create_test_registry();

        let config = TimeVoteConfig {
            sample_size: 0,
            ..Default::default()
        };
        assert!(TimeVoteConsensus::new(config, registry.clone()).is_err());

        let config = TimeVoteConfig {
            finality_confidence: 0,
            ..Default::default()
        };
        assert!(TimeVoteConsensus::new(config, registry).is_err());
    }
}

// ============================================================================
// §7.6 LIVENESS FALLBACK PROTOCOL - Leader Election
// ============================================================================

/// Compute deterministic fallback leader for a stalled transaction (§7.6.4 Step 2)
///
/// Uses SHA-256 hash function to select a leader that all nodes compute identically,
/// without any message exchange or coordination. Leader selection is deterministic
/// based on transaction ID, slot index, and masternode public keys.
///
/// # Algorithm
/// ```text
/// For each masternode in AVS:
///     score = H(txid || slot_index || mn_pubkey)
/// leader = masternode with minimum score
/// ```
///
/// # Properties
/// - **Deterministic:** Same inputs → same output on all nodes
/// - **Unpredictable:** Hash function prevents gaming the system
/// - **Fair:** Each masternode has equal probability (uniform hash distribution)
/// - **Timeout-resistant:** Incrementing slot_index selects new leader
///
/// # Timeout Handling (§7.6.5)
/// If leader fails or times out:
/// 1. All nodes increment `slot_index`
/// 2. Recompute leader with new slot_index
/// 3. New leader deterministically selected
/// 4. No coordination or view change messages needed
///
/// # Arguments
/// * `txid` - The stalled transaction ID (32 bytes)
/// * `slot_index` - Current slot index (increments on timeout)
/// * `avs` - Active Validator Set snapshot (from Protocol §8.4)
///
/// # Returns
/// * `Some(mn_id)` - The masternode address of the elected leader
/// * `None` - If AVS is empty (should not happen in production)
///
/// # Performance
/// * Time: O(N log N) where N = AVS size (dominated by sorting)
/// * Space: O(N) for score vector
/// * Typical: < 1ms for N = 100 masternodes
///
/// # Example
/// ```ignore
/// // All nodes compute same leader independently
/// let txid = stalled_transaction.txid();
/// let slot = current_slot_index();
/// let avs = consensus.get_avs_snapshot(slot)?;
///
/// let leader_id = compute_fallback_leader(&txid, slot, &avs, &prev_block_hash).unwrap();
///
/// if leader_id == my_node_id {
///     // I am the leader, propose decision
///     consensus.broadcast_finality_proposal(txid, slot, decision).await?;
/// }
/// ```
pub fn compute_fallback_leader(
    txid: &Hash256,
    slot_index: u64,
    avs: &[Masternode],
    prev_block_hash: &Hash256,
) -> Option<String> {
    if avs.is_empty() {
        return None;
    }

    // Compute hash score for each masternode
    // Including prev_block_hash prevents prediction of leader before latest block is produced
    let mut scores: Vec<(Hash256, String)> = avs
        .iter()
        .map(|mn| {
            let mut hasher = Sha256::new();
            hasher.update(txid);
            hasher.update(slot_index.to_le_bytes());
            hasher.update(prev_block_hash);
            hasher.update(mn.public_key.as_bytes());
            let score: Hash256 = hasher.finalize().into();
            (score, mn.address.clone())
        })
        .collect();

    // Leader is the masternode with minimum hash score
    scores.sort_by_key(|a| a.0);

    scores.first().map(|(_, mn_id)| mn_id.clone())
}

#[cfg(test)]
mod fallback_tests {
    use super::*;
    use ed25519_dalek::SigningKey;

    #[test]
    fn test_compute_fallback_leader_deterministic() {
        // Create test masternodes
        let mut avs = Vec::new();
        for i in 0..5 {
            let signing_key = SigningKey::from_bytes(&[i; 32]);
            avs.push(Masternode::new_legacy(
                format!("mn{}", i),
                format!("wallet{}", i),
                1000,
                signing_key.verifying_key(),
                MasternodeTier::Bronze,
                0,
            ));
        }

        let txid = [1u8; 32];
        let slot_index = 100;

        // Compute leader twice - should be same
        let prev_hash = [0u8; 32];
        let leader1 = compute_fallback_leader(&txid, slot_index, &avs, &prev_hash);
        let leader2 = compute_fallback_leader(&txid, slot_index, &avs, &prev_hash);
        assert_eq!(leader1, leader2);
        assert!(leader1.is_some());

        // Different slot should give potentially different leader
        let leader3 = compute_fallback_leader(&txid, slot_index + 1, &avs, &prev_hash);
        assert!(leader3.is_some());
        // May or may not be different, but function should work

        // Different txid should give potentially different leader
        let txid2 = [2u8; 32];
        let leader4 = compute_fallback_leader(&txid2, slot_index, &avs, &prev_hash);
        assert!(leader4.is_some());
    }

    #[test]
    fn test_compute_fallback_leader_empty_avs() {
        let txid = [1u8; 32];
        let slot_index = 100;
        let avs: Vec<Masternode> = Vec::new();

        let leader = compute_fallback_leader(&txid, slot_index, &avs, &[0u8; 32]);
        assert!(leader.is_none());
    }

    // ========================================================================
    // §7.6 LIVENESS FALLBACK PROTOCOL - INTEGRATION TESTS
    // ========================================================================

    /// Test that fallback round tracking is initialized and cleaned up properly
    #[tokio::test]
    async fn test_fallback_tracking_lifecycle() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();
        let txid = [99u8; 32];

        // Initially no tracking
        assert!(consensus.fallback_rounds.get(&txid).is_none());

        // Start tracking
        consensus
            .fallback_rounds
            .insert(txid, (100, 0, Instant::now()));

        // Verify present
        assert!(consensus.fallback_rounds.get(&txid).is_some());

        // Remove tracking
        consensus.fallback_rounds.remove(&txid);

        // Verify cleaned up
        assert!(consensus.fallback_rounds.get(&txid).is_none());
    }

    /// Test Q_finality calculation: majority threshold
    #[test]
    fn test_q_finality_calculation() {
        // Test various total weights
        let total1 = 6_000_000_000u64;
        let q1 = (total1 * 2) / 3;
        assert_eq!(q1, 4_000_000_000u64);

        let total2 = 10_000_000_000u64;
        let q2 = (total2 * 2) / 3;
        assert!((6_666_666_666u64..=6_666_666_667u64).contains(&q2));

        let total3 = 3_000_000_000u64;
        let q3 = (total3 * 2) / 3;
        assert_eq!(q3, 2_000_000_000u64);
    }

    /// Test f+1 threshold calculation: ⌊(n-1)/3⌋ + 1
    #[test]
    fn test_f_plus_1_threshold() {
        // n=4: f=1, need 2 alerts
        let n4 = 4;
        let f4 = (n4 - 1) / 3;
        assert_eq!(f4, 1);
        assert_eq!(f4 + 1, 2);

        // n=10: f=3, need 4 alerts
        let n10 = 10;
        let f10 = (n10 - 1) / 3;
        assert_eq!(f10, 3);
        assert_eq!(f10 + 1, 4);

        // n=100: f=33, need 34 alerts
        let n100 = 100;
        let f100 = (n100 - 1) / 3;
        assert_eq!(f100, 33);
        assert_eq!(f100 + 1, 34);
    }

    /// Test FALLBACK_ROUND_TIMEOUT constant
    #[test]
    fn test_fallback_timeout_constant() {
        assert_eq!(FALLBACK_ROUND_TIMEOUT, Duration::from_secs(10));
    }

    /// Test MAX_FALLBACK_ROUNDS constant
    #[test]
    fn test_max_fallback_rounds_constant() {
        assert_eq!(MAX_FALLBACK_ROUNDS, 5);

        // Worst-case time: 5 rounds * 10 seconds = 50 seconds
        let worst_case_ms = (MAX_FALLBACK_ROUNDS as u64) * 10 * 1000;
        assert_eq!(worst_case_ms, 50_000); // 50 seconds
    }

    /// Test proposal-to-transaction mapping operations
    #[tokio::test]
    async fn test_proposal_tx_mapping_operations() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let txid = [100u8; 32];
        let proposal_hash = [200u8; 32];

        // Initially no mapping
        assert!(consensus.proposal_to_tx.get(&proposal_hash).is_none());

        // Insert mapping
        consensus.proposal_to_tx.insert(proposal_hash, txid);

        // Verify mapping exists
        let retrieved = consensus.proposal_to_tx.get(&proposal_hash);
        assert!(retrieved.is_some());
        assert_eq!(*retrieved.unwrap(), txid);

        // Remove mapping
        consensus.proposal_to_tx.remove(&proposal_hash);

        // Verify removed
        assert!(consensus.proposal_to_tx.get(&proposal_hash).is_none());
    }

    /// Test liveness alerts accumulation structure
    #[tokio::test]
    async fn test_liveness_alerts_accumulation() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let txid = [101u8; 32];

        // Initially no alerts
        assert!(consensus.liveness_alerts.get(&txid).is_none());

        // Insert alert vector
        let alerts = Vec::new();
        consensus.liveness_alerts.insert(txid, alerts);

        // Verify exists
        assert!(consensus.liveness_alerts.get(&txid).is_some());

        // Clean up
        consensus.liveness_alerts.remove(&txid);
        assert!(consensus.liveness_alerts.get(&txid).is_none());
    }

    /// Test fallback votes accumulation structure
    #[tokio::test]
    async fn test_fallback_votes_accumulation() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let proposal_hash = [202u8; 32];

        // Initially no votes
        assert!(consensus.fallback_votes.get(&proposal_hash).is_none());

        // Insert vote vector
        let votes = Vec::new();
        consensus.fallback_votes.insert(proposal_hash, votes);

        // Verify exists
        assert!(consensus.fallback_votes.get(&proposal_hash).is_some());

        // Clean up
        consensus.fallback_votes.remove(&proposal_hash);
        assert!(consensus.fallback_votes.get(&proposal_hash).is_none());
    }

    /// Test that DashMap operations are thread-safe
    #[tokio::test]
    async fn test_dashmap_concurrent_safety() {
        use std::sync::Arc;
        use std::thread;

        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = Arc::new(TimeVoteConsensus::new(config, registry).unwrap());

        let handles: Vec<_> = (0..10)
            .map(|i| {
                let consensus = Arc::clone(&consensus);
                thread::spawn(move || {
                    let txid = [i; 32];
                    consensus
                        .fallback_rounds
                        .insert(txid, (i as u64, 0, Instant::now()));
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        // Verify all inserts succeeded
        for i in 0..10u8 {
            let txid = [i; 32];
            assert!(consensus.fallback_rounds.get(&txid).is_some());
        }
    }

    /// Test leader determinism: same inputs always give same leader
    #[test]
    fn test_leader_election_determinism() {
        use ed25519_dalek::SigningKey;

        let txid = [123u8; 32];
        let slot_index = 456u64;

        let avs: Vec<Masternode> = (0..5)
            .map(|i| {
                let signing_key = SigningKey::from_bytes(&[i; 32]);
                Masternode::new_legacy(
                    format!("mn{}", i),
                    format!("wallet{}", i),
                    1_000_000_000,
                    signing_key.verifying_key(),
                    MasternodeTier::Bronze,
                    0,
                )
            })
            .collect();

        // Compute leader multiple times
        let prev_hash = [0u8; 32];
        let leader1 = compute_fallback_leader(&txid, slot_index, &avs, &prev_hash);
        let leader2 = compute_fallback_leader(&txid, slot_index, &avs, &prev_hash);
        let leader3 = compute_fallback_leader(&txid, slot_index, &avs, &prev_hash);

        // All must be identical
        assert_eq!(leader1, leader2);
        assert_eq!(leader2, leader3);
    }

    // ========================================================================
    // PHASE 6: COMPREHENSIVE FALLBACK PROTOCOL TESTS
    // ========================================================================

    /// Test alert accumulation tracking
    #[tokio::test]
    async fn test_phase6_alert_accumulation() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let txid = [42u8; 32];

        // Initially no alerts
        assert!(consensus.liveness_alerts.get(&txid).is_none());

        // Add alerts directly
        for i in 0..3 {
            let alert = LivenessAlert {
                chain_id: 1,
                txid,
                tx_hash_commitment: [0u8; 32],
                slot_index: 1000,
                poll_history: vec![],
                current_confidence: 5,
                stall_duration_ms: 30000,
                reporter_mn_id: format!("mn_{}", i),
                reporter_signature: vec![],
            };

            consensus
                .liveness_alerts
                .entry(txid)
                .or_default()
                .push(alert);
        }

        // Verify count
        let alerts = consensus.liveness_alerts.get(&txid).unwrap();
        assert_eq!(alerts.len(), 3);

        // Verify unique reporters
        let unique: std::collections::HashSet<_> =
            alerts.iter().map(|a| &a.reporter_mn_id).collect();
        assert_eq!(unique.len(), 3);
    }

    /// Test vote accumulation tracking
    #[tokio::test]
    async fn test_phase6_vote_accumulation() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let proposal_hash = [42u8; 32];

        // Initially no votes
        assert!(consensus.fallback_votes.get(&proposal_hash).is_none());

        // Add votes directly to internal structure
        for i in 0..5 {
            let vote = FallbackVote {
                chain_id: 1,
                proposal_hash,
                vote: FallbackVoteDecision::Approve,
                voter_mn_id: format!("mn_{}", i),
                voter_weight: 1_000_000_000,
                voter_signature: vec![],
            };

            consensus
                .fallback_votes
                .entry(proposal_hash)
                .or_default()
                .push(vote);
        }

        // Verify votes stored
        let votes = consensus.fallback_votes.get(&proposal_hash).unwrap();
        assert_eq!(votes.len(), 5);

        // Calculate weights manually
        let approve_weight: u64 = votes
            .iter()
            .filter(|v| matches!(v.vote, FallbackVoteDecision::Approve))
            .map(|v| v.voter_weight)
            .sum();
        assert_eq!(approve_weight, 5_000_000_000);
    }

    /// Test proposal registration and lookup
    #[tokio::test]
    async fn test_phase6_proposal_tracking() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let txid = [42u8; 32];
        let proposal_hash = [1u8; 32];

        // Register proposal directly
        consensus.proposal_to_tx.insert(proposal_hash, txid);

        // Lookup should work
        let found_txid = consensus.proposal_to_tx.get(&proposal_hash).map(|v| *v);
        assert_eq!(found_txid, Some(txid));

        // Non-existent proposal
        let fake_hash = [99u8; 32];
        assert!(consensus.proposal_to_tx.get(&fake_hash).is_none());
    }

    /// Test fallback round tracking
    #[tokio::test]
    async fn test_phase6_fallback_round_tracking() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let txid = [42u8; 32];
        let slot_index = 1000u64;
        let round = 2u32;

        // Initially not tracking
        assert!(consensus.fallback_rounds.get(&txid).is_none());

        // Start tracking
        consensus
            .fallback_rounds
            .insert(txid, (slot_index, round, Instant::now()));

        // Verify tracking
        let (stored_slot, stored_round, _) = *consensus.fallback_rounds.get(&txid).unwrap().value();
        assert_eq!(stored_slot, slot_index);
        assert_eq!(stored_round, round);
    }

    /// Test Q_finality threshold calculation (simple majority)
    #[tokio::test]
    async fn test_phase6_q_finality_threshold() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let proposal_hash = [42u8; 32];
        let total_weight = 9_000_000_000u64;
        let q_finality = (total_weight * 2) / 3; // 6B

        // Add votes below threshold
        for i in 0..5 {
            let vote = FallbackVote {
                chain_id: 1,
                proposal_hash,
                vote: FallbackVoteDecision::Approve,
                voter_mn_id: format!("mn_{}", i),
                voter_weight: 1_000_000_000,
                voter_signature: vec![],
            };
            consensus
                .fallback_votes
                .entry(proposal_hash)
                .or_default()
                .push(vote);
        }

        // Calculate weight
        // NOTE: Must scope the DashMap Ref guard to avoid deadlock.
        // `.get()` returns a Ref that holds a read lock on the shard.
        // If still held when `.entry()` tries to write-lock the same shard below, it deadlocks.
        let approve_weight: u64 = {
            let votes = consensus.fallback_votes.get(&proposal_hash).unwrap();
            votes
                .iter()
                .filter(|v| matches!(v.vote, FallbackVoteDecision::Approve))
                .map(|v| v.voter_weight)
                .sum()
        };
        assert_eq!(approve_weight, 5_000_000_000);
        assert!(approve_weight < q_finality, "5B < 6B, should not finalize");

        // Add more votes to reach threshold
        for i in 5..7 {
            let vote = FallbackVote {
                chain_id: 1,
                proposal_hash,
                vote: FallbackVoteDecision::Approve,
                voter_mn_id: format!("mn_{}", i),
                voter_weight: 1_000_000_000,
                voter_signature: vec![],
            };
            consensus
                .fallback_votes
                .entry(proposal_hash)
                .or_default()
                .push(vote);
        }

        let votes = consensus.fallback_votes.get(&proposal_hash).unwrap();
        let approve_weight: u64 = votes
            .iter()
            .filter(|v| matches!(v.vote, FallbackVoteDecision::Approve))
            .map(|v| v.voter_weight)
            .sum();
        assert_eq!(approve_weight, 7_000_000_000);
        assert!(approve_weight >= q_finality, "7B >= 6B, should finalize");
    }

    /// Test reject decision reaches Q_finality
    #[tokio::test]
    async fn test_phase6_reject_reaches_quorum() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let proposal_hash = [43u8; 32];
        let total_weight = 10_000_000_000u64;
        let q_finality = (total_weight * 2) / 3; // ~6.67B

        // Add 7 Reject votes (7B >= 6.67B)
        for i in 0..7 {
            let vote = FallbackVote {
                chain_id: 1,
                proposal_hash,
                vote: FallbackVoteDecision::Reject,
                voter_mn_id: format!("mn_{}", i),
                voter_weight: 1_000_000_000,
                voter_signature: vec![],
            };
            consensus
                .fallback_votes
                .entry(proposal_hash)
                .or_default()
                .push(vote);
        }

        let votes = consensus.fallback_votes.get(&proposal_hash).unwrap();
        let reject_weight: u64 = votes
            .iter()
            .filter(|v| matches!(v.vote, FallbackVoteDecision::Reject))
            .map(|v| v.voter_weight)
            .sum();
        assert_eq!(reject_weight, 7_000_000_000);
        assert!(
            reject_weight >= q_finality,
            "Reject should reach Q_finality"
        );
    }

    /// Test f+1 alert threshold with different network sizes
    #[tokio::test]
    async fn test_phase6_f_plus_1_various_sizes() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        // Test n=10: f=3, threshold=4
        let txid1 = [1u8; 32];
        for i in 0..4 {
            let alert = LivenessAlert {
                chain_id: 1,
                txid: txid1,
                tx_hash_commitment: [0u8; 32],
                slot_index: 1000,
                poll_history: vec![],
                current_confidence: 5,
                stall_duration_ms: 30000,
                reporter_mn_id: format!("mn_{}", i),
                reporter_signature: vec![],
            };
            consensus
                .liveness_alerts
                .entry(txid1)
                .or_default()
                .push(alert);
        }

        // Verify alert count
        let alerts = consensus.liveness_alerts.get(&txid1).unwrap();
        let unique: std::collections::HashSet<_> =
            alerts.iter().map(|a| &a.reporter_mn_id).collect();
        assert_eq!(unique.len(), 4, "Should have 4 unique reporters");

        // Test n=100: f=33, threshold=34
        let txid2 = [2u8; 32];
        for i in 0..34 {
            let alert = LivenessAlert {
                chain_id: 1,
                txid: txid2,
                tx_hash_commitment: [0u8; 32],
                slot_index: 1000,
                poll_history: vec![],
                current_confidence: 5,
                stall_duration_ms: 30000,
                reporter_mn_id: format!("mn_{}", i),
                reporter_signature: vec![],
            };
            consensus
                .liveness_alerts
                .entry(txid2)
                .or_default()
                .push(alert);
        }

        let alerts = consensus.liveness_alerts.get(&txid2).unwrap();
        let unique: std::collections::HashSet<_> =
            alerts.iter().map(|a| &a.reporter_mn_id).collect();
        assert_eq!(unique.len(), 34, "Should have 34 unique reporters");
    }

    /// Test mixed Approve/Reject votes
    #[tokio::test]
    async fn test_phase6_mixed_votes() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        let proposal_hash = [44u8; 32];

        // Add 4 Approve votes
        for i in 0..4 {
            let vote = FallbackVote {
                chain_id: 1,
                proposal_hash,
                vote: FallbackVoteDecision::Approve,
                voter_mn_id: format!("mn_approve_{}", i),
                voter_weight: 1_000_000_000,
                voter_signature: vec![],
            };
            consensus
                .fallback_votes
                .entry(proposal_hash)
                .or_default()
                .push(vote);
        }

        // Add 3 Reject votes
        for i in 0..3 {
            let vote = FallbackVote {
                chain_id: 1,
                proposal_hash,
                vote: FallbackVoteDecision::Reject,
                voter_mn_id: format!("mn_reject_{}", i),
                voter_weight: 1_000_000_000,
                voter_signature: vec![],
            };
            consensus
                .fallback_votes
                .entry(proposal_hash)
                .or_default()
                .push(vote);
        }

        // Check status
        let votes = consensus.fallback_votes.get(&proposal_hash).unwrap();
        assert_eq!(votes.len(), 7);

        let approve_weight: u64 = votes
            .iter()
            .filter(|v| matches!(v.vote, FallbackVoteDecision::Approve))
            .map(|v| v.voter_weight)
            .sum();
        let reject_weight: u64 = votes
            .iter()
            .filter(|v| matches!(v.vote, FallbackVoteDecision::Reject))
            .map(|v| v.voter_weight)
            .sum();

        assert_eq!(approve_weight, 4_000_000_000);
        assert_eq!(reject_weight, 3_000_000_000);
    }

    /// Test Byzantine detection via internal tracking
    #[tokio::test]
    async fn test_phase6_byzantine_tracking() {
        let config = TimeVoteConfig::default();
        let registry = create_test_registry();
        let consensus = TimeVoteConsensus::new(config, registry).unwrap();

        // Direct access to internal byzantine_nodes map
        assert_eq!(consensus.byzantine_nodes.len(), 0);

        // Flag a node
        consensus.byzantine_nodes.insert("mn_bad".to_string(), true);

        // Verify tracking
        assert_eq!(consensus.byzantine_nodes.len(), 1);
        assert!(*consensus.byzantine_nodes.get("mn_bad").unwrap().value());
    }
}
