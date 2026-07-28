//! Peer Connection Management
//! Handles individual peer connections and message routing.

#![allow(dead_code)]

use std::sync::Arc;
use std::time::Duration;
use tokio::net::TcpStream;
use tokio::sync::RwLock;
use tokio::time::{interval, Instant};
use tracing::{debug, error, info, warn};

use crate::blockchain::Blockchain;
use crate::network::banlist::IPBanlist;
use crate::network::message::NetworkMessage;
use crate::network::message_handler::{ConnectionDirection, MessageContext, MessageHandler};
use crate::network::tls::TlsConfig;
use std::collections::HashMap;

/// State for tracking ping/pong health
#[derive(Debug)]
pub struct PingState {
    last_ping_sent: Option<Instant>,
    last_pong_received: Option<Instant>,
    pending_pings: Vec<(u64, Instant)>, // (nonce, sent_time)
    missed_pongs: u32,
    pub last_rtt_ms: Option<f64>, // Latest one-way latency in milliseconds (RTT/2)
}

// Circuit breaker limits for fork resolution
const FORK_RESOLUTION_TIMEOUT_SECS: u64 = 60; // 60 seconds - fast fork resolution
const CRITICAL_FORK_DEPTH: u64 = 100; // Log warning if fork > 100 blocks (but don't stop)
const PROGRESS_LOG_INTERVAL: u32 = 10; // Log progress every 10 attempts

/// Fork resolution attempt tracker with enhanced circuit breaker
#[derive(Debug, Clone)]
struct ForkResolutionAttempt {
    fork_height: u64,
    attempt_count: u32,
    last_attempt: std::time::Instant,
    common_ancestor: Option<u64>,
    peer_height: u64,
    max_depth_searched: u64, // Track deepest search to prevent infinite loops
}

impl ForkResolutionAttempt {
    fn new(fork_height: u64, peer_height: u64) -> Self {
        Self {
            fork_height,
            attempt_count: 1,
            last_attempt: std::time::Instant::now(),
            common_ancestor: None,
            peer_height,
            max_depth_searched: 0,
        }
    }

    fn is_same_fork(&self, fork_height: u64, peer_height: u64) -> bool {
        // Consider it the same fork if heights are within 10 blocks
        (self.fork_height as i64 - fork_height as i64).abs() <= 10
            && (self.peer_height as i64 - peer_height as i64).abs() <= 10
    }

    fn should_give_up(&self) -> bool {
        let elapsed = self.last_attempt.elapsed();

        // Only give up on timeout - no attempt or depth limits
        if elapsed.as_secs() > FORK_RESOLUTION_TIMEOUT_SECS {
            tracing::error!(
                "🚨 Fork resolution timeout: {} seconds exceeded (attempt {}, depth {})",
                FORK_RESOLUTION_TIMEOUT_SECS,
                self.attempt_count,
                self.max_depth_searched
            );
            return true;
        }

        // Log progress periodically to show we're still working
        if self.attempt_count % PROGRESS_LOG_INTERVAL == 0 {
            tracing::warn!(
                "🔄 Fork resolution in progress: attempt {}, searched {} blocks back, fork at height {}",
                self.attempt_count,
                self.max_depth_searched,
                self.fork_height
            );
        }

        // Warn if fork is very deep but keep going
        if self.max_depth_searched > CRITICAL_FORK_DEPTH && self.max_depth_searched % 100 == 0 {
            tracing::warn!(
                "⚠️ Deep fork: searched {} blocks back - this may take a while",
                self.max_depth_searched
            );
        }

        false
    }

    fn update_depth(&mut self, current_height: u64, search_height: u64) {
        let depth = current_height.saturating_sub(search_height);
        if depth > self.max_depth_searched {
            self.max_depth_searched = depth;

            // Log warning for deep forks
            if depth > CRITICAL_FORK_DEPTH {
                tracing::warn!(
                    "⚠️  Deep fork detected: {} blocks back (critical threshold: {})",
                    depth,
                    CRITICAL_FORK_DEPTH
                );
            }
        }
    }

    fn increment(&mut self) {
        self.attempt_count += 1;
        self.last_attempt = std::time::Instant::now();
    }
}

impl PingState {
    fn new() -> Self {
        Self {
            last_ping_sent: None,
            last_pong_received: None,
            pending_pings: Vec::new(),
            missed_pongs: 0,
            last_rtt_ms: None,
        }
    }

    fn record_ping_sent(&mut self, nonce: u64) {
        let now = Instant::now();
        self.last_ping_sent = Some(now);

        // Hard limit to prevent memory exhaustion on high packet-loss networks
        const MAX_PENDING_PINGS: usize = 100;
        if self.pending_pings.len() >= MAX_PENDING_PINGS {
            // Remove oldest 50% when limit reached
            self.pending_pings.drain(0..50);
            tracing::warn!(
                "Pending pings exceeded {}, cleared old entries",
                MAX_PENDING_PINGS
            );
        }

        self.pending_pings.push((nonce, now));

        // Remove pings that have already timed out (older than 120 seconds)
        // Increased timeout for high-latency satellite/mobile connections
        const TIMEOUT: Duration = Duration::from_secs(120);
        self.pending_pings
            .retain(|(_, sent_time)| now.duration_since(*sent_time) <= TIMEOUT);
    }

    fn record_pong_received(&mut self, nonce: u64) -> bool {
        let now = Instant::now();
        self.last_pong_received = Some(now);

        // Find and remove the matching ping, calculating one-way latency
        if let Some(pos) = self.pending_pings.iter().position(|(n, _)| *n == nonce) {
            let (_nonce, sent_time) = self.pending_pings.remove(pos);

            // Calculate round-trip time and divide by 2 for one-way latency
            let rtt = now.duration_since(sent_time);
            self.last_rtt_ms = Some(rtt.as_secs_f64() * 1000.0 / 2.0);

            self.missed_pongs = 0; // Reset counter on successful pong
            true
        } else {
            debug!(
                "🔀 Received pong for unknown nonce: {} (likely duplicate connection)",
                nonce
            );
            false
        }
    }

    fn check_timeout(&mut self, max_missed: u32, timeout_duration: Duration) -> bool {
        let now = Instant::now();

        // Check for expired pings
        let mut expired_count = 0;
        self.pending_pings.retain(|(_, sent_time)| {
            if now.duration_since(*sent_time) > timeout_duration {
                expired_count += 1;
                false
            } else {
                true
            }
        });

        if expired_count > 0 {
            self.missed_pongs += expired_count;
            debug!(
                "⏰ {} ping(s) expired, total missed: {}/{}",
                expired_count, self.missed_pongs, max_missed
            );
        }

        self.missed_pongs >= max_missed
    }
}

/// Unified peer connection handling both inbound and outbound connections
pub struct PeerConnection {
    /// Peer's IP address (identity)
    peer_ip: String,

    /// Connection direction
    direction: ConnectionDirection,

    /// Channel receiver for incoming parsed messages (from I/O bridge task)
    msg_reader: tokio::sync::mpsc::UnboundedReceiver<Result<Option<NetworkMessage>, String>>,

    /// Channel sender for outgoing serialized frame bytes (to I/O bridge task)
    writer_tx: crate::network::peer_connection_registry::PeerWriterTx,

    /// Ping/pong state
    ping_state: Arc<RwLock<PingState>>,

    /// Invalid/skipped block counter (for fork detection)
    invalid_block_count: Arc<RwLock<u32>>,

    /// Local listening port (for logging)
    #[allow(dead_code)]
    local_port: u16,

    /// Remote port for this connection (ephemeral)
    remote_port: u16,

    /// Last known height of the peer (for fork resolution)
    peer_height: Arc<RwLock<Option<u64>>>,

    /// Fork resolution attempt tracker
    fork_resolution_tracker: Arc<RwLock<Option<ForkResolutionAttempt>>>,

    /// Last opportunistic sync request time (for throttling)
    last_opportunistic_sync: Arc<RwLock<Option<Instant>>>,

    /// Whitelist status - whitelisted masternodes get relaxed ping/pong timeouts
    is_whitelisted: bool,

    /// Network type (mainnet/testnet) for handshake
    network_type: crate::network_type::NetworkType,

    /// Per-TX UTXOStateUpdate (Locked) count for AV10 flood detection
    peer_tx_lock_counts: HashMap<[u8; 32], u32>,

    /// Consecutive excess-ping count for AV27 rate-limit detection
    ping_excess_streak: u32,
}

/// Configuration for peer connection message loop
/// Supports optional components for different connection scenarios
pub struct MessageLoopConfig {
    /// Required: Peer registry for tracking active connections
    pub peer_registry: Arc<crate::network::peer_connection_registry::PeerConnectionRegistry>,

    /// Optional: Masternode registry for masternode-specific handling
    pub masternode_registry: Option<Arc<crate::masternode_registry::MasternodeRegistry>>,

    /// Optional: Blockchain for block synchronization and validation
    pub blockchain: Option<Arc<Blockchain>>,

    /// Optional: Broadcast receiver for forwarding gossip and other broadcasts
    pub broadcast_rx:
        Option<tokio::sync::broadcast::Receiver<crate::network::message::NetworkMessage>>,

    /// Optional: Banlist for rejecting messages from banned peers
    pub banlist: Option<Arc<RwLock<IPBanlist>>>,

    /// Optional: AI System for recording events and making intelligent decisions
    pub ai_system: Option<Arc<crate::ai::AISystem>>,

    /// Optional: Per-connection rate limiter — mirrors the inbound check_rate_limit! macro
    pub rate_limiter: Option<Arc<RwLock<crate::network::rate_limiter::RateLimiter>>>,
    /// Optional: Relay store for Silver/Gold message relay nodes
    pub relay_store: Option<Arc<crate::messaging::relay::RelayStore>>,
    /// Optional: Signing key for relay operations (storage acks, delivery events)
    pub relay_signing_key: Option<Arc<ed25519_dalek::SigningKey>>,
    /// Optional: Contacts book for persistent pubkey lookups across restarts
    pub contacts_book: Option<Arc<crate::messaging::contacts::ContactsBook>>,
}

impl MessageLoopConfig {
    /// Create a new config with just peer registry (minimal setup)
    pub fn new(
        peer_registry: Arc<crate::network::peer_connection_registry::PeerConnectionRegistry>,
    ) -> Self {
        Self {
            peer_registry,
            masternode_registry: None,
            blockchain: None,
            broadcast_rx: None,
            banlist: None,
            ai_system: None,
            rate_limiter: None,
            relay_store: None,
            relay_signing_key: None,
            contacts_book: None,
        }
    }

    /// Add relay store and signing key for Silver/Gold messaging relay (builder pattern)
    pub fn with_relay_store(
        mut self,
        relay_store: Arc<crate::messaging::relay::RelayStore>,
        signing_key: Arc<ed25519_dalek::SigningKey>,
    ) -> Self {
        self.relay_store = Some(relay_store);
        self.relay_signing_key = Some(signing_key);
        self
    }

    /// Add contacts book for persistent pubkey lookups (builder pattern)
    pub fn with_contacts_book(
        mut self,
        contacts_book: Arc<crate::messaging::contacts::ContactsBook>,
    ) -> Self {
        self.contacts_book = Some(contacts_book);
        self
    }

    /// Add masternode registry (builder pattern)
    pub fn with_masternode_registry(
        mut self,
        registry: Arc<crate::masternode_registry::MasternodeRegistry>,
    ) -> Self {
        self.masternode_registry = Some(registry);
        self
    }

    /// Add blockchain (builder pattern)
    pub fn with_blockchain(mut self, blockchain: Arc<Blockchain>) -> Self {
        self.blockchain = Some(blockchain);
        self
    }

    /// Add broadcast receiver (builder pattern)
    pub fn with_broadcast_rx(
        mut self,
        rx: tokio::sync::broadcast::Receiver<crate::network::message::NetworkMessage>,
    ) -> Self {
        self.broadcast_rx = Some(rx);
        self
    }

    /// Add banlist (builder pattern)
    pub fn with_banlist(mut self, banlist: Arc<RwLock<IPBanlist>>) -> Self {
        self.banlist = Some(banlist);
        self
    }

    /// Add AI system (builder pattern)
    pub fn with_ai_system(mut self, ai_system: Arc<crate::ai::AISystem>) -> Self {
        self.ai_system = Some(ai_system);
        self
    }

    /// Add per-connection rate limiter (builder pattern)
    pub fn with_rate_limiter(
        mut self,
        rl: Arc<RwLock<crate::network::rate_limiter::RateLimiter>>,
    ) -> Self {
        self.rate_limiter = Some(rl);
        self
    }
}

/// Map a `NetworkMessage` to the rate-limit bucket name used in both the inbound
/// `check_rate_limit!` macro (server.rs) and the outbound path (handle_message_unified).
fn rate_limit_key(msg: &NetworkMessage) -> &'static str {
    match msg {
        NetworkMessage::TransactionBroadcast(_) => "tx",
        NetworkMessage::TransactionFinalized { .. } => "tx_finalized",
        NetworkMessage::GetBlocks(..) => "get_blocks",
        NetworkMessage::GetPeers => "get_peers",
        NetworkMessage::GetMasternodes => "get_masternodes",
        NetworkMessage::MasternodesResponse(_) => "masternodes_response",
        NetworkMessage::MasternodeAnnouncement { .. }
        | NetworkMessage::MasternodeAnnouncementV2 { .. }
        | NetworkMessage::MasternodeAnnouncementV3 { .. }
        | NetworkMessage::MasternodeAnnouncementV4 { .. } => "masternode_announce",
        NetworkMessage::BlockAnnouncement(_)
        | NetworkMessage::BlockResponse(_)
        | NetworkMessage::TimeLockBlockProposal { .. } => "block",
        NetworkMessage::TimeVoteRequest { .. }
        | NetworkMessage::TimeVoteResponse { .. }
        | NetworkMessage::TimeVoteBroadcast { .. }
        | NetworkMessage::TimeVotePrepare { .. }
        | NetworkMessage::TimeVotePrecommit { .. }
        | NetworkMessage::TransactionVoteRequest { .. }
        | NetworkMessage::TransactionVoteResponse { .. }
        | NetworkMessage::FinalityVoteRequest { .. }
        | NetworkMessage::FinalityVoteResponse { .. }
        | NetworkMessage::FinalityVoteBroadcast { .. } => "vote",
        // Bulk sync responses arrive in bursts by design; give them a dedicated
        // high-limit bucket so they don't saturate the 100/s "general" limit.
        NetworkMessage::BlocksResponse(_)
        | NetworkMessage::BlockRangeResponse(_)
        | NetworkMessage::UTXOSetResponse(_)
        | NetworkMessage::UTXOSetChunk { .. }
        | NetworkMessage::UtxoReconciliationResponse { .. }
        | NetworkMessage::UtxoReconciliationChunk { .. } => "sync",
        _ => "general",
    }
}

impl PeerConnection {
    const PING_INTERVAL: Duration = Duration::from_secs(30);
    const TIMEOUT_CHECK_INTERVAL: Duration = Duration::from_secs(10);
    const PONG_TIMEOUT: Duration = Duration::from_secs(300); // 5 minutes - very generous
    const MAX_MISSED_PONGS: u32 = 10; // Allow many missed pongs before disconnect

    // Phase 1: Relaxed timeouts for whitelisted masternodes
    const WHITELISTED_PONG_TIMEOUT: Duration = Duration::from_secs(600); // 10 minutes
    const WHITELISTED_MAX_MISSED_PONGS: u32 = 20; // Allow even more missed pongs

    /// Create a new outbound connection to a peer
    pub async fn new_outbound(
        peer_ip: String,
        port: u16,
        is_whitelisted: bool,
        tls_config: Option<Arc<TlsConfig>>,
        network_type: crate::network_type::NetworkType,
    ) -> Result<Self, String> {
        let addr = format!("{}:{}", peer_ip, port);

        if is_whitelisted {
            debug!("🔗 [OUTBOUND-WHITELIST] Connecting to masternode {}", addr);
        } else {
            debug!("🔗 [OUTBOUND] Connecting to {}", addr);
        }

        let stream = tokio::time::timeout(
            std::time::Duration::from_secs(10),
            TcpStream::connect(&addr),
        )
        .await
        .map_err(|_| format!("Connection to {} timed out (10s)", addr))?
        .map_err(|e| format!("Failed to connect to {}: {}", addr, e))?;

        let remote_addr = stream
            .peer_addr()
            .map_err(|e| format!("Failed to get peer address: {}", e))?;

        let local_addr = stream
            .local_addr()
            .map_err(|e| format!("Failed to get local address: {}", e))?;

        // Create channel-based I/O to avoid tokio::io::split() on TLS streams
        let (msg_read_tx, msg_read_rx) =
            tokio::sync::mpsc::unbounded_channel::<Result<Option<NetworkMessage>, String>>();
        let (write_tx, mut write_rx) = tokio::sync::mpsc::unbounded_channel::<Vec<u8>>();

        if let Some(tls) = tls_config {
            debug!("🔒 [OUTBOUND] TLS handshake with {}", addr);
            let tls_stream = tls
                .connect_client(stream, "timecoin.local")
                .await
                .map_err(|e| {
                    tracing::warn!("🚫 TLS handshake failed with {}: {}", addr, e);
                    format!("TLS handshake failed with {}: {}", addr, e)
                })?;
            let peer_addr = addr.clone();
            // Split into dedicated reader and writer tasks.
            // The old single-task select!(read_message, write_rx.recv()) bridge was
            // NOT cancellation-safe: tokio::select! cancels the losing future, and
            // read_exact (used inside read_message) is NOT cancellation-safe.  When a
            // write became ready while read_message was mid-frame, the select! would
            // drop the read future after consuming some bytes, leaving the stream at an
            // inconsistent offset.  The next read_message then read payload bytes as a
            // frame-length prefix, producing the 100 MB–3 GB "FrameBomb" sizes seen
            // in production.  Dedicated tasks (same as plaintext path below) eliminate
            // the hazard.  tokio::io::split() is safe here: rustls uses TLS 1.3
            // exclusively — no renegotiation, no cross-direction TLS I/O post-handshake.
            let (mut tls_read, mut tls_write) = tokio::io::split(tls_stream);
            let peer_addr_r = peer_addr.clone();
            // Dedicated reader task — reads continuously without competing with writes.
            tokio::spawn(async move {
                loop {
                    let result = crate::network::wire::read_message(&mut tls_read).await;
                    let is_eof = matches!(&result, Ok(None));
                    let is_err = result.is_err();
                    if msg_read_tx.send(result).is_err() {
                        break;
                    }
                    if is_eof || is_err {
                        break;
                    }
                }
                tracing::debug!("🔒 TLS reader task exiting for {}", peer_addr_r);
            });
            // Dedicated writer task.
            tokio::spawn(async move {
                use tokio::io::AsyncWriteExt;
                while let Some(data) = write_rx.recv().await {
                    if let Err(e) = tls_write.write_all(&data).await {
                        tracing::debug!("🔒 TLS write error for {}: {}", peer_addr, e);
                        break;
                    }
                    if let Err(e) = tls_write.flush().await {
                        tracing::debug!("🔒 TLS flush error for {}: {}", peer_addr, e);
                        break;
                    }
                }
                tracing::debug!("🔒 TLS writer task exiting for {}", peer_addr);
            });
        } else {
            let (r, w) = stream.into_split();
            let peer_addr = addr.clone();
            // Spawn reader task
            tokio::spawn(async move {
                let mut reader = r;
                loop {
                    let result = crate::network::wire::read_message(&mut reader).await;
                    let is_eof = matches!(&result, Ok(None));
                    let is_err = result.is_err();
                    if msg_read_tx.send(result).is_err() {
                        break;
                    }
                    if is_eof || is_err {
                        break;
                    }
                }
                tracing::debug!("📖 Reader task exiting for {}", peer_addr);
            });
            // Spawn writer task
            let peer_addr2 = addr.clone();
            tokio::spawn(async move {
                use tokio::io::AsyncWriteExt;
                let mut writer = w;
                while let Some(data) = write_rx.recv().await {
                    if let Err(e) = writer.write_all(&data).await {
                        tracing::debug!("📝 Write error for {}: {}", peer_addr2, e);
                        break;
                    }
                    if let Err(e) = writer.flush().await {
                        tracing::debug!("📝 Flush error for {}: {}", peer_addr2, e);
                        break;
                    }
                }
                tracing::debug!("📝 Writer task exiting for {}", peer_addr2);
            });
        }

        Ok(Self {
            peer_ip,
            direction: ConnectionDirection::Outbound,
            msg_reader: msg_read_rx,
            writer_tx: write_tx,
            ping_state: Arc::new(RwLock::new(PingState::new())),
            invalid_block_count: Arc::new(RwLock::new(0)),
            peer_height: Arc::new(RwLock::new(None)),
            fork_resolution_tracker: Arc::new(RwLock::new(None)),
            last_opportunistic_sync: Arc::new(RwLock::new(None)),
            local_port: local_addr.port(),
            remote_port: remote_addr.port(),
            is_whitelisted,
            network_type,
            peer_tx_lock_counts: HashMap::new(),
            ping_excess_streak: 0,
        })
    }

    /// Create a new inbound connection from an already-established channel pair.
    ///
    /// `drive_inbound` handles TLS/plaintext I/O setup, pre-handshake loop,
    /// and peer registration before calling this.  This constructor receives the
    /// ready channel pair so `run_message_loop_unified` can take over immediately.
    #[allow(dead_code)]
    pub fn new_inbound(
        peer_ip: String,
        remote_port: u16,
        local_port: u16,
        is_whitelisted: bool,
        network_type: crate::network_type::NetworkType,
        writer_tx: crate::network::peer_connection_registry::PeerWriterTx,
        msg_reader: tokio::sync::mpsc::UnboundedReceiver<Result<Option<NetworkMessage>, String>>,
    ) -> Result<Self, String> {
        Ok(Self {
            peer_ip,
            direction: ConnectionDirection::Inbound,
            msg_reader,
            writer_tx,
            ping_state: Arc::new(RwLock::new(PingState::new())),
            invalid_block_count: Arc::new(RwLock::new(0)),
            peer_height: Arc::new(RwLock::new(None)),
            fork_resolution_tracker: Arc::new(RwLock::new(None)),
            last_opportunistic_sync: Arc::new(RwLock::new(None)),
            local_port,
            remote_port,
            is_whitelisted,
            network_type,
            peer_tx_lock_counts: HashMap::new(),
            ping_excess_streak: 0,
        })
    }

    /// Get peer IP (identity)
    pub fn peer_ip(&self) -> &str {
        &self.peer_ip
    }

    /// Get connection direction
    #[allow(dead_code)]
    pub fn direction(&self) -> ConnectionDirection {
        self.direction
    }

    /// Get remote port for this connection
    #[allow(dead_code)]
    pub fn remote_port(&self) -> u16 {
        self.remote_port
    }

    /// Get peer's reported blockchain height
    pub async fn get_peer_height(&self) -> Option<u64> {
        *self.peer_height.read().await
    }

    /// Get the latest ping RTT in seconds (for RPC)
    pub async fn get_ping_rtt(&self) -> Option<f64> {
        let state = self.ping_state.read().await;
        state.last_rtt_ms.map(|ms| ms / 1000.0) // Convert ms to seconds
    }

    /// Get the writer channel sender for registration in peer registry
    pub fn shared_writer(&self) -> crate::network::peer_connection_registry::SharedPeerWriter {
        self.writer_tx.clone()
    }

    /// Send a message via the write channel
    fn send_message(
        writer_tx: &crate::network::peer_connection_registry::PeerWriterTx,
        message: &NetworkMessage,
    ) -> Result<(), String> {
        let frame_bytes = crate::network::wire::serialize_frame(message)?;
        writer_tx
            .send(frame_bytes)
            .map_err(|_| "Writer channel closed".to_string())
    }

    /// Send a ping to the peer. Returns the nonce on success for RTT tracking.
    async fn send_ping(&mut self, blockchain: Option<&Arc<Blockchain>>) -> Result<u64, String> {
        let nonce = rand::random::<u64>();
        let timestamp = chrono::Utc::now().timestamp();
        let height = blockchain.map(|bc| bc.get_height());
        let direction = self.direction;
        let peer_ip = self.peer_ip.clone();

        {
            let mut state = self.ping_state.write().await;
            state.record_ping_sent(nonce);
        }

        let height_info = height
            .map(|h| format!(" at height {}", h))
            .unwrap_or_default();
        debug!(
            "📤 [{:?}] Sent ping to {}{} (nonce: {})",
            direction, peer_ip, height_info, nonce
        );

        Self::send_message(
            &self.writer_tx,
            &NetworkMessage::Ping {
                nonce,
                timestamp,
                height,
            },
        )?;
        Ok(nonce)
    }

    /// Handle received ping
    async fn handle_ping(
        &mut self,
        nonce: u64,
        _timestamp: i64,
        peer_height: Option<u64>,
        our_height: Option<u64>,
    ) -> Result<(), String> {
        // Phase 3: Log peer height from ping
        let height_info = peer_height
            .map(|h| format!(" at height {}", h))
            .unwrap_or_default();
        info!(
            "📨 [{:?}] Received ping from {}{}  (nonce: {})",
            self.direction, self.peer_ip, height_info, nonce
        );

        // Phase 3: Update peer height if provided
        if let Some(height) = peer_height {
            *self.peer_height.write().await = Some(height);
        }

        let timestamp = chrono::Utc::now().timestamp();
        // Phase 3: Include our height in pong response
        Self::send_message(
            &self.writer_tx,
            &NetworkMessage::Pong {
                nonce,
                timestamp,
                height: our_height,
            },
        )?;

        info!(
            "✅ [{:?}] Sent pong to {} (nonce: {})",
            self.direction, self.peer_ip, nonce
        );

        Ok(())
    }

    /// Handle received pong
    async fn handle_pong(
        &mut self,
        nonce: u64,
        _timestamp: i64,
        peer_height: Option<u64>,
    ) -> Result<(), String> {
        // Phase 3: Log peer height from pong
        let height_info = peer_height
            .map(|h| format!(" at height {}", h))
            .unwrap_or_default();
        debug!(
            "📨 [{:?}] Received pong from {}{}  (nonce: {})",
            self.direction, self.peer_ip, height_info, nonce
        );

        // Phase 3: Update peer height if provided
        if let Some(height) = peer_height {
            *self.peer_height.write().await = Some(height);
        }

        let mut state = self.ping_state.write().await;

        debug!(
            "📊 [{:?}] Before pong: {} pending pings, {} missed",
            self.direction,
            state.pending_pings.len(),
            state.missed_pongs
        );

        if state.record_pong_received(nonce) {
            debug!(
                "✅ [{:?}] Pong MATCHED for {} (nonce: {}), {} pending pings remain",
                self.direction,
                self.peer_ip,
                nonce,
                state.pending_pings.len()
            );
            Ok(())
        } else {
            // Check if this could be from a duplicate connection
            // If we have no pending pings at all, this is likely from another connection instance
            if state.pending_pings.is_empty() {
                debug!(
                    "🔀 [{:?}] Received pong from {} (nonce: {}) but no pending pings - likely duplicate connection or peer bug",
                    self.direction,
                    self.peer_ip,
                    nonce
                );
            } else {
                // If we have pending pings but wrong nonce, could be cross-connection mixing
                // This happens when both inbound and outbound connections exist to same peer
                debug!(
                    "🔀 [{:?}] Pong nonce mismatch from {} (got: {}, expected one of: {:?}) - possibly duplicate connection",
                    self.direction,
                    self.peer_ip,
                    nonce,
                    state
                        .pending_pings
                        .iter()
                        .map(|(n, _)| n)
                        .collect::<Vec<_>>()
                );
            }
            Ok(())
        }
    }

    /// Check if other peers agree with fork from this peer (lightweight consensus)
    /// Returns the number of peers that agree (are within 10 blocks of fork height)
    async fn check_fork_agreement(
        &self,
        peer_registry: &Arc<crate::network::peer_connection_registry::PeerConnectionRegistry>,
        fork_height: u64,
        exclude_peer: &str,
    ) -> Result<usize, String> {
        let connected_peers = peer_registry.get_connected_peers().await;

        if connected_peers.len() < 2 {
            // Not enough peers to check consensus
            return Ok(0);
        }

        let mut agreement_count = 0;

        for peer_ip in &connected_peers {
            if peer_ip == exclude_peer {
                continue; // Skip the peer we're checking
            }

            if let Some(peer_height) = peer_registry.get_peer_height(peer_ip).await {
                // Peer agrees if within 10 blocks of fork height
                if (peer_height as i64 - fork_height as i64).abs() <= 10 {
                    agreement_count += 1;
                    debug!(
                        "Peer {} agrees with fork (height {} vs fork {})",
                        peer_ip, peer_height, fork_height
                    );
                }
            }
        }

        Ok(agreement_count)
    }

    /// Check if connection should be closed due to timeout
    async fn should_disconnect(
        &mut self,
        _peer_registry: &crate::network::peer_connection_registry::PeerConnectionRegistry,
    ) -> bool {
        // CRITICAL FIX: Whitelisted masternodes should NEVER be disconnected due to timeout
        // They are essential network infrastructure and must maintain persistent connections
        if self.is_whitelisted {
            let state = self.ping_state.read().await;
            // Log warning for monitoring but DO NOT disconnect
            if state.missed_pongs > Self::WHITELISTED_MAX_MISSED_PONGS {
                warn!(
                    "⚠️ [{:?}] Whitelisted masternode {} has {} missed pongs (NOT disconnecting - protected)",
                    self.direction, self.peer_ip, state.missed_pongs
                );
            }
            return false; // ✅ FIX: Never disconnect whitelisted nodes
        }

        // Non-whitelisted peers: Use normal timeout logic
        let mut state = self.ping_state.write().await;
        if state.check_timeout(Self::MAX_MISSED_PONGS, Self::PONG_TIMEOUT) {
            warn!(
                "❌ [{:?}] Disconnecting non-whitelisted peer {} after {} missed pongs",
                self.direction, self.peer_ip, state.missed_pongs
            );
            true
        } else {
            false
        }
    }

    /// Unified message handler that delegates to MessageHandler
    /// This replaces the old handle_message_with_* functions
    async fn handle_message_unified(
        &mut self,
        message: NetworkMessage,
        config: &MessageLoopConfig,
        handler: &MessageHandler,
    ) -> Result<(), String> {
        // Handle connection-level messages that need special state management
        match &message {
            NetworkMessage::Ping {
                nonce,
                timestamp,
                height,
            } => {
                let our_height = config.blockchain.as_ref().map(|bc| bc.get_height());
                return self
                    .handle_ping(*nonce, *timestamp, *height, our_height)
                    .await;
            }
            NetworkMessage::Pong {
                nonce,
                timestamp,
                height,
            } => {
                self.handle_pong(*nonce, *timestamp, *height).await?;
                // Push RTT to registry via both paths for reliability
                config
                    .peer_registry
                    .record_pong_received(&self.peer_ip, *nonce)
                    .await;
                if let Some(rtt_secs) = self.get_ping_rtt().await {
                    config
                        .peer_registry
                        .set_peer_ping_time(&self.peer_ip, rtt_secs)
                        .await;
                }
                return Ok(());
            }
            NetworkMessage::Handshake { commit_count, .. } => {
                // Check if the peer is running newer software than us.
                let our_commits = env!("GIT_COMMIT_COUNT").parse::<u32>().unwrap_or(0);
                if *commit_count > our_commits && our_commits > 0 {
                    warn!(
                        "⬆️  [{:?}] Peer {} is running newer software (commit {}, we are at {}). \
                        Consider upgrading: https://github.com/time-coin/time-masternode",
                        self.direction, self.peer_ip, commit_count, our_commits
                    );
                }
                return Ok(());
            }
            NetworkMessage::Version { commit_count, .. } => {
                let our_commits = env!("GIT_COMMIT_COUNT").parse::<u32>().unwrap_or(0);
                let peer_commits = commit_count.parse::<u32>().unwrap_or(0);
                if peer_commits > our_commits && our_commits > 0 {
                    warn!(
                        "⬆️  [{:?}] Peer {} is running newer software (commit {}, we are at {}). \
                        Consider upgrading: https://github.com/time-coin/time-masternode",
                        self.direction, self.peer_ip, peer_commits, our_commits
                    );
                }
                return Ok(());
            }
            NetworkMessage::Ack { .. } => {
                debug!(
                    "📨 [{:?}] Received Ack from {}",
                    self.direction, self.peer_ip
                );
                return Ok(());
            }
            _ => {
                // All other messages go through MessageHandler
            }
        }

        // Apply per-connection rate limiting — mirrors the inbound check_rate_limit! macro.
        if let Some(ref rl) = config.rate_limiter {
            let mut limiter = rl.write().await;
            if !limiter.check(rate_limit_key(&message), &self.peer_ip) {
                tracing::warn!(
                    "⚠️ [{:?}] Rate limit exceeded for {} from {}",
                    self.direction,
                    rate_limit_key(&message),
                    self.peer_ip
                );
                return Ok(());
            }
        }

        // Build context for MessageHandler
        let context = if let Some(ref blockchain) = config.blockchain {
            let masternode_registry = config
                .masternode_registry
                .as_ref()
                .expect("Masternode registry required when blockchain is provided");

            // Use from_registry to automatically fetch consensus engine
            let mut ctx = MessageContext::from_registry(
                Arc::clone(blockchain),
                Arc::clone(&config.peer_registry),
                Arc::clone(masternode_registry),
            )
            .await;

            // Add banlist if available
            if let Some(ref banlist) = config.banlist {
                ctx = ctx.with_banlist(Arc::clone(banlist));
            }

            // Add AI system if available
            if let Some(ref ai_system) = config.ai_system {
                ctx = ctx.with_ai_system(Arc::clone(ai_system));
            }

            // Add relay store if available (Silver/Gold nodes)
            if let (Some(ref relay_store), Some(ref relay_key)) =
                (&config.relay_store, &config.relay_signing_key)
            {
                ctx = ctx.with_relay_store(Arc::clone(relay_store), Arc::clone(relay_key));
            }

            // Add contacts book if available
            if let Some(ref cb) = config.contacts_book {
                ctx = ctx.with_contacts_book(Arc::clone(cb));
            }

            ctx
        } else if let Some(ref _masternode_registry) = config.masternode_registry {
            // This case should not happen in practice - we always have blockchain when we have masternode_registry
            return Err("Cannot create context without blockchain".to_string());
        } else {
            return Err("Cannot create context without masternode registry".to_string());
        };

        // Delegate to MessageHandler
        match handler.handle_message(&message, &context).await {
            Ok(Some(response)) => {
                // Send response if MessageHandler returned one
                if let Err(e) = Self::send_message(&self.writer_tx, &response) {
                    warn!(
                        "⚠️ [{:?}] Failed to send response to {}: {}",
                        self.direction, self.peer_ip, e
                    );
                }
                Ok(())
            }
            Ok(None) => {
                // Message handled successfully, no response needed
                Ok(())
            }
            Err(e) => {
                if e.contains("is banned") {
                    // Banned peer — signal the message loop to disconnect
                    return Err(e);
                }
                debug!(
                    "⚠️ [{:?}] MessageHandler error for {} (may be normal): {}",
                    self.direction, self.peer_ip, e
                );
                Ok(()) // Don't propagate handler errors as connection errors
            }
        }
    }

    /// Unified message loop that works with any combination of components
    ///
    /// This replaces the 4 separate run_message_loop variants with a single
    /// flexible implementation using the builder pattern.
    ///
    /// # Example
    /// ```ignore
    /// // Basic setup (peer registry only)
    /// let config = MessageLoopConfig::new(peer_registry);
    /// peer_connection.run_message_loop_unified(config).await?;
    ///
    /// // With masternode registry
    /// let config = MessageLoopConfig::new(peer_registry)
    ///     .with_masternode_registry(masternode_registry);
    /// peer_connection.run_message_loop_unified(config).await?;
    ///
    /// // Full setup
    /// let config = MessageLoopConfig::new(peer_registry)
    ///     .with_masternode_registry(masternode_registry)
    ///     .with_blockchain(blockchain);
    /// peer_connection.run_message_loop_unified(config).await?;
    /// ```
    pub async fn run_message_loop_unified(
        mut self,
        mut config: MessageLoopConfig,
    ) -> Result<(), String> {
        let mut ping_interval = interval(Self::PING_INTERVAL);
        ping_interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        let mut timeout_check = interval(Self::TIMEOUT_CHECK_INTERVAL);
        timeout_check.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

        info!(
            "🔄 [{:?}] Starting unified message loop for {} (port: {})",
            self.direction, self.peer_ip, self.remote_port
        );

        // Register this connection in the peer registry
        config
            .peer_registry
            .register_peer_shared(self.peer_ip.clone(), self.shared_writer())
            .await;
        debug!(
            "📝 [{:?}] Registered {} in PeerConnectionRegistry",
            self.direction, self.peer_ip
        );

        // Send initial handshake
        let handshake = NetworkMessage::Handshake {
            magic: self.network_type.magic_bytes(),
            protocol_version: 2,
            network: format!("{}", self.network_type).to_lowercase(),
            commit_count: env!("GIT_COMMIT_COUNT").parse::<u32>().unwrap_or(0),
        };

        if let Err(e) = Self::send_message(&self.writer_tx, &handshake) {
            error!(
                "❌ [{:?}] Failed to send handshake to {}: {}",
                self.direction, self.peer_ip, e
            );
            return Err(e);
        }

        debug!(
            "🤝 [{:?}] Sent handshake to {}",
            self.direction, self.peer_ip
        );

        // Send initial ping
        match self.send_ping(config.blockchain.as_ref()).await {
            Ok(nonce) => {
                config
                    .peer_registry
                    .record_ping_sent(&self.peer_ip, nonce)
                    .await;
            }
            Err(e) => {
                error!(
                    "❌ [{:?}] Failed to send initial ping to {}: {}",
                    self.direction, self.peer_ip, e
                );
                return Err(e);
            }
        }

        // Outbound connections proactively request the remote's peer and masternode lists.
        // The inbound path (server.rs) does the same when a peer connects to us.
        // Without this, fresh nodes never learn about the full network from their bootstrap peers.
        if self.direction == ConnectionDirection::Outbound {
            let _ = Self::send_message(&self.writer_tx, &NetworkMessage::GetPeers);
            let _ = Self::send_message(&self.writer_tx, &NetworkMessage::GetMasternodes);
            debug!(
                "📤 [Outbound] Sent GetPeers + GetMasternodes to {} for peer discovery",
                self.peer_ip
            );

            // Send our masternode announcement so the remote peer learns our tier immediately.
            // Without this, peers only discover our tier when THEY dial us (inbound to us),
            // meaning outbound-only connections never propagate our Gold/Silver/Bronze status.
            if let Some(ref mn_registry) = config.masternode_registry {
                if let Some(our_address) = mn_registry.get_local_address().await {
                    let local_masternodes = mn_registry.get_all().await;
                    if let Some(our_mn) = local_masternodes
                        .iter()
                        .find(|mn| mn.masternode.address == our_address)
                    {
                        let cert = mn_registry.get_local_certificate().await;
                        let proof = our_mn
                            .masternode
                            .collateral_outpoint
                            .as_ref()
                            .and_then(|op| mn_registry.get_v4_proof(op))
                            .unwrap_or_default();
                        let announcement = if !proof.is_empty() {
                            NetworkMessage::MasternodeAnnouncementV4 {
                                address: our_mn.masternode.address.clone(),
                                reward_address: our_mn.reward_address.clone(),
                                tier: our_mn.masternode.tier,
                                public_key: our_mn.masternode.public_key,
                                collateral_outpoint: our_mn.masternode.collateral_outpoint.clone(),
                                certificate: cert.to_vec(),
                                started_at: mn_registry.get_started_at(),
                                collateral_proof: proof.clone(),
                            }
                        } else {
                            NetworkMessage::MasternodeAnnouncementV3 {
                                address: our_mn.masternode.address.clone(),
                                reward_address: our_mn.reward_address.clone(),
                                tier: our_mn.masternode.tier,
                                public_key: our_mn.masternode.public_key,
                                collateral_outpoint: our_mn.masternode.collateral_outpoint.clone(),
                                certificate: cert.to_vec(),
                                started_at: mn_registry.get_started_at(),
                            }
                        };
                        let version = if proof.is_empty() {
                            "V3"
                        } else {
                            "V4 (with collateral proof)"
                        };
                        let _ = Self::send_message(&self.writer_tx, &announcement);
                        info!(
                            "📢 [Outbound] Sent masternode announcement ({}) to {}",
                            version, self.peer_ip
                        );
                    }
                }
            }
        }

        // Extract broadcast_rx before the loop to avoid borrow checker issues
        let mut broadcast_rx = config.broadcast_rx.take();

        // Spawn a background genesis compatibility check for this connection.
        // If the peer responds with a different genesis hash we permanently ban it and
        // disconnect immediately.  The oneshot result is polled inside the select loop
        // using the same pattern as broadcast_rx.
        let mut genesis_check_rx: Option<tokio::sync::oneshot::Receiver<bool>> = if let Some(
            ref blockchain,
        ) =
            config.blockchain
        {
            if config.peer_registry.claim_genesis_check(&self.peer_ip) {
                match blockchain.get_block_by_height(0).await {
                    Ok(block) => {
                        let our_genesis_hash = block.hash();
                        let (tx, rx) = tokio::sync::oneshot::channel::<bool>();
                        let registry = Arc::clone(&config.peer_registry);
                        let peer_ip = self.peer_ip.clone();
                        tokio::spawn(async move {
                            let compatible = registry
                                .verify_genesis_compatibility(&peer_ip, our_genesis_hash)
                                .await;
                            registry.release_genesis_check(&peer_ip);
                            let _ = tx.send(compatible);
                        });
                        Some(rx)
                    }
                    Err(e) => {
                        // We can't read our own genesis block — do NOT fall back to a
                        // zero hash. That would guarantee a "mismatch" against every
                        // legitimate peer and permanently genesis-ban them all (this ban
                        // is not exempt from the whitelist). Skip the check entirely;
                        // it will retry on the next connection attempt.
                        tracing::warn!(
                                "⚠️ Skipping genesis compatibility check with {} — could not read our own genesis block: {}",
                                self.peer_ip, e
                            );
                        config.peer_registry.release_genesis_check(&self.peer_ip);
                        None
                    }
                }
            } else {
                None
            }
        } else {
            None
        };

        // Create handler once per connection (reused across all messages)
        let handler = MessageHandler::new(self.peer_ip.clone(), self.direction);

        let mut messages_received: u32 = 0;

        // Main message loop
        loop {
            tokio::select! {
                // Read incoming messages from I/O bridge channel
                result = self.msg_reader.recv() => {
                    let result = match result {
                        Some(r) => r,
                        None => {
                            info!("🔌 [{:?}] Reader channel closed for {}", self.direction, self.peer_ip);
                            break;
                        }
                    };
                    match result {
                        Ok(None) => {
                            if messages_received == 0 {
                                info!("🔌 [{:?}] Connection closed by {} after 0 messages (immediate rejection)", self.direction, self.peer_ip);
                            } else {
                                info!("🔌 [{:?}] Connection closed by {} (received {} message(s))", self.direction, self.peer_ip, messages_received);
                            }
                            break;
                        }
                        Ok(Some(message)) => {
                            messages_received += 1;
                            // Use unified message handler
                            let handle_result = self.handle_message_unified(message, &config, &handler).await;

                            if let Err(e) = handle_result {
                                if e.contains("is banned") {
                                    // Peer is banned — close the connection regardless of
                                    // whitelist/masternode status.  A banned connection cannot
                                    // process any messages; keeping it open only produces log
                                    // spam (one WARN per incoming message).  The outbound
                                    // reconnect loop will re-establish the connection after
                                    // the temporary ban expires.
                                    warn!(
                                        "🚫 [{:?}] Closing connection to {} (banned, will reconnect): {}",
                                        self.direction, self.peer_ip, e
                                    );
                                    break;
                                } else if e.contains("DISCONNECT:") {
                                    // Protocol-violation DISCONNECT signal.  Suppress for
                                    // whitelisted/masternode peers so a transient protocol
                                    // hiccup doesn't drop operator-trusted infrastructure.
                                    if self.is_whitelisted {
                                        warn!(
                                            "⚠️ [{:?}] Suppressing DISCONNECT for whitelisted peer {}: {}",
                                            self.direction, self.peer_ip, e
                                        );
                                    } else {
                                        warn!("🚫 [{:?}] Disconnecting peer {}: {}", self.direction, self.peer_ip, e);
                                        break;
                                    }
                                } else {
                                    warn!("⚠️ [{:?}] Error handling message from {}: {}",
                                          self.direction, self.peer_ip, e);
                                }
                            }
                        }
                        Err(e) => {
                            error!("❌ [{:?}] Error reading from {}: {}", self.direction, self.peer_ip, e);
                            // Clearly malicious oversized frames (>100 MB) — ban the sender,
                            // mirroring the inbound-side logic in server.rs.
                            // Whitelisted/masternode peers are excluded: they are
                            // operator-trusted infrastructure and a bad frame from them
                            // is almost certainly TLS corruption (old code), not an attack.
                            // Just close the connection; the reconnect loop handles recovery.
                            if e.contains("Frame too large") {
                                const MALICIOUS_FRAME_BYTES: u64 = 100 * 1024 * 1024;
                                let frame_bytes: Option<u64> = e
                                    .split_whitespace()
                                    .find_map(|w| {
                                        w.trim_end_matches("bytes")
                                            .trim_end_matches(':')
                                            .parse::<u64>()
                                            .ok()
                                    });
                                if frame_bytes.is_some_and(|b| b > MALICIOUS_FRAME_BYTES) {
                                    if self.is_whitelisted {
                                        tracing::warn!(
                                            "⚠️ [{:?}] Oversized frame from masternode/whitelisted peer {} — closing (stream unrecoverable, peer may need upgrade): {}",
                                            self.direction, self.peer_ip, e
                                        );
                                    } else if let Ok(ip) = self.peer_ip.parse::<std::net::IpAddr>() {
                                        if let Some(ref bl) = config.banlist {
                                            bl.write().await.record_frame_bomb_violation(ip, &e);
                                        }
                                        let ai_ref = config
                                            .ai_system
                                            .as_ref()
                                            .or_else(|| {
                                                config
                                                    .blockchain
                                                    .as_ref()
                                                    .and_then(|b| b.ai_system())
                                            });
                                        if let Some(ai) = ai_ref {
                                            ai.attack_detector.record_frame_bomb(&self.peer_ip);
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }

                // Forward broadcast messages to peer
                result = async {
                    if let Some(ref mut rx) = broadcast_rx {
                        rx.recv().await
                    } else {
                        // If no broadcast receiver, never resolve
                        std::future::pending().await
                    }
                } => {
                    if let Ok(msg) = result {
                        // Forward broadcast to this peer; writer closed means peer is dead
                        if let Err(e) = Self::send_message(&self.writer_tx, &msg) {
                            debug!("⚠️ [{:?}] Broadcast to {} failed ({}), closing connection",
                                  self.direction, self.peer_ip, e);
                            break;
                        }
                    }
                }

                // Receive genesis compatibility check result
                result = async {
                    if let Some(ref mut rx) = genesis_check_rx {
                        rx.await.unwrap_or(true) // timeout/cancelled → assume compatible
                    } else {
                        std::future::pending().await
                    }
                }, if genesis_check_rx.is_some() => {
                    // Consume the receiver so this branch never fires again
                    genesis_check_rx = None;
                    if !result {
                        // Peer replied with a different genesis hash — wrong network/fork.
                        // Permanently ban and disconnect, UNLESS the peer is whitelisted —
                        // an operator-trusted node with a different genesis hash means our
                        // local registry / chain state is the one out of sync. Keep the
                        // connection and let resync / convergence resolve it.
                        if self.is_whitelisted {
                            warn!(
                                "🚫 [{:?}] Genesis mismatch with whitelisted peer {} — disconnecting and banning (wrong chain, operator-trust does not override).",
                                self.direction, self.peer_ip
                            );
                        } else {
                            warn!(
                                "🚫 [{:?}] Disconnecting {} — genesis hash mismatch (wrong network/fork). Banning.",
                                self.direction, self.peer_ip
                            );
                        }
                        if let Some(ref banlist) = config.banlist {
                            let bare = self
                                .peer_ip
                                .split(':')
                                .next()
                                .unwrap_or(&self.peer_ip);
                            if let Ok(ip) = bare.parse::<std::net::IpAddr>() {
                                banlist
                                    .write()
                                    .await
                                    .add_genesis_ban(ip, "genesis hash mismatch");
                            }
                        }
                        break;
                    }
                }

                // Send periodic pings
                _ = ping_interval.tick() => {
                    match self.send_ping(config.blockchain.as_ref()).await {
                        Ok(nonce) => {
                            config.peer_registry.record_ping_sent(&self.peer_ip, nonce).await;
                        }
                        Err(e) => {
                            error!("❌ [{:?}] Failed to send ping to {}: {}", self.direction, self.peer_ip, e);
                            break;
                        }
                    }
                }

                // Check for timeout
                _ = timeout_check.tick() => {
                    if self.should_disconnect(&config.peer_registry).await {
                        error!("❌ [{:?}] Disconnecting {} due to timeout", self.direction, self.peer_ip);
                        break;
                    }
                }
            }
        }

        // Clear stale peer data on disconnect to prevent reporting old heights
        config.peer_registry.clear_peer_data(&self.peer_ip).await;

        info!(
            "🔌 [{:?}] Unified message loop ended for {}",
            self.direction, self.peer_ip
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ping_state_new() {
        let state = PingState::new();
        assert_eq!(state.missed_pongs, 0);
        assert!(state.pending_pings.is_empty());
        assert!(state.last_ping_sent.is_none());
        assert!(state.last_pong_received.is_none());
    }

    #[test]
    fn test_record_ping_sent() {
        let mut state = PingState::new();
        state.record_ping_sent(12345);

        assert_eq!(state.pending_pings.len(), 1);
        assert_eq!(state.pending_pings[0].0, 12345);
        assert!(state.last_ping_sent.is_some());
    }

    #[test]
    fn test_record_pong_matching() {
        let mut state = PingState::new();
        state.record_ping_sent(12345);

        let matched = state.record_pong_received(12345);

        assert!(matched);
        assert!(state.pending_pings.is_empty());
        assert_eq!(state.missed_pongs, 0);
    }

    #[test]
    fn test_record_pong_non_matching() {
        let mut state = PingState::new();
        state.record_ping_sent(12345);

        let matched = state.record_pong_received(99999);

        assert!(!matched);
        assert_eq!(state.pending_pings.len(), 1); // Original ping still there
    }

    #[test]
    fn test_multiple_pending_pings() {
        let mut state = PingState::new();

        // Send multiple pings
        for i in 1..=5 {
            state.record_ping_sent(i);
        }

        assert_eq!(state.pending_pings.len(), 5);

        // Respond to one
        let matched = state.record_pong_received(3);
        assert!(matched);
        assert_eq!(state.pending_pings.len(), 4);
    }

    #[test]
    fn test_pending_pings_timeout_cleanup() {
        let mut state = PingState::new();

        // Send 7 pings immediately - all should be kept since none have timed out
        for i in 1..=7 {
            state.record_ping_sent(i);
        }

        // All pings should be kept since they're recent (within 90 second timeout)
        assert_eq!(state.pending_pings.len(), 7);

        let nonces: Vec<u64> = state.pending_pings.iter().map(|(n, _)| *n).collect();
        assert_eq!(nonces, vec![1, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    fn test_direction_inbound() {
        let dir = ConnectionDirection::Inbound;
        assert_eq!(dir, ConnectionDirection::Inbound);
        assert_ne!(dir, ConnectionDirection::Outbound);
    }

    #[test]
    fn test_direction_outbound() {
        let dir = ConnectionDirection::Outbound;
        assert_eq!(dir, ConnectionDirection::Outbound);
        assert_ne!(dir, ConnectionDirection::Inbound);
    }

    #[test]
    fn test_ping_state_reset_on_pong() {
        let mut state = PingState::new();
        state.missed_pongs = 5; // Simulate some missed pongs

        state.record_ping_sent(100);
        let matched = state.record_pong_received(100);

        assert!(matched);
        assert_eq!(state.missed_pongs, 0); // Should be reset
    }
}
