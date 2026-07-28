//! Outbound P2P connection manager.
//!
//! `NetworkClient::start()` runs phased peer discovery and dials outbound peers.
//! Per-connection lifecycle is delegated to `ConnectionDriver::drive_outbound`.

use crate::ai::adaptive_reconnection::{AdaptiveReconnectionAI, ReconnectionConfig};
use crate::blockchain::Blockchain;
use crate::masternode_registry::MasternodeRegistry;
use crate::network::banlist::IPBanlist;
use crate::network::connection_manager::ConnectionManager;

use crate::network::peer_connection_registry::PeerConnectionRegistry;
use crate::network::tls::TlsConfig;
use crate::peer_manager::PeerManager;
use crate::NetworkType;
use std::collections::HashSet;
use std::sync::Arc;
use tokio::sync::RwLock;
use tokio::time::{sleep, Duration};

pub struct NetworkClient {
    peer_manager: Arc<PeerManager>,
    masternode_registry: Arc<MasternodeRegistry>,
    blockchain: Arc<Blockchain>,
    peer_connection_registry: Arc<PeerConnectionRegistry>,
    connection_manager: Arc<crate::network::connection_manager::ConnectionManager>,
    p2p_port: u16,
    max_peers: usize,
    reserved_masternode_slots: usize,
    local_ip: Option<String>,
    banned_peers: HashSet<String>,
    /// Real-time banlist for rejecting messages from banned peers
    ip_banlist: Option<Arc<RwLock<IPBanlist>>>,
    /// AI-powered adaptive reconnection
    reconnection_ai: Arc<AdaptiveReconnectionAI>,
    /// TLS configuration for encrypted connections
    tls_config: Option<Arc<TlsConfig>>,
    /// Network type (mainnet/testnet)
    network_type: NetworkType,
    /// Attack detector for recording coordinated disconnect events (outbound side of AV3).
    attack_detector: Option<Arc<crate::ai::attack_detector::AttackDetector>>,
    /// Full AI system for connection-level detection (frame bombs, TLS failures, etc.).
    ai_system: Option<Arc<crate::ai::AISystem>>,
    /// Discovered peer IPs from time-coin.io.  When non-empty, the daemon
    /// connects to these first on startup (Phase 0); if there is no local
    /// genesis the pyramid expansion in Phase 1 is gated until initial
    /// blockchain sync completes from this trusted set.
    discovered_peer_ips: Vec<String>,
    relay_store: Option<Arc<crate::messaging::relay::RelayStore>>,
    relay_signing_key: Option<Arc<ed25519_dalek::SigningKey>>,
    contacts_book: Option<Arc<crate::messaging::contacts::ContactsBook>>,
}

impl NetworkClient {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        peer_manager: Arc<PeerManager>,
        masternode_registry: Arc<MasternodeRegistry>,
        blockchain: Arc<Blockchain>,
        network_type: NetworkType,
        max_peers: usize,
        peer_connection_registry: Arc<PeerConnectionRegistry>,
        connection_manager: Arc<crate::network::connection_manager::ConnectionManager>,
        local_ip: Option<String>,
        banned_peers: Vec<String>,
        ip_banlist: Option<Arc<RwLock<IPBanlist>>>,
    ) -> Self {
        let reserved_masternode_slots = (max_peers * 40 / 100).clamp(20, 100);

        // Default AI-powered reconnection system (immediately overridden by set_reconnection_ai in main.rs).
        // Use an ephemeral DB for this throwaway instance — it is never actually queried.
        let ephemeral_db = Arc::new(
            sled::Config::new()
                .temporary(true)
                .open()
                .expect("ephemeral sled DB for NetworkClient default reconnection AI"),
        );
        let reconnection_ai = Arc::new(AdaptiveReconnectionAI::new(
            ephemeral_db,
            ReconnectionConfig::default(),
        ));

        Self {
            peer_manager,
            masternode_registry,
            blockchain,
            peer_connection_registry,
            connection_manager,
            p2p_port: network_type.default_p2p_port(),
            max_peers,
            reserved_masternode_slots,
            local_ip,
            banned_peers: banned_peers.into_iter().collect(),
            ip_banlist,
            reconnection_ai,
            tls_config: None,
            network_type,
            attack_detector: None,
            ai_system: None,
            discovered_peer_ips: Vec::new(),
            relay_store: None,
            relay_signing_key: None,
            contacts_book: None,
        }
    }

    /// Replace the reconnection AI with a shared instance from AISystem.
    /// This ensures connection learning data is shared across all subsystems.
    pub fn set_reconnection_ai(&mut self, ai: Arc<AdaptiveReconnectionAI>) {
        self.reconnection_ai = ai;
    }

    /// Set TLS configuration for encrypted peer connections
    pub fn set_tls_config(&mut self, tls_config: Arc<TlsConfig>) {
        self.tls_config = Some(tls_config);
    }

    /// Set the attack detector so outbound disconnects are recorded for AV3 detection.
    pub fn set_attack_detector(&mut self, ad: Arc<crate::ai::attack_detector::AttackDetector>) {
        self.attack_detector = Some(ad);
    }

    /// Wire the full AI system for outbound connection-level attack detection.
    pub fn set_ai_system(&mut self, ai: Arc<crate::ai::AISystem>) {
        self.ai_system = Some(ai);
    }

    /// Wire the secure messaging relay store so outbound connections can handle MSG_* messages.
    pub fn set_relay_store(
        &mut self,
        relay_store: Arc<crate::messaging::relay::RelayStore>,
        signing_key: Arc<ed25519_dalek::SigningKey>,
    ) {
        self.relay_store = Some(relay_store);
        self.relay_signing_key = Some(signing_key);
    }

    /// Wire the contacts book so outbound connections can persist and look up pubkeys.
    pub fn set_contacts_book(
        &mut self,
        contacts_book: Arc<crate::messaging::contacts::ContactsBook>,
    ) {
        self.contacts_book = Some(contacts_book);
    }

    /// Seed the client with trusted discovery peers fetched at startup.
    pub fn set_discovered_peer_ips(&mut self, peers: Vec<String>) {
        self.discovered_peer_ips = peers;
    }

    pub async fn start(&self) {
        let peer_manager = self.peer_manager.clone();
        let masternode_registry = self.masternode_registry.clone();
        let blockchain = self.blockchain.clone();
        let peer_registry = self.peer_connection_registry.clone();
        let connection_manager = self.connection_manager.clone();
        let max_peers = self.max_peers;
        let reserved_masternode_slots = self.reserved_masternode_slots;
        let local_ip = self.local_ip.clone();
        let banned_peers = self.banned_peers.clone();
        let discovered_peer_ips = self.discovered_peer_ips.clone();

        let res = ConnectionResources {
            port: self.p2p_port,
            connection_manager: connection_manager.clone(),
            masternode_registry: masternode_registry.clone(),
            blockchain: blockchain.clone(),
            peer_manager: peer_manager.clone(),
            peer_registry: peer_registry.clone(),
            reconnection_ai: self.reconnection_ai.clone(),
            ip_banlist: self.ip_banlist.clone(),
            tls_config: self.tls_config.clone(),
            network_type: self.network_type,
            attack_detector: self.attack_detector.clone(),
            ai_system: self.ai_system.clone(),
            relay_store: self.relay_store.clone(),
            relay_signing_key: self.relay_signing_key.clone(),
            contacts_book: self.contacts_book.clone(),
        };

        tokio::spawn(async move {
            tracing::info!(
                "🔌 Starting network client (max peers: {}, reserved for masternodes: {})",
                max_peers,
                reserved_masternode_slots
            );
            tracing::info!("🧠 AI-powered adaptive reconnection enabled");

            if let Some(ref ip) = local_ip {
                tracing::info!("🏠 Local IP: {} (will skip self-connections)", ip);
            }

            // Helper: should we skip connecting to this IP?
            // Only skip when we already have a *live writer* or a dial in flight.
            // Zombie CM `Connected` without a writer must NOT block redial (that
            // was collapsing the mesh from ~18 peers down to 1).
            let should_skip = |ip: &str| -> bool {
                if let Some(ref local) = local_ip {
                    if ip == local.as_str() {
                        return true;
                    }
                }
                if banned_peers.contains(ip) {
                    return true;
                }
                if peer_registry.has_live_writer_sync(ip) {
                    return true;
                }
                if connection_manager.is_connecting(ip) {
                    return true;
                }
                false
            };

            // Helper: deduplicate peer addresses by IP
            let dedup_peers = |peers: Vec<String>| -> Vec<String> {
                let mut seen = std::collections::HashSet::new();
                peers
                    .into_iter()
                    .filter_map(|addr| {
                        let ip = if let Some(pos) = addr.rfind(':') {
                            &addr[..pos]
                        } else {
                            &addr
                        };
                        if seen.insert(ip.to_string()) {
                            Some(ip.to_string())
                        } else {
                            None
                        }
                    })
                    .collect()
            };

            // PHASE 0: When joining an existing network without local genesis, dial the
            // trusted discovery peers first. This guarantees we have a path to the
            // whitelist before the broader topology/reconnection logic kicks in.
            let trusted_startup_peers = dedup_peers(discovered_peer_ips);
            if !blockchain.has_genesis() && !trusted_startup_peers.is_empty() {
                tracing::info!(
                    "🔐 [PHASE0] No local genesis - connecting to {} trusted discovery peer(s) first",
                    trusted_startup_peers.len()
                );

                let mut phase0_connections = 0usize;
                for ip in &trusted_startup_peers {
                    if should_skip(ip) {
                        continue;
                    }
                    if let Some(ref bl) = res.ip_banlist {
                        if let Ok(parsed_ip) = ip.parse::<std::net::IpAddr>() {
                            if bl.write().await.is_banned(parsed_ip).is_some() {
                                tracing::debug!("⏭️  [PHASE0] Skipping {} (banned)", ip);
                                continue;
                            }
                        }
                    }
                    if !connection_manager.mark_connecting(ip) {
                        continue;
                    }
                    tracing::debug!("🔗 [PHASE0] Connecting to trusted peer {}", ip);
                    res.spawn(ip.clone(), false);
                    phase0_connections += 1;
                }

                if phase0_connections > 0 {
                    tracing::info!(
                        "✅ [PHASE0] Initiated {} trusted bootstrap connection(s)",
                        phase0_connections
                    );
                    sleep(Duration::from_secs(2)).await;
                }

                // Gate Phase 1 expansion until initial blockchain sync completes.
                // While we have no genesis (or are still actively syncing), the daemon
                // only talks to time-coin.io's trusted peer list — no pyramid expansion
                // to potentially malicious peers that could feed a forked chain during
                // initial download.  Bounded by PHASE0_SYNC_TIMEOUT_SECS so we don't
                // hang forever if the trusted set is unreachable.
                const PHASE0_SYNC_TIMEOUT_SECS: u64 = 600; // 10 min
                const PHASE0_POLL_INTERVAL_SECS: u64 = 2;
                let phase0_started = std::time::Instant::now();
                let mut last_log = phase0_started;
                tracing::info!(
                    "⏳ [PHASE0] Holding Phase 1 until initial blockchain sync completes (timeout {}s)",
                    PHASE0_SYNC_TIMEOUT_SECS
                );
                loop {
                    if blockchain.has_genesis() && !blockchain.is_syncing() {
                        tracing::info!(
                            "✅ [PHASE0] Initial sync complete after {}s — proceeding to Phase 1",
                            phase0_started.elapsed().as_secs()
                        );
                        break;
                    }
                    if phase0_started.elapsed().as_secs() >= PHASE0_SYNC_TIMEOUT_SECS {
                        tracing::warn!(
                            "⏱️ [PHASE0] {}s elapsed without sync completing — proceeding to Phase 1 with broader peer set",
                            PHASE0_SYNC_TIMEOUT_SECS
                        );
                        break;
                    }
                    if last_log.elapsed().as_secs() >= 30 {
                        tracing::info!(
                            "⏳ [PHASE0] Still waiting for sync (genesis={}, syncing={}, height={})",
                            blockchain.has_genesis(),
                            blockchain.is_syncing(),
                            blockchain.get_height()
                        );
                        last_log = std::time::Instant::now();
                    }
                    sleep(Duration::from_secs(PHASE0_POLL_INTERVAL_SECS)).await;
                }
            }

            // PHASE 1: Pyramid-aware startup connections.
            //
            // Network topology mirrors the collateral tier hierarchy:
            //
            //          ┌──── Gold ────┐   ← full mesh backbone (few nodes, high stake)
            //         Silver ── Silver      ← connect ALL Gold + lateral Silver peers
            //        Bronze  ── Bronze      ← connect N Silver (upward) + lateral Bronze
            //       Free  Free  Free  Free  ← connect N Bronze/Silver (upward only)
            //
            // SMALL NETWORK EXCEPTION: if total masternodes ≤ connection limit, every
            // node connects to every other node (full mesh regardless of tier).  This
            // guarantees all nodes see each other for gossip, voting, and rewards.
            use crate::types::MasternodeTier;
            use rand::seq::SliceRandom;

            // Number of peers to connect to per relationship
            const GOLD_SILVER_EXTRAS: usize = 3; // Gold also connects to N Silver for downward visibility
            const SILVER_LATERAL: usize = 4; // Silver lateral peers within Silver tier
            const BRONZE_UPWARD: usize = 5; // Bronze → Silver connections
            const BRONZE_LATERAL: usize = 3; // Bronze lateral peers within Bronze tier (when upward nodes exist)
            const FREE_UPWARD: usize = 5; // Free → Bronze connections (+ 1 Silver fallback)
            const FULL_MESH_THRESHOLD: usize = 50; // Use full mesh when total nodes ≤ this

            // Determine our own tier
            let our_tier: Option<MasternodeTier> = {
                let our_ip = masternode_registry.get_local_address().await;
                match our_ip {
                    Some(ref ip) => masternode_registry.get(ip).await.map(|i| i.masternode.tier),
                    None => None,
                }
            };

            // Fetch masternodes by tier once.
            // Use list_all() (not list_by_tier which filters is_active) because at startup
            // all nodes load from sled as inactive — they have no peer reports yet.
            // PHASE1's job is to establish the connections that will activate them.
            let all_nodes_for_phase1 = masternode_registry.list_all().await;
            let gold_nodes: Vec<_> = all_nodes_for_phase1
                .iter()
                .filter(|m| m.masternode.tier == MasternodeTier::Gold)
                .cloned()
                .collect();
            let mut silver_nodes: Vec<_> = all_nodes_for_phase1
                .iter()
                .filter(|m| m.masternode.tier == MasternodeTier::Silver)
                .cloned()
                .collect();
            let mut bronze_nodes: Vec<_> = all_nodes_for_phase1
                .iter()
                .filter(|m| m.masternode.tier == MasternodeTier::Bronze)
                .cloned()
                .collect();
            let mut free_nodes: Vec<_> = all_nodes_for_phase1
                .iter()
                .filter(|m| m.masternode.tier == MasternodeTier::Free)
                .cloned()
                .collect();

            silver_nodes.shuffle(&mut rand::thread_rng());
            bronze_nodes.shuffle(&mut rand::thread_rng());
            free_nodes.shuffle(&mut rand::thread_rng());

            let total_masternodes =
                gold_nodes.len() + silver_nodes.len() + bronze_nodes.len() + free_nodes.len();

            // Build the connection target list for our tier
            let targets: Vec<String> = if total_masternodes <= FULL_MESH_THRESHOLD {
                // Small network: connect to everyone — full mesh guarantees all nodes
                // can gossip, vote, and see each other regardless of tier.
                tracing::info!(
                    "🔗 [PHASE1] Small network ({} masternodes ≤ {}): using full mesh",
                    total_masternodes,
                    FULL_MESH_THRESHOLD
                );
                gold_nodes
                    .iter()
                    .chain(silver_nodes.iter())
                    .chain(bronze_nodes.iter())
                    .chain(free_nodes.iter())
                    .map(|m| m.masternode.address.clone())
                    .collect()
            } else {
                match our_tier {
                    Some(MasternodeTier::Gold) => {
                        // Gold: full mesh with ALL Gold + a few Silver for downward visibility
                        let mut t: Vec<String> = gold_nodes
                            .iter()
                            .map(|m| m.masternode.address.clone())
                            .collect();
                        t.extend(
                            silver_nodes
                                .iter()
                                .take(GOLD_SILVER_EXTRAS)
                                .map(|m| m.masternode.address.clone()),
                        );
                        t
                    }
                    Some(MasternodeTier::Silver) => {
                        // Silver: connect to ALL Gold (backbone) + lateral Silver peers.
                        // If no Gold exists, connect to ALL Silver (single-tier network).
                        let mut t: Vec<String> = gold_nodes
                            .iter()
                            .map(|m| m.masternode.address.clone())
                            .collect();
                        let silver_limit = if t.is_empty() {
                            silver_nodes.len()
                        } else {
                            SILVER_LATERAL
                        };
                        t.extend(
                            silver_nodes
                                .iter()
                                .take(silver_limit)
                                .map(|m| m.masternode.address.clone()),
                        );
                        t
                    }
                    Some(MasternodeTier::Bronze) => {
                        // Bronze: N Silver (upward) + lateral Bronze; fall back to Gold if no Silver.
                        // If no upward tier exists at all, connect to ALL Bronze so the
                        // network stays fully connected even in a Bronze-only deployment.
                        let mut t: Vec<String> = silver_nodes
                            .iter()
                            .take(BRONZE_UPWARD)
                            .map(|m| m.masternode.address.clone())
                            .collect();
                        if t.is_empty() {
                            t.extend(gold_nodes.iter().map(|m| m.masternode.address.clone()));
                        }
                        let bronze_limit = if t.is_empty() {
                            bronze_nodes.len()
                        } else {
                            BRONZE_LATERAL
                        };
                        t.extend(
                            bronze_nodes
                                .iter()
                                .take(bronze_limit)
                                .map(|m| m.masternode.address.clone()),
                        );
                        t
                    }
                    None | Some(MasternodeTier::Free) => {
                        // Free / unregistered: connect upward to Bronze, with a Silver fallback.
                        // If no upward tier exists, connect to ALL Free nodes.
                        let mut t: Vec<String> = bronze_nodes
                            .iter()
                            .take(FREE_UPWARD)
                            .map(|m| m.masternode.address.clone())
                            .collect();
                        t.extend(
                            silver_nodes
                                .iter()
                                .take(1)
                                .map(|m| m.masternode.address.clone()),
                        );
                        if t.is_empty() {
                            // No upward tier: try Gold, then all Free peers
                            t.extend(gold_nodes.iter().map(|m| m.masternode.address.clone()));
                            if t.is_empty() {
                                t.extend(free_nodes.iter().map(|m| m.masternode.address.clone()));
                            }
                        }
                        t
                    }
                }
            };

            tracing::info!(
                "🔺 [PHASE1] Pyramid startup (our tier: {:?}) — {} target(s): {:?}",
                our_tier,
                targets.len(),
                targets
            );

            let mut masternode_connections = 0;
            for ip in targets.iter().take(reserved_masternode_slots) {
                if should_skip(ip) {
                    if connection_manager.is_connected(ip) {
                        masternode_connections += 1;
                    }
                    continue;
                }
                // Higher IP dials lower IP — wait for inbound from peers that rank above us,
                // unless we've been waiting long enough that they're likely unreachable.
                if !connection_manager.is_preferred_dialer(ip)
                    && !connection_manager.passive_wait_expired(ip)
                {
                    tracing::debug!(
                        "⏳ [PHASE1] Waiting for inbound from {} (they are preferred dialer)",
                        ip
                    );
                    continue;
                }
                if !connection_manager.mark_connecting(ip) {
                    continue;
                }
                masternode_connections += 1;
                tracing::debug!("🔗 [PHASE1] Connecting to: {} (tier: {:?})", ip, our_tier);
                res.spawn(ip.clone(), true);
            }

            // Brief delay for masternode connections to initiate
            sleep(Duration::from_millis(500)).await;

            tracing::info!(
                "✅ Initiated {} masternode connection(s), {} slots for regular peers",
                masternode_connections,
                max_peers.saturating_sub(masternode_connections)
            );

            // PHASE 2: Fill remaining slots with regular peers
            let available_slots = max_peers.saturating_sub(masternode_connections);
            if available_slots > 0 {
                let unique_peers = dedup_peers(peer_manager.get_all_peers().await);
                tracing::info!(
                    "🔌 Filling {} slot(s) with {} unique regular peers",
                    available_slots,
                    unique_peers.len()
                );

                for ip in unique_peers.iter().take(available_slots) {
                    if should_skip(ip) {
                        continue;
                    }
                    // Skip IPs that are currently banned — same guard as PHASE3.
                    if let Some(ref bl) = res.ip_banlist {
                        if let Ok(parsed_ip) = ip.parse::<std::net::IpAddr>() {
                            if bl.write().await.is_banned(parsed_ip).is_some() {
                                tracing::debug!("⏭️  [PHASE2] Skipping {} (banned)", ip);
                                continue;
                            }
                        }
                    }
                    if !connection_manager.is_preferred_dialer(ip)
                        && !connection_manager.passive_wait_expired(ip)
                    {
                        tracing::debug!(
                            "⏳ [PHASE2] Waiting for inbound from {} (they are preferred dialer)",
                            ip
                        );
                        continue;
                    }
                    if !connection_manager.mark_connecting(ip) {
                        continue;
                    }
                    let is_registered_mn = masternode_registry
                        .list_all()
                        .await
                        .iter()
                        .any(|mn| mn.masternode.address == *ip);
                    tracing::debug!("🔗 [PHASE2] Connecting to: {}", ip);
                    res.spawn(ip.clone(), is_registered_mn);
                }
            }

            // PHASE 3: Periodic peer discovery with masternode priority.
            // `priority_notify` is fired by `mark_inactive_on_disconnect` when a
            // paid-tier node disconnects, so we wake immediately and reconnect instead
            // of waiting up to 30 s for the next scheduled tick.
            let peer_discovery_interval = Duration::from_secs(30);
            let priority_notify = masternode_registry.priority_reconnect_notify();
            // On startup, fire one immediate pass (after Phase 1/2 settle) that bypasses
            // AI cooldowns so registered masternodes reconnect within seconds of restart.
            let mut startup_pass = true;
            loop {
                // Either wait for the regular 30-second interval OR wake immediately
                // on a paid-tier disconnect signal from the registry.
                let priority_wake = if startup_pass {
                    // Give Phase 1/2 a moment to establish connections, then go immediately.
                    sleep(Duration::from_secs(3)).await;
                    true
                } else {
                    tokio::select! {
                        _ = sleep(peer_discovery_interval) => false,
                        _ = priority_notify.notified() => true,
                    }
                };

                tracing::info!(
                    "🩺 [PHASE3-STALL-TRACE] tick woke (priority_wake={})",
                    priority_wake
                );

                // Clean up stale Connecting states (stuck >30s)
                let stale = connection_manager.cleanup_stale_connecting(Duration::from_secs(30));
                if stale > 0 {
                    tracing::info!("🧹 Reset {} stale connecting peer(s)", stale);
                }

                // Heal zombie Connected slots with no live writer so PHASE3 can redial.
                let live_ips: std::collections::HashSet<String> = peer_registry
                    .get_connected_peers()
                    .await
                    .into_iter()
                    .collect();
                let healed = connection_manager.heal_connected_without_writers(&live_ips);
                if !healed.is_empty() {
                    tracing::warn!(
                        "🩹 Healed {} zombie Connected session(s) with no live writer: {:?}",
                        healed.len(),
                        healed
                    );
                    for ip in &healed {
                        peer_registry.unregister_peer(ip).await;
                    }
                }

                let active_count = masternode_registry.list_active().await.len();
                let (live_total, live_in, live_out) = peer_registry.live_direction_counts().await;

                tracing::debug!(
                    "🔍 Peer check: {} live ({} out, {} in), {} active masternodes, {} total slots",
                    live_total,
                    live_out,
                    live_in,
                    active_count,
                    max_peers
                );

                // Masternodes: ensure full mesh with all registered masternodes.
                // Phase 1 handles initial connections, but masternodes that come
                // online after our startup (or that we lost connection to) must
                // be reconnected here. Uses list_all() (not list_active) because
                // masternodes marked inactive are exactly the ones we need to
                // reconnect to. AI reconnection advice still applies to avoid
                // hammering nodes that are legitimately offline.
                {
                    let all_masternodes = masternode_registry.list_all().await;
                    let total_mn = all_masternodes.len();
                    let mut reconnected = 0usize;

                    // AV25: Pre-count currently-connected nodes per /24 subnet so we can
                    // cap how many Free-tier nodes we reconnect from each attacking subnet.
                    const MAX_FREE_TIER_RECONNECT_PER_SUBNET: usize = 3;
                    let mut subnet_active_counts: std::collections::HashMap<String, usize> =
                        std::collections::HashMap::new();
                    for mn_info in &all_masternodes {
                        let addr = &mn_info.masternode.address;
                        // Live writers + in-flight dials only (not zombie Connected).
                        if peer_registry.has_live_writer_sync(addr)
                            || connection_manager.is_connecting(addr)
                        {
                            let ip = addr.split(':').next().unwrap_or(addr);
                            let parts: Vec<&str> = ip.split('.').collect();
                            let subnet = if parts.len() >= 3 {
                                format!("{}.{}.{}", parts[0], parts[1], parts[2])
                            } else {
                                ip.to_string()
                            };
                            *subnet_active_counts.entry(subnet).or_insert(0) += 1;
                        }
                    }

                    for mn_info in &all_masternodes {
                        let mn_ip = &mn_info.masternode.address;
                        if should_skip(mn_ip) {
                            continue;
                        }
                        // should_skip already covers live writer + Connecting.
                        // Stall-diagnosis tracing (2026-07-13 incident): the reconnection
                        // pass silently stopped logging for ~7h with RPC still responsive,
                        // suggesting one specific await here never returned. These
                        // before/after pairs pinpoint exactly which one if it recurs —
                        // remove once the root cause is confirmed and fixed.
                        tracing::info!("🩺 [PHASE3-STALL-TRACE] {} pre-is_incompatible", mn_ip);
                        let incompatible = peer_registry.is_incompatible(mn_ip).await;
                        tracing::info!("🩺 [PHASE3-STALL-TRACE] {} post-is_incompatible", mn_ip);
                        if incompatible {
                            continue;
                        }
                        // Respect AI advice to avoid hammering offline nodes.
                        // Exceptions:
                        //   (a) paid-tier node on a priority-wake signal → reconnect immediately
                        //   (b) whitelisted peer → always bypass AI cooldown (operator trust)
                        let is_paid_tier = !matches!(mn_info.masternode.tier, MasternodeTier::Free);
                        // Higher-IP-dials-lower: only the preferred dialer initiates.
                        // Exceptions: (a) priority wake after a paid-tier disconnect — either
                        // side may redial so a dead higher-IP peer cannot leave us isolated;
                        // (b) we've been waiting passively long enough that they're likely
                        // unreachable (down/firewalled/NAT'd) and will never dial us.
                        let force_dial = priority_wake && is_paid_tier;
                        if !force_dial
                            && !connection_manager.is_preferred_dialer(mn_ip)
                            && !connection_manager.passive_wait_expired(mn_ip)
                        {
                            tracing::debug!(
                                "⏳ [PHASE3-MN] Waiting for inbound from {} (they dial us)",
                                mn_ip
                            );
                            continue;
                        }
                        // Shared ceiling: once a peer has failed this many times in a row,
                        // every "reconnect immediately" exception below (manual whitelist,
                        // startup pass, paid-tier priority wake) stops bypassing the AI
                        // cooldown. Without this, a paid-tier peer that keeps failing
                        // re-fires `priority_reconnect_notify` on every disconnect (that's
                        // what "genuine disconnect" triggers), which re-enters this loop
                        // and bypasses backoff forever — observed 2026-07-15 as a permanent
                        // ~30s hammer against Gold masternodes that were TLS-handshake-eof
                        // rejecting us the entire time.
                        const FAST_RETRY_FAILURE_LIMIT: u32 = 5;
                        let mn_is_whitelisted = if let Some(ref bl) = res.ip_banlist {
                            if let Ok(parsed) = mn_ip.parse::<std::net::IpAddr>() {
                                tracing::info!(
                                    "🩺 [PHASE3-STALL-TRACE] {} pre-banlist-read",
                                    mn_ip
                                );
                                let whitelisted = bl.read().await.is_whitelisted(parsed);
                                tracing::info!(
                                    "🩺 [PHASE3-STALL-TRACE] {} post-banlist-read",
                                    mn_ip
                                );
                                whitelisted
                            } else {
                                false
                            }
                        } else {
                            false
                        };
                        if mn_is_whitelisted {
                            // Whitelisted peers get a short cooldown for the first several
                            // failures — reconnect within one PHASE3-MN cycle so a brief blip
                            // recovers almost instantly (near-100% uptime for trusted
                            // masternodes). Max backoff while under the limit: 10s (well under
                            // the 30s tick).
                            //
                            // Once a peer has failed FAST_RETRY_FAILURE_LIMIT times in a
                            // row, it's not a blip — it's a peer that's actively rejecting us
                            // (e.g. repeated TLS handshake resets). Retrying it at the same 10s/
                            // 30s floor forever accomplishes nothing and looks like abuse both
                            // to the remote and to our own AV3 IP-cycling detector. Fall through
                            // to the same exponential backoff used for non-whitelisted peers
                            // instead of hammering indefinitely.
                            let failures = res.reconnection_ai.consecutive_failures_for(mn_ip);
                            if failures > 0 && failures <= FAST_RETRY_FAILURE_LIMIT {
                                let min_delay_secs =
                                    (5u64 * 2u64.pow(failures.saturating_sub(1).min(1))).min(10);
                                let elapsed = connection_manager
                                    .time_since_disconnect(mn_ip)
                                    .unwrap_or(Duration::MAX);
                                if elapsed < Duration::from_secs(min_delay_secs) {
                                    tracing::debug!(
                                        "⏸️  [PHASE3-MN] Whitelisted {} cooling down ({} failures, {}s/{}s elapsed)",
                                        mn_ip, failures, elapsed.as_secs(), min_delay_secs
                                    );
                                    continue;
                                }
                            } else if failures > FAST_RETRY_FAILURE_LIMIT {
                                let advice =
                                    res.reconnection_ai.get_reconnection_advice(mn_ip, true);
                                if !advice.should_attempt {
                                    tracing::debug!(
                                        "⏭️  [PHASE3-MN] Skipping whitelisted {} (sustained failures={}, AI cooldown: {})",
                                        mn_ip, failures, advice.reasoning
                                    );
                                    continue;
                                }
                            }
                        } else {
                            let failures = res.reconnection_ai.consecutive_failures_for(mn_ip);
                            // startup_pass and paid-tier priority wakes normally bypass the AI
                            // cooldown entirely so a fresh boot or a genuine one-off disconnect
                            // reconnects immediately. But a paid-tier peer that keeps failing
                            // re-fires priority_wake on every disconnect — past
                            // FAST_RETRY_FAILURE_LIMIT that stops being a one-off and the
                            // bypass must stop too, or backoff never engages.
                            let bypass_cooldown = (startup_pass || (priority_wake && is_paid_tier))
                                && failures <= FAST_RETRY_FAILURE_LIMIT;
                            if !bypass_cooldown {
                                let advice =
                                    res.reconnection_ai.get_reconnection_advice(mn_ip, true);
                                if !advice.should_attempt {
                                    tracing::debug!(
                                        "⏭️  [PHASE3-MN] Skipping {} (AI cooldown: {}, failures={})",
                                        mn_ip,
                                        advice.reasoning,
                                        failures
                                    );
                                    continue;
                                }
                            }
                        }
                        // Skip IPs that are currently banned — avoids full TCP+TLS
                        // round-trip to banned subnets, which wastes tokio tasks + memory.
                        if let Some(ref bl) = res.ip_banlist {
                            if let Ok(parsed_ip) = mn_ip.parse::<std::net::IpAddr>() {
                                tracing::info!(
                                    "🩺 [PHASE3-STALL-TRACE] {} pre-banlist-write",
                                    mn_ip
                                );
                                let banned = bl.write().await.is_banned(parsed_ip).is_some();
                                tracing::info!(
                                    "🩺 [PHASE3-STALL-TRACE] {} post-banlist-write",
                                    mn_ip
                                );
                                if banned {
                                    tracing::debug!("⏭️  [PHASE3-MN] Skipping {} (banned)", mn_ip);
                                    continue;
                                }
                            }
                        }
                        // AV25: Per-/24 subnet cap for Free-tier reconnections.
                        // Stops PHASE3 from maintaining dozens of connections to one attacker subnet.
                        // OnChain masternodes bypass: they're verified on-chain and the operator
                        // may legitimately run multiple nodes on the same /24.
                        let is_onchain = matches!(
                            mn_info.registration_source,
                            crate::masternode_registry::RegistrationSource::OnChain(_)
                        );
                        if mn_info.masternode.tier == MasternodeTier::Free
                            && !is_onchain
                            && !mn_is_whitelisted
                        {
                            let ip = mn_ip.split(':').next().unwrap_or(mn_ip);
                            let parts: Vec<&str> = ip.split('.').collect();
                            let subnet = if parts.len() >= 3 {
                                format!("{}.{}.{}", parts[0], parts[1], parts[2])
                            } else {
                                ip.to_string()
                            };
                            let active = subnet_active_counts.get(&subnet).copied().unwrap_or(0);
                            if active >= MAX_FREE_TIER_RECONNECT_PER_SUBNET {
                                tracing::debug!(
                                    "⏭️  [PHASE3-MN] Skipping {} (AV25: {} already active from /24 {})",
                                    mn_ip,
                                    active,
                                    subnet
                                );
                                continue;
                            }
                        }
                        if !connection_manager.mark_connecting(mn_ip) {
                            continue;
                        }
                        tracing::info!(
                            "🔗 [PHASE3-MN] Reconnecting to masternode {} (tier: {:?})",
                            mn_ip,
                            mn_info.masternode.tier
                        );
                        res.spawn(mn_ip.clone(), true);
                        reconnected += 1;
                        // AV25: count this new outbound connection against the subnet cap.
                        if mn_info.masternode.tier == MasternodeTier::Free {
                            let ip = mn_ip.split(':').next().unwrap_or(mn_ip);
                            let parts: Vec<&str> = ip.split('.').collect();
                            let subnet = if parts.len() >= 3 {
                                format!("{}.{}.{}", parts[0], parts[1], parts[2])
                            } else {
                                ip.to_string()
                            };
                            *subnet_active_counts.entry(subnet).or_insert(0) += 1;
                        }
                        sleep(Duration::from_millis(10)).await;
                    }

                    if reconnected > 0 {
                        tracing::info!(
                            "🔗 [PHASE3-MN] Initiated {} masternode reconnection(s) ({} registered){}",
                            reconnected, total_mn,
                            if startup_pass { " [startup pass]" } else { "" }
                        );
                    } else if total_mn > 1 {
                        tracing::debug!(
                            "🔗 [PHASE3-MN] All {} registered masternodes already connected or skipped",
                            total_mn
                        );
                    }
                    startup_pass = false;
                }

                // Fill remaining slots with regular peers — prefer less-loaded ones
                // so new nodes naturally spread connections across the network.
                let available_slots = max_peers.saturating_sub(live_total);
                if available_slots > 0 {
                    let mut unique_peers = dedup_peers(peer_manager.get_all_peers().await);
                    // Sort by known connection load (ascending) so we dial the least-loaded
                    // candidates first.  Peers with unknown load sort to the back (u16::MAX).
                    unique_peers.sort_by_key(|ip| peer_registry.get_peer_load(ip));
                    for ip in unique_peers.iter().take(available_slots) {
                        if should_skip(ip) {
                            continue;
                        }
                        // Skip masternodes — handled by Phase 3-MN block above
                        if masternode_registry.get(ip).await.is_some() {
                            continue;
                        }
                        if connection_manager.is_reconnecting(ip) {
                            continue;
                        }
                        if !connection_manager.is_preferred_dialer(ip)
                            && !connection_manager.passive_wait_expired(ip)
                        {
                            continue;
                        }
                        // Check AI advice before spawning. If a peer has failed enough
                        // times to reach deep exponential backoff (≥5 consecutive
                        // failures), evict it from the peer_manager entirely — it
                        // will be re-added via PeerExchange if it recovers.
                        const FORGET_THRESHOLD: u32 = 5;
                        let failures = res.reconnection_ai.consecutive_failures_for(ip);
                        if failures >= FORGET_THRESHOLD {
                            peer_manager.remove_peer(ip).await;
                            res.reconnection_ai.forget_peer(ip);
                            tracing::info!(
                                "🗑️  Evicted persistently unreachable peer {} ({} consecutive failures)",
                                ip, failures
                            );
                            continue;
                        }
                        let advice = res.reconnection_ai.get_reconnection_advice(ip, false);
                        if !advice.should_attempt {
                            tracing::debug!(
                                "⏭️  [PHASE3-PEER] Skipping {} (AI cooldown: {})",
                                ip,
                                advice.reasoning
                            );
                            continue;
                        }
                        // Skip IPs that are currently banned (including banned subnets)
                        if let Some(ref bl) = res.ip_banlist {
                            if let Ok(parsed_ip) = ip.parse::<std::net::IpAddr>() {
                                if bl.write().await.is_banned(parsed_ip).is_some() {
                                    tracing::debug!("⏭️  [PHASE3-PEER] Skipping {} (banned)", ip);
                                    continue;
                                }
                            }
                        }
                        if !connection_manager.mark_connecting(ip) {
                            continue;
                        }
                        tracing::debug!("🔗 [PHASE3-PEER] Connecting to: {}", ip);
                        res.spawn(ip.clone(), false);
                        sleep(Duration::from_millis(10)).await;
                    }
                }

                // PHASE 4: Periodic chain tip comparison for fork detection
                let our_height = blockchain.get_height();
                if our_height > 0 {
                    let our_hash = blockchain.get_block_hash(our_height).unwrap_or([0u8; 32]);
                    let connected_peers = peer_registry.get_connected_peers().await;
                    if !connected_peers.is_empty() {
                        tracing::debug!(
                            "🔍 Chain tip check: height {} hash {}, querying {} peers",
                            our_height,
                            hex::encode(&our_hash[..8]),
                            connected_peers.len()
                        );
                        for peer_ip in connected_peers.iter() {
                            let msg = crate::network::message::NetworkMessage::GetChainTip;
                            if let Err(e) = peer_registry.send_to_peer(peer_ip, msg).await {
                                tracing::debug!("Failed to send GetChainTip to {}: {}", peer_ip, e);
                            }
                        }
                    }
                }
            }
        });
    }
}

/// Shared resources for spawning peer connections.
/// Eliminates repeated Arc cloning at each call site.
#[derive(Clone)]
struct ConnectionResources {
    port: u16,
    connection_manager: Arc<ConnectionManager>,
    masternode_registry: Arc<MasternodeRegistry>,
    blockchain: Arc<Blockchain>,
    peer_manager: Arc<PeerManager>,
    peer_registry: Arc<PeerConnectionRegistry>,
    reconnection_ai: Arc<AdaptiveReconnectionAI>,
    ip_banlist: Option<Arc<RwLock<IPBanlist>>>,
    tls_config: Option<Arc<TlsConfig>>,
    network_type: NetworkType,
    attack_detector: Option<Arc<crate::ai::attack_detector::AttackDetector>>,
    ai_system: Option<Arc<crate::ai::AISystem>>,
    relay_store: Option<Arc<crate::messaging::relay::RelayStore>>,
    relay_signing_key: Option<Arc<ed25519_dalek::SigningKey>>,
    contacts_book: Option<Arc<crate::messaging::contacts::ContactsBook>>,
}

impl ConnectionResources {
    /// Spawn a one-shot connection task for a peer.
    /// Reconnection is handled externally by the Phase 3 discovery loop (every 120s),
    /// which re-spawns tasks for any masternode still in the registry.
    fn spawn(&self, ip: String, is_masternode: bool) {
        let res = self.clone();
        let tag = if is_masternode { "[MASTERNODE]" } else { "" };
        tracing::debug!("{} spawn_connection_task called for {}", tag, ip);

        tokio::spawn(async move {
            // Whitelisted peers bypass AI cooldown — operator trust is absolute.
            // If a whitelisted node keeps failing, reconnect immediately rather
            // than letting backoff hold it offline for minutes.
            let peer_is_whitelisted = if let Some(ref bl) = res.ip_banlist {
                if let Ok(parsed) = ip.parse::<std::net::IpAddr>() {
                    bl.read().await.is_whitelisted(parsed)
                } else {
                    false
                }
            } else {
                false
            };

            if !peer_is_whitelisted {
                // Check if AI advises skipping this peer entirely
                let advice = res
                    .reconnection_ai
                    .get_reconnection_advice(&ip, is_masternode);
                if !advice.should_attempt {
                    tracing::debug!(
                        "🧠 [AI] Skipping connection to {}: {}",
                        ip,
                        advice.reasoning
                    );
                    res.connection_manager.clear_reconnecting(&ip);
                    return;
                }
            }

            let driver = crate::network::connection_driver::ConnectionDriver {
                connection_manager: res.connection_manager.clone(),
                masternode_registry: res.masternode_registry.clone(),
                blockchain: res.blockchain.clone(),
                peer_registry: res.peer_registry.clone(),
                banlist: res.ip_banlist.clone(),
                tls_config: res.tls_config.clone(),
                network_type: res.network_type,
                ai_system: res.ai_system.clone(),
                relay_store: res.relay_store.clone(),
                relay_signing_key: res.relay_signing_key.clone(),
                contacts_book: res.contacts_book.clone(),
            };

            let connect_duration: Option<std::time::Duration> =
                match driver.drive_outbound(&ip, res.port, is_masternode).await {
                    Ok(elapsed) => {
                        let connect_time = elapsed.as_millis() as u64;
                        // A session that lived < 10 s succeeded at TCP/TLS but ended almost
                        // immediately — typical of a version-mismatch flood-gate or frame-size
                        // kick.  Count as a failure so the reconnect backoff applies and we don't
                        // hammer a peer that can't stay connected at the current protocol version.
                        if elapsed < std::time::Duration::from_secs(10) {
                            res.reconnection_ai.record_connection_failure(
                                &ip,
                                is_masternode,
                                "short-lived session",
                            );
                            tracing::info!(
                                "{} Connection to {} ended quickly ({:.1}s)",
                                tag,
                                ip,
                                elapsed.as_secs_f64()
                            );
                        } else {
                            res.reconnection_ai.record_connection_success(
                                &ip,
                                is_masternode,
                                connect_time,
                            );
                            tracing::info!("{} Connection to {} ended gracefully", tag, ip);
                        }
                        Some(elapsed)
                    }
                    Err(e) => {
                        res.reconnection_ai
                            .record_connection_failure(&ip, is_masternode, &e);
                        tracing::debug!("{} Connection to {} failed: {}", tag, ip, e);
                        None
                    }
                };

            // cleanup (mark_outbound_disconnected and masternode inactive) is handled
            // inside drive_outbound; we only need AV3 recording and peer_manager eviction.
            let peer_still_connected = res.peer_registry.is_connected(&ip);

            let connection_was_live = connect_duration.is_some();
            // AV3/Coordinated disconnect: only count connections that were actually live
            // (Ok path), not failed attempts (Err path). During partition recovery a node
            // tries hundreds of masternodes in rapid succession; counting those failures
            // would flood the /16 detector and falsely block legitimate cloud-provider peers.
            // If this outbound was superseded by a live inbound replacement, the peer is
            // still connected and this is not a real disconnect event.
            if is_masternode && connection_was_live && !peer_still_connected {
                if let Some(ref ad) = res.attack_detector {
                    let ip_str = ip.split(':').next().unwrap_or(&ip);
                    ad.record_synchronized_disconnect(ip_str);
                }
            }

            // If the node was removed (Free/Handshake tier), also remove it from the
            // peer list so it doesn't re-appear as a regular peer in the Phase 3 loop.
            if is_masternode
                && !peer_still_connected
                && res.masternode_registry.get(&ip).await.is_none()
            {
                res.peer_manager.remove_peer(&ip).await;
            }
            // Task exits here. If this node is still in the registry (OnChain tier),
            // the Phase 3 loop will re-spawn a connection attempt every 120 seconds.
        });
    }
}
