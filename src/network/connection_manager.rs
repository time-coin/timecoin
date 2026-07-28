//! Connection manager for tracking peer connection state
//! Uses DashMap for lock-free concurrent access to connection states
//!
//! Phase 2.1: Enhanced with connection limits, rate limiting, and quality tracking

#![allow(dead_code)] // Public API - methods will be used by server and monitoring

use crate::network::connection_direction::ConnectionDirection;
use dashmap::DashMap;
use std::net::IpAddr;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

// Phase 2.1: Connection limits for DoS protection
// Phase 3: Masternode slot reservation
const MAX_TOTAL_CONNECTIONS: usize = 500;
const MAX_INBOUND_CONNECTIONS: usize = 250;
const MAX_OUTBOUND_CONNECTIONS: usize = 250;
const RESERVED_MASTERNODE_SLOTS: usize = 100; // Reserve slots for whitelisted masternodes
const MAX_REGULAR_PEER_CONNECTIONS: usize = 150; // Remaining slots for regular peers
const MAX_CONNECTIONS_PER_IP: usize = 3;
const CONNECTION_RATE_LIMIT_WINDOW: Duration = Duration::from_secs(60); // 1 minute
const MAX_NEW_CONNECTIONS_PER_WINDOW: usize = 25; // 25 new connections per minute
                                                  // How long to passively wait for a higher-IP peer to dial us before we give
                                                  // up on the IP-rank rule and dial them ourselves. Without this, a peer that
                                                  // outranks us but is down/firewalled/NAT'd leaves us permanently isolated
                                                  // from it — neither side ever initiates. Simultaneous-open resolution
                                                  // (`accept_inbound`'s tiebreaker) already handles the case where both sides
                                                  // end up dialing, so this fallback dial is safe.
const PASSIVE_WAIT_TIMEOUT: Duration = Duration::from_secs(180);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PeerConnectionState {
    Disconnected,
    Connecting,
    Connected,
    Reconnecting,
}

#[derive(Clone, Debug)]
struct ConnectionInfo {
    state: PeerConnectionState,
    direction: ConnectionDirection,
    /// Monotonic session id for this peer slot. Cleanup from an old task must
    /// only proceed when `generation` still matches, so a superseded outbound
    /// or replaced inbound cannot wipe a newer live session.
    generation: u64,
    connected_at: Option<Instant>,
    disconnected_at: Option<Instant>,
    connection_count: usize, // Track how many times this IP has connected
    last_message_at: Option<Instant>, // For detecting slow/unresponsive peers
    bytes_sent: u64,
    bytes_received: u64,
    messages_sent: u64,
    messages_received: u64,
    is_whitelisted: bool, // NEW: Track if this is a whitelisted masternode
}

/// Manages the lifecycle of peer connections (inbound/outbound)
pub struct ConnectionManager {
    connections: Arc<DashMap<String, ConnectionInfo>>,
    connected_count: Arc<AtomicUsize>,
    inbound_count: Arc<AtomicUsize>,
    outbound_count: Arc<AtomicUsize>,
    /// Global counter for [`ConnectionInfo::generation`] assignment.
    next_generation: AtomicU64,
    local_ip: OnceLock<String>,
    // Phase 2.1: Connection rate limiting
    recent_connections: Arc<DashMap<Instant, String>>, // timestamp -> peer_ip
    last_cleanup: Arc<std::sync::Mutex<Instant>>,
    /// Peers first observed as "Connected with no live writer" by
    /// `heal_connected_without_writers`, and when. A peer is only actually
    /// disconnected once it is *still* zombie-looking on a later confirmation
    /// pass — never on the first observation. This is what lets us say a
    /// connection is confirmed gone rather than guessed gone from one snapshot.
    zombie_since: Arc<DashMap<String, Instant>>,
    /// Peers we've been passively waiting on inbound from (IP-rank rule says
    /// they're the preferred dialer) — first-observed timestamp per peer_ip.
    /// Cleared once a connection to that peer actually succeeds.
    passive_wait_since: Arc<DashMap<String, Instant>>,
}

impl ConnectionManager {
    /// Create a new connection manager
    pub fn new() -> Self {
        Self {
            connections: Arc::new(DashMap::new()),
            connected_count: Arc::new(AtomicUsize::new(0)),
            inbound_count: Arc::new(AtomicUsize::new(0)),
            outbound_count: Arc::new(AtomicUsize::new(0)),
            next_generation: AtomicU64::new(1),
            local_ip: OnceLock::new(),
            recent_connections: Arc::new(DashMap::new()),
            last_cleanup: Arc::new(std::sync::Mutex::new(Instant::now())),
            zombie_since: Arc::new(DashMap::new()),
            passive_wait_since: Arc::new(DashMap::new()),
        }
    }

    fn alloc_generation(&self) -> u64 {
        self.next_generation.fetch_add(1, Ordering::Relaxed)
    }

    /// Current connection generation for a peer, if tracked.
    pub fn connection_generation(&self, peer_ip: &str) -> Option<u64> {
        self.connections.get(peer_ip).map(|info| info.generation)
    }

    pub fn set_local_ip(&self, ip: String) {
        let _ = self.local_ip.set(ip);
    }

    pub fn get_local_ip(&self) -> Option<String> {
        self.local_ip.get().cloned()
    }

    /// Returns the direction of an active or in-progress connection, if tracked.
    pub fn connection_direction(&self, peer_ip: &str) -> Option<ConnectionDirection> {
        self.connections.get(peer_ip).map(|info| info.direction)
    }

    /// Direction only when the peer is fully `Connected` (not Connecting/Disconnected).
    pub fn direction_if_connected(&self, peer_ip: &str) -> Option<ConnectionDirection> {
        self.connections.get(peer_ip).and_then(|info| {
            (info.state == PeerConnectionState::Connected).then_some(info.direction)
        })
    }

    /// True when our public IP ranks **above** `peer_ip` (octet/lex order).
    ///
    /// Used for simultaneous-open resolution and for who should **initiate** the
    /// outbound dial. Higher IP dials lower IP → one connection per pair with a
    /// deterministic direction (higher=outbound, lower=inbound). Without this,
    /// every node dials everyone at startup and aggressive dialers show
    /// "N out / 0 in" even when port 24000 is open.
    fn ip_ranks_above_peer(&self, peer_ip: &str) -> bool {
        if let Some(local_ip) = self.local_ip.get() {
            if let Ok(local_addr) = local_ip.parse::<IpAddr>() {
                if local_addr.is_unspecified() {
                    // Public-IP detection failed and we fell back to the listen
                    // address (0.0.0.0 / ::) — this is not a real IP to rank
                    // against peers. Treat it as unknown so we don't silently
                    // become permanently dial-passive (see full_external_address).
                    return true;
                }
                if let Ok(peer_addr) = peer_ip.parse::<IpAddr>() {
                    return match (local_addr, peer_addr) {
                        (IpAddr::V4(l), IpAddr::V4(p)) => l.octets() > p.octets(),
                        (IpAddr::V6(l), IpAddr::V6(p)) => l.octets() > p.octets(),
                        (IpAddr::V6(_), IpAddr::V4(_)) => true,
                        (IpAddr::V4(_), IpAddr::V6(_)) => false,
                    };
                }
            }
            local_ip.as_str() > peer_ip
        } else {
            // Unknown local IP — fall back to dialing (legacy behaviour).
            true
        }
    }

    fn should_keep_outbound(&self, peer_ip: &str) -> bool {
        self.ip_ranks_above_peer(peer_ip)
    }

    /// True if we should initiate an outbound dial to `peer_ip` under the
    /// higher-IP-dials-lower rule. Non-preferred side waits for inbound instead.
    pub fn is_preferred_dialer(&self, peer_ip: &str) -> bool {
        self.ip_ranks_above_peer(peer_ip)
    }

    /// True once we've been passively waiting on inbound from `peer_ip` for
    /// longer than `PASSIVE_WAIT_TIMEOUT` with no connection ever arriving.
    /// Callers should dial anyway when this returns true, overriding the
    /// IP-rank rule so a dead/unreachable higher-IP peer can't leave us
    /// permanently isolated from it. Starts the clock on first call.
    pub fn passive_wait_expired(&self, peer_ip: &str) -> bool {
        self.passive_wait_expired_after(peer_ip, PASSIVE_WAIT_TIMEOUT)
    }

    fn passive_wait_expired_after(&self, peer_ip: &str, timeout: Duration) -> bool {
        match self.passive_wait_since.get(peer_ip) {
            Some(since) => since.elapsed() >= timeout,
            None => {
                self.passive_wait_since
                    .insert(peer_ip.to_string(), Instant::now());
                false
            }
        }
    }

    /// Clear passive-wait tracking for `peer_ip`, e.g. once a connection to it
    /// actually succeeds, so a later disconnect restarts the wait from zero.
    fn clear_passive_wait(&self, peer_ip: &str) {
        self.passive_wait_since.remove(peer_ip);
    }

    fn recalculate_counts(&self) -> (usize, usize, usize) {
        self.connections.iter().fold(
            (0usize, 0usize, 0usize),
            |(connected, inbound, outbound), entry| {
                if entry.value().state != PeerConnectionState::Connected {
                    return (connected, inbound, outbound);
                }

                match entry.value().direction {
                    ConnectionDirection::Inbound => (connected + 1, inbound + 1, outbound),
                    ConnectionDirection::Outbound => (connected + 1, inbound, outbound + 1),
                }
            },
        )
    }

    fn reconcile_counts(&self) -> (usize, usize, usize) {
        let (connected, inbound, outbound) = self.recalculate_counts();
        self.connected_count.store(connected, Ordering::Relaxed);
        self.inbound_count.store(inbound, Ordering::Relaxed);
        self.outbound_count.store(outbound, Ordering::Relaxed);
        (connected, inbound, outbound)
    }

    fn decrement_counter(counter: &AtomicUsize) {
        let _ = counter.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
            Some(current.saturating_sub(1))
        });
    }

    /// Phase 2.1: Check if we can accept a new inbound connection
    /// Phase 3: Add whitelist exemption for masternodes
    pub fn can_accept_inbound(&self, peer_ip: &str, is_whitelisted: bool) -> Result<(), String> {
        let (total, inbound, _) = self.reconcile_counts();

        // Whitelisted masternodes bypass regular connection limits (but still respect total)
        if is_whitelisted {
            if total >= MAX_TOTAL_CONNECTIONS {
                return Err(format!(
                    "Max total connections reached: {}/{}",
                    total, MAX_TOTAL_CONNECTIONS
                ));
            }
            // Allow whitelisted connection - bypass all other checks
            return Ok(());
        }

        // For regular peers, enforce stricter limits
        if total >= MAX_TOTAL_CONNECTIONS {
            return Err(format!(
                "Max total connections reached: {}/{}",
                total, MAX_TOTAL_CONNECTIONS
            ));
        }

        // Check if regular peer slots are full
        let regular_count = self.count_regular_peer_connections();
        if regular_count >= MAX_REGULAR_PEER_CONNECTIONS {
            return Err(format!(
                "Max regular peer connections reached: {}/{} (reserved {} slots for masternodes)",
                regular_count, MAX_REGULAR_PEER_CONNECTIONS, RESERVED_MASTERNODE_SLOTS
            ));
        }

        // Check inbound limit
        if inbound >= MAX_INBOUND_CONNECTIONS {
            return Err(format!(
                "Max inbound connections reached: {}/{}",
                inbound, MAX_INBOUND_CONNECTIONS
            ));
        }

        // Check per-IP limit
        let ip_connections = self.count_connections_from_ip(peer_ip);
        if ip_connections >= MAX_CONNECTIONS_PER_IP {
            return Err(format!(
                "Max connections per IP reached: {}/{}",
                ip_connections, MAX_CONNECTIONS_PER_IP
            ));
        }

        // Phase 2.1: Check connection rate limit
        self.cleanup_old_connections();
        let recent_count = self.recent_connections.len();
        if recent_count >= MAX_NEW_CONNECTIONS_PER_WINDOW {
            return Err(format!(
                "Connection rate limit exceeded: {} connections in last minute",
                recent_count
            ));
        }

        Ok(())
    }

    /// Phase 2.1: Check if we can make a new outbound connection
    pub fn can_connect_outbound(&self) -> Result<(), String> {
        let (total, _, outbound) = self.reconcile_counts();

        // Check total connection limit
        if total >= MAX_TOTAL_CONNECTIONS {
            return Err(format!(
                "Max total connections reached: {}/{}",
                total, MAX_TOTAL_CONNECTIONS
            ));
        }

        // Check outbound limit
        if outbound >= MAX_OUTBOUND_CONNECTIONS {
            return Err(format!(
                "Max outbound connections reached: {}/{}",
                outbound, MAX_OUTBOUND_CONNECTIONS
            ));
        }

        Ok(())
    }

    /// Phase 2.1: Count connections from a specific IP (exact key match).
    fn count_connections_from_ip(&self, peer_ip: &str) -> usize {
        self.connections
            .get(peer_ip)
            .filter(|info| info.state == PeerConnectionState::Connected)
            .map(|_| 1)
            .unwrap_or(0)
    }

    /// Phase 3: Count regular (non-whitelisted) peer connections
    fn count_regular_peer_connections(&self) -> usize {
        self.connections
            .iter()
            .filter(|entry| {
                entry.value().state == PeerConnectionState::Connected
                    && !entry.value().is_whitelisted
            })
            .count()
    }

    /// Phase 3: Count whitelisted masternode connections
    #[allow(dead_code)]
    pub fn count_whitelisted_connections(&self) -> usize {
        self.connections
            .iter()
            .filter(|entry| {
                entry.value().state == PeerConnectionState::Connected
                    && entry.value().is_whitelisted
            })
            .count()
    }

    /// Phase 2.1: Cleanup old connection tracking entries
    fn cleanup_old_connections(&self) {
        let mut last_cleanup = self
            .last_cleanup
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let now = Instant::now();

        // Only cleanup every 10 seconds
        if now.duration_since(*last_cleanup) < Duration::from_secs(10) {
            return;
        }

        let cutoff = now - CONNECTION_RATE_LIMIT_WINDOW;
        self.recent_connections
            .retain(|timestamp, _| *timestamp > cutoff);

        *last_cleanup = now;
    }

    /// Phase 2.1: Record a new connection for rate limiting
    fn record_new_connection(&self, peer_ip: &str) {
        self.recent_connections
            .insert(Instant::now(), peer_ip.to_string());
    }

    /// Check if we're already connected to a peer
    pub fn is_connected(&self, peer_ip: &str) -> bool {
        self.connections
            .get(peer_ip)
            .map(|info| info.state == PeerConnectionState::Connected)
            .unwrap_or(false)
    }

    /// Check if a peer has any active state (connecting, connected, or reconnecting)
    pub fn is_active(&self, peer_ip: &str) -> bool {
        self.connections
            .get(peer_ip)
            .map(|info| info.state != PeerConnectionState::Disconnected)
            .unwrap_or(false)
    }

    /// True only while an outbound dial is in flight (TCP/TLS not finished yet).
    pub fn is_connecting(&self, peer_ip: &str) -> bool {
        self.connections
            .get(peer_ip)
            .map(|info| info.state == PeerConnectionState::Connecting)
            .unwrap_or(false)
    }

    /// Clear a stuck/failed Connecting slot so PHASE3 can retry.
    pub fn abort_connecting(&self, peer_ip: &str) -> bool {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            if entry.state == PeerConnectionState::Connecting {
                entry.state = PeerConnectionState::Disconnected;
                entry.disconnected_at = Some(Instant::now());
                return true;
            }
        }
        false
    }

    /// Heal zombie sessions: CM says `Connected` but there is no live writer.
    ///
    /// Without this, PHASE3 skips redial (`is_active` / `is_connected`) forever and
    /// the node can collapse from ~N peers to 1 after short-lived sessions die
    /// without a clean unregister path.
    ///
    /// A freshly `Connected` slot legitimately has no writer yet: inbound reserves
    /// the CM slot before TLS even starts (`accept_inbound`), and the writer isn't
    /// registered until TLS *and* the handshake message complete — which can take
    /// up to the 10s pre-handshake timeout in `drive_inbound`. A single snapshot
    /// comparing "Connected" against "has a live writer right now" can't tell a
    /// zombie apart from a healthy connection that's simply still mid-handshake.
    ///
    /// So this never disconnects on the first sighting. A peer is only marked
    /// "no live writer" *once*; it's actually force-disconnected only if it is
    /// **still** in that state on a later call at least [`ZOMBIE_CONFIRM_WINDOW`]
    /// after the first sighting — i.e. we confirm the connection is really gone
    /// before acting, rather than guessing from one snapshot. Peers that regain a
    /// live writer (or leave `Connected`) before confirmation are cleared and
    /// never touched.
    ///
    /// Returns the peer IPs that were force-disconnected.
    pub fn heal_connected_without_writers(
        &self,
        live_writer_ips: &std::collections::HashSet<String>,
    ) -> Vec<String> {
        const ZOMBIE_CONFIRM_WINDOW: Duration = Duration::from_secs(15);
        self.heal_connected_without_writers_with_window(live_writer_ips, ZOMBIE_CONFIRM_WINDOW)
    }

    /// Test-injectable confirmation window so unit tests don't need to sleep real time.
    fn heal_connected_without_writers_with_window(
        &self,
        live_writer_ips: &std::collections::HashSet<String>,
        confirm_window: Duration,
    ) -> Vec<String> {
        // Clear tracking for anything that recovered a writer, left Connected,
        // or was removed entirely — it no longer needs confirming.
        self.zombie_since.retain(|ip, _| {
            !live_writer_ips.contains(ip.as_str())
                && self
                    .connections
                    .get(ip)
                    .is_some_and(|info| info.state == PeerConnectionState::Connected)
        });

        let mut dead = Vec::new();
        for entry in self.connections.iter() {
            let ip = entry.key();
            if entry.value().state != PeerConnectionState::Connected
                || live_writer_ips.contains(ip.as_str())
            {
                continue;
            }

            match self.zombie_since.get(ip) {
                Some(first_seen) if first_seen.elapsed() >= confirm_window => {
                    dead.push(ip.clone());
                }
                Some(_) => {
                    // Already flagged, not old enough to confirm yet — wait.
                }
                None => {
                    // First sighting this call — flag it, don't act yet.
                    self.zombie_since.insert(ip.clone(), Instant::now());
                }
            }
        }

        for ip in &dead {
            self.mark_disconnected(ip);
            self.zombie_since.remove(ip);
        }
        dead
    }

    /// Check if we have an outbound connection to a peer
    pub fn has_outbound_connection(&self, peer_ip: &str) -> bool {
        self.connections
            .get(peer_ip)
            .map(|info| {
                info.state == PeerConnectionState::Connected
                    && info.direction == ConnectionDirection::Outbound
            })
            .unwrap_or(false)
    }

    /// Check if we should connect to a peer
    /// Returns false if already connected or currently connecting
    pub fn should_connect_to(&self, peer_ip: &str) -> bool {
        !self.connections.contains_key(peer_ip)
            || self
                .connections
                .get(peer_ip)
                .map(|info| info.state == PeerConnectionState::Disconnected)
                .unwrap_or(false)
    }

    /// Accept an inbound connection — the single authority for inbound registration.
    ///
    /// Atomically registers the peer as Connected/Inbound and returns the new
    /// session `generation` on success. Returns `None` (caller must close the
    /// socket immediately) if:
    ///   - The peer already has an incompatible active connection state.
    ///   - The connection would exceed capacity limits (unless whitelisted).
    ///
    /// This is the counterpart to `mark_connecting` for outbound. All inbound
    /// connections MUST go through this method so ConnectionManager is the
    /// single source of truth for both directions.
    ///
    /// When we already have an outbound connection to the same peer, use a
    /// deterministic IP tiebreaker: one side yields its outbound slot and
    /// accepts the inbound replacement, preventing the "both peers dial each
    /// other and both reject inbound" disconnect loop.
    ///
    /// The returned generation must be passed to [`Self::mark_inbound_disconnected`]
    /// so a superseded session cannot wipe a newer replacement.
    pub fn accept_inbound(&self, peer_ip: &str, is_whitelisted: bool) -> Option<u64> {
        use dashmap::mapref::entry::Entry;

        // Check capacity before touching the map (fast path for overload)
        if let Err(_e) = self.can_accept_inbound(peer_ip, is_whitelisted) {
            return None;
        }

        self.clear_passive_wait(peer_ip);
        let generation = self.alloc_generation();
        let new_info = ConnectionInfo {
            state: PeerConnectionState::Connected,
            direction: ConnectionDirection::Inbound,
            generation,
            connected_at: Some(Instant::now()),
            disconnected_at: None,
            connection_count: 1,
            last_message_at: Some(Instant::now()),
            bytes_sent: 0,
            bytes_received: 0,
            messages_sent: 0,
            messages_received: 0,
            is_whitelisted,
        };

        match self.connections.entry(peer_ip.to_string()) {
            Entry::Vacant(e) => {
                e.insert(new_info);
                self.record_new_connection(peer_ip);
                self.connected_count.fetch_add(1, Ordering::Relaxed);
                self.inbound_count.fetch_add(1, Ordering::Relaxed);
                Some(generation)
            }
            Entry::Occupied(mut e) => {
                if e.get().state == PeerConnectionState::Disconnected {
                    // Previously connected peer reconnecting as inbound — allow it.
                    // Disconnected state does not hold a slot in connected_count, so
                    // we only increment the counters, not decrement first.
                    e.insert(new_info);
                    self.record_new_connection(peer_ip);
                    self.connected_count.fetch_add(1, Ordering::Relaxed);
                    self.inbound_count.fetch_add(1, Ordering::Relaxed);
                    Some(generation)
                } else if e.get().direction == ConnectionDirection::Outbound {
                    // Whitelisted peers are operator-trusted: never reject their
                    // inbound for tiebreaker reasons. A stuck outbound entry must
                    // not block a fresh inbound from the operator's own node.
                    if !is_whitelisted && self.should_keep_outbound(peer_ip) {
                        tracing::debug!(
                            "🔄 Rejecting inbound from {} — keeping {:?} outbound (IP tiebreaker)",
                            peer_ip,
                            e.get().state
                        );
                        None
                    } else {
                        let was_connected = e.get().state == PeerConnectionState::Connected;
                        tracing::info!(
                            "🔄 Simultaneous connection with {} — yielding {:?} outbound and accepting inbound",
                            peer_ip,
                            e.get().state
                        );

                        if was_connected {
                            Self::decrement_counter(&self.outbound_count);
                            self.inbound_count.fetch_add(1, Ordering::Relaxed);
                        } else {
                            self.connected_count.fetch_add(1, Ordering::Relaxed);
                            self.inbound_count.fetch_add(1, Ordering::Relaxed);
                        }

                        let connection_count = e.get().connection_count.saturating_add(1);
                        e.insert(ConnectionInfo {
                            state: PeerConnectionState::Connected,
                            direction: ConnectionDirection::Inbound,
                            generation,
                            connected_at: Some(Instant::now()),
                            disconnected_at: None,
                            connection_count,
                            last_message_at: Some(Instant::now()),
                            bytes_sent: 0,
                            bytes_received: 0,
                            messages_sent: 0,
                            messages_received: 0,
                            is_whitelisted,
                        });
                        Some(generation)
                    }
                } else if is_whitelisted {
                    // Whitelisted peers must never be locked out by a stale or
                    // duplicate inbound entry. Replace the existing slot in place;
                    // the previous I/O bridge will exit when its writer is evicted
                    // and generation-mismatched cleanup is a no-op.
                    let was_connected = e.get().state == PeerConnectionState::Connected;
                    let connection_count = e.get().connection_count.saturating_add(1);
                    tracing::info!(
                        "🔄 Replacing existing inbound slot for whitelisted peer {} (prev state: {:?})",
                        peer_ip,
                        e.get().state
                    );
                    e.insert(ConnectionInfo {
                        state: PeerConnectionState::Connected,
                        direction: ConnectionDirection::Inbound,
                        generation,
                        connected_at: Some(Instant::now()),
                        disconnected_at: None,
                        connection_count,
                        last_message_at: Some(Instant::now()),
                        bytes_sent: 0,
                        bytes_received: 0,
                        messages_sent: 0,
                        messages_received: 0,
                        is_whitelisted,
                    });
                    if !was_connected {
                        self.connected_count.fetch_add(1, Ordering::Relaxed);
                        self.inbound_count.fetch_add(1, Ordering::Relaxed);
                    }
                    self.record_new_connection(peer_ip);
                    Some(generation)
                } else {
                    // Active inbound session already exists.
                    tracing::debug!(
                        "🔄 Rejecting inbound from {} — already {:?} (ConnectionManager)",
                        peer_ip,
                        e.get().state
                    );
                    None
                }
            }
        }
    }

    /// Mark a peer as connected (inbound connection). Returns session generation.
    pub fn mark_inbound(&self, peer_ip: &str) -> Option<u64> {
        self.record_new_connection(peer_ip);

        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            if entry.state == PeerConnectionState::Connecting {
                let generation = self.alloc_generation();
                entry.state = PeerConnectionState::Connected;
                entry.direction = ConnectionDirection::Inbound;
                entry.generation = generation;
                entry.connected_at = Some(Instant::now());
                entry.connection_count += 1;

                self.connected_count.fetch_add(1, Ordering::Relaxed);
                self.inbound_count.fetch_add(1, Ordering::Relaxed);
                Some(generation)
            } else {
                None
            }
        } else {
            let generation = self.alloc_generation();
            let info = ConnectionInfo {
                state: PeerConnectionState::Connected,
                direction: ConnectionDirection::Inbound,
                generation,
                connected_at: Some(Instant::now()),
                disconnected_at: None,
                connection_count: 1,
                last_message_at: Some(Instant::now()),
                bytes_sent: 0,
                bytes_received: 0,
                messages_sent: 0,
                messages_received: 0,
                is_whitelisted: false,
            };
            self.connections.insert(peer_ip.to_string(), info);
            self.connected_count.fetch_add(1, Ordering::Relaxed);
            self.inbound_count.fetch_add(1, Ordering::Relaxed);
            Some(generation)
        }
    }

    /// Mark an inbound connection as disconnected **only if** `generation` still
    /// owns the slot. Returns `false` when a newer session has replaced this one.
    pub fn mark_inbound_disconnected(&self, peer_ip: &str, generation: u64) -> bool {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            if entry.generation != generation {
                return false;
            }
            if entry.state == PeerConnectionState::Connected {
                entry.state = PeerConnectionState::Disconnected;
                entry.disconnected_at = Some(Instant::now());

                Self::decrement_counter(&self.connected_count);

                if entry.direction == ConnectionDirection::Inbound {
                    Self::decrement_counter(&self.inbound_count);
                }
                return true;
            }
        }
        false
    }

    /// Mark a peer as being attempted for connection
    pub fn mark_connecting(&self, peer_ip: &str) -> bool {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            // Allow dial from Disconnected or Reconnecting. Refuse Connected
            // (live or zombie — zombies are healed before PHASE3 dials) and
            // Connecting (dial already in flight).
            match entry.state {
                PeerConnectionState::Disconnected | PeerConnectionState::Reconnecting => {
                    entry.state = PeerConnectionState::Connecting;
                    entry.direction = ConnectionDirection::Outbound;
                    entry.generation = self.alloc_generation();
                    entry.last_message_at = Some(Instant::now());
                    true
                }
                _ => false,
            }
        } else {
            let info = ConnectionInfo {
                state: PeerConnectionState::Connecting,
                direction: ConnectionDirection::Outbound,
                generation: self.alloc_generation(),
                connected_at: None,
                disconnected_at: None,
                connection_count: 0,
                last_message_at: Some(Instant::now()), // Track when connecting started
                bytes_sent: 0,
                bytes_received: 0,
                messages_sent: 0,
                messages_received: 0,
                is_whitelisted: false,
            };
            self.connections.insert(peer_ip.to_string(), info);
            true
        }
    }

    /// Mark a connection attempt as successfully connected.
    ///
    /// Returns the session generation on success. Returns `None` if the peer is
    /// no longer in `Connecting` (e.g. superseded by an inbound accept) — the
    /// outbound task must abort without touching registry/MN state.
    pub fn mark_connected(&self, peer_ip: &str) -> Option<u64> {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            if entry.state == PeerConnectionState::Connecting {
                self.clear_passive_wait(peer_ip);
                let generation = self.alloc_generation();
                entry.state = PeerConnectionState::Connected;
                entry.generation = generation;
                entry.connected_at = Some(Instant::now());
                entry.last_message_at = Some(Instant::now());
                entry.connection_count += 1;

                self.connected_count.fetch_add(1, Ordering::Relaxed);

                if entry.direction == ConnectionDirection::Outbound {
                    self.outbound_count.fetch_add(1, Ordering::Relaxed);
                }
                Some(generation)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Mark a connection as failed and retry later with backoff
    pub fn mark_failed(&self, peer_ip: &str) -> bool {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            entry.state = PeerConnectionState::Reconnecting;
            entry.disconnected_at = Some(Instant::now());
            true
        } else {
            let info = ConnectionInfo {
                state: PeerConnectionState::Reconnecting,
                direction: ConnectionDirection::Outbound,
                generation: self.alloc_generation(),
                connected_at: None,
                disconnected_at: Some(Instant::now()),
                connection_count: 0,
                last_message_at: None,
                bytes_sent: 0,
                bytes_received: 0,
                messages_sent: 0,
                messages_received: 0,
                is_whitelisted: false,
            };
            self.connections.insert(peer_ip.to_string(), info);
            true
        }
    }

    /// Remove a peer from tracking (cleanup)
    pub fn remove(&self, peer_ip: &str) {
        if let Some((_, info)) = self.connections.remove(peer_ip) {
            if info.state == PeerConnectionState::Connected {
                Self::decrement_counter(&self.connected_count);

                match info.direction {
                    ConnectionDirection::Inbound => {
                        Self::decrement_counter(&self.inbound_count);
                    }
                    ConnectionDirection::Outbound => {
                        Self::decrement_counter(&self.outbound_count);
                    }
                }
            }
        }
    }

    /// Get count of connected peers
    pub fn connected_count(&self) -> usize {
        self.reconcile_counts().0
    }

    /// Phase 2.1: Get inbound connection count
    pub fn inbound_count(&self) -> usize {
        self.reconcile_counts().1
    }

    /// Phase 2.1: Get outbound connection count
    pub fn outbound_count(&self) -> usize {
        self.reconcile_counts().2
    }

    /// Check if a peer is in reconnecting state
    pub fn is_reconnecting(&self, peer_ip: &str) -> bool {
        self.connections
            .get(peer_ip)
            .map(|info| info.state == PeerConnectionState::Reconnecting)
            .unwrap_or(false)
    }

    /// Mark a peer as disconnected
    pub fn mark_disconnected(&self, peer_ip: &str) {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            if entry.state == PeerConnectionState::Connected {
                Self::decrement_counter(&self.connected_count);

                match entry.direction {
                    ConnectionDirection::Inbound => {
                        Self::decrement_counter(&self.inbound_count);
                    }
                    ConnectionDirection::Outbound => {
                        Self::decrement_counter(&self.outbound_count);
                    }
                }
            }
            entry.state = PeerConnectionState::Disconnected;
            entry.disconnected_at = Some(Instant::now());
        }
    }

    /// Mark an outbound connection as disconnected, but only if the current entry
    /// still represents **this** outbound session (`generation` match + Outbound).
    ///
    /// This prevents a late-closing outbound task from wiping out a newer inbound
    /// replacement for the same peer, which would otherwise trigger unnecessary
    /// reconnect churn.
    pub fn mark_outbound_disconnected(&self, peer_ip: &str, generation: u64) -> bool {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            if entry.direction != ConnectionDirection::Outbound {
                return false;
            }
            if entry.generation != generation {
                return false;
            }

            if entry.state == PeerConnectionState::Connected {
                Self::decrement_counter(&self.connected_count);
                Self::decrement_counter(&self.outbound_count);
            }

            entry.state = PeerConnectionState::Disconnected;
            entry.disconnected_at = Some(Instant::now());
            return true;
        }

        false
    }

    /// Clear reconnecting state for a peer (allow immediate retry)
    pub fn clear_reconnecting(&self, peer_ip: &str) {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            if entry.state == PeerConnectionState::Reconnecting {
                entry.state = PeerConnectionState::Disconnected;
            }
        }
    }

    /// Phase 3: Mark a connection as whitelisted (trusted masternode)
    pub fn mark_whitelisted(&self, peer_ip: &str) {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            entry.is_whitelisted = true;
        }
    }

    /// Phase 3: Check if a peer is marked as whitelisted
    pub fn is_whitelisted(&self, peer_ip: &str) -> bool {
        self.connections
            .get(peer_ip)
            .map(|entry| entry.is_whitelisted)
            .unwrap_or(false)
    }

    /// Phase 2: Check if peer should be protected from disconnection (whitelisted)
    pub fn should_protect(&self, peer_ip: &str) -> bool {
        self.is_whitelisted(peer_ip)
    }

    /// Mark a peer as reconnecting (with retry logic)
    pub fn mark_reconnecting(
        &self,
        peer_ip: &str,
        _retry_delay: std::time::Duration,
        _consecutive_failures: u32,
    ) {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            entry.state = PeerConnectionState::Reconnecting;
        }
    }

    /// Get list of currently connected peers
    pub fn get_connected_peers(&self) -> Vec<String> {
        self.connections
            .iter()
            .filter(|entry| entry.value().state == PeerConnectionState::Connected)
            .map(|entry| entry.key().clone())
            .collect()
    }

    /// Get list of peers currently being connected to
    pub fn get_connecting_peers(&self) -> Vec<String> {
        self.connections
            .iter()
            .filter(|entry| entry.value().state == PeerConnectionState::Connecting)
            .map(|entry| entry.key().clone())
            .collect()
    }

    /// Reset peers stuck in Connecting state for longer than the timeout.
    /// Only resets Connecting (stuck TCP handshakes), NOT Reconnecting
    /// (intentional AI-managed delays that may legitimately last minutes).
    /// Returns the number of peers reset to Disconnected.
    pub fn cleanup_stale_connecting(&self, timeout: Duration) -> usize {
        let now = Instant::now();
        let mut cleaned = 0;
        for mut entry in self.connections.iter_mut() {
            let key = entry.key().clone();
            let info = entry.value_mut();
            if info.state == PeerConnectionState::Connecting {
                let started = info.last_message_at.unwrap_or(now);
                if now.duration_since(started) > timeout {
                    tracing::debug!("🧹 Resetting stale {:?} state for peer {}", info.state, key);
                    info.state = PeerConnectionState::Disconnected;
                    info.disconnected_at = Some(now);
                    cleaned += 1;
                }
            }
        }
        cleaned
    }

    /// How long ago this peer disconnected. Returns None if no disconnect time is recorded.
    pub fn time_since_disconnect(&self, peer_ip: &str) -> Option<Duration> {
        self.connections
            .get(peer_ip)
            .and_then(|info| info.disconnected_at)
            .map(|t| t.elapsed())
    }

    /// Phase 2.1: Update activity timestamp for a peer (for detecting slow/unresponsive)
    pub fn record_activity(&self, peer_ip: &str) {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            entry.last_message_at = Some(Instant::now());
        }
    }

    /// Phase 2.1: Check for slow/unresponsive peers (no activity in 5 minutes)
    pub fn get_unresponsive_peers(&self, timeout: Duration) -> Vec<String> {
        let now = Instant::now();
        self.connections
            .iter()
            .filter(|entry| {
                entry.value().state == PeerConnectionState::Connected
                    && entry
                        .value()
                        .last_message_at
                        .map(|last| now.duration_since(last) > timeout)
                        .unwrap_or(false)
            })
            .map(|entry| entry.key().clone())
            .collect()
    }

    /// Phase 2.1: Get connection quality metrics for a peer
    pub fn get_connection_quality(&self, peer_ip: &str) -> Option<ConnectionQuality> {
        self.connections.get(peer_ip).map(|info| {
            let uptime = info
                .connected_at
                .map(|connected| Instant::now().duration_since(connected))
                .unwrap_or(Duration::from_secs(0));

            let messages_per_sec = if uptime.as_secs() > 0 {
                (info.messages_received + info.messages_sent) as f64 / uptime.as_secs() as f64
            } else {
                0.0
            };

            ConnectionQuality {
                uptime,
                connection_count: info.connection_count,
                messages_per_sec,
                bytes_sent: info.bytes_sent,
                bytes_received: info.bytes_received,
            }
        })
    }
}

/// Phase 2.1: Connection quality metrics
#[derive(Debug, Clone)]
pub struct ConnectionQuality {
    pub uptime: Duration,
    pub connection_count: usize,
    pub messages_per_sec: f64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
}

impl ConnectionManager {
    /// Update whitelist status for a specific peer
    /// Call this when masternode registry changes
    pub fn update_whitelist_status(&self, peer_ip: &str, is_whitelisted: bool) {
        if let Some(mut entry) = self.connections.get_mut(peer_ip) {
            let old_status = entry.is_whitelisted;
            entry.is_whitelisted = is_whitelisted;

            if old_status != is_whitelisted {
                tracing::info!(
                    "🔄 Updated whitelist status for {}: {} → {}",
                    peer_ip,
                    old_status,
                    is_whitelisted
                );
            }
        }
    }

    /// Bulk sync whitelist status from masternode registry
    /// Call this periodically or when masternode set changes
    ///
    /// # Arguments
    /// * `masternode_ips` - List of current masternode IP addresses
    pub fn sync_whitelist_from_registry(&self, masternode_ips: &[String]) {
        use std::collections::HashSet;

        let whitelist_set: HashSet<_> = masternode_ips.iter().map(|s| s.as_str()).collect();
        let mut updated_count = 0;

        for mut entry in self.connections.iter_mut() {
            let ip = entry.key().as_str();
            let should_be_whitelisted = whitelist_set.contains(ip);

            if entry.is_whitelisted != should_be_whitelisted {
                entry.is_whitelisted = should_be_whitelisted;
                updated_count += 1;
            }
        }

        if updated_count > 0 {
            tracing::info!(
                "🔄 Synced whitelist status: updated {} connections from masternode registry",
                updated_count
            );
        }
    }
}

impl Default for ConnectionManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accept_inbound_yields_outbound_when_local_ip_is_lower() {
        let manager = ConnectionManager::new();
        manager.set_local_ip("10.0.0.1".to_string());

        assert!(manager.mark_connecting("10.0.0.2"));
        let out_gen = manager.mark_connected("10.0.0.2").expect("outbound gen");
        let in_gen = manager
            .accept_inbound("10.0.0.2", true)
            .expect("inbound accepted");
        assert_ne!(out_gen, in_gen);

        let entry = manager.connections.get("10.0.0.2").unwrap();
        assert_eq!(entry.direction, ConnectionDirection::Inbound);
        assert_eq!(entry.state, PeerConnectionState::Connected);
        assert_eq!(entry.generation, in_gen);
        assert!(entry.is_whitelisted);
        drop(entry);
        assert_eq!(manager.connected_count(), 1);
        assert_eq!(manager.outbound_count(), 0);
        assert_eq!(manager.inbound_count(), 1);

        // Superseded outbound cleanup must not wipe the new inbound slot.
        assert!(!manager.mark_outbound_disconnected("10.0.0.2", out_gen));
        assert_eq!(manager.connected_count(), 1);
        assert_eq!(manager.inbound_count(), 1);
    }

    #[test]
    fn accept_inbound_rejects_when_local_ip_should_keep_outbound() {
        let manager = ConnectionManager::new();
        manager.set_local_ip("10.0.0.9".to_string());

        assert!(manager.mark_connecting("10.0.0.2"));
        let out_gen = manager.mark_connected("10.0.0.2").expect("outbound gen");
        assert!(manager.accept_inbound("10.0.0.2", false).is_none());

        let entry = manager.connections.get("10.0.0.2").unwrap();
        assert_eq!(entry.direction, ConnectionDirection::Outbound);
        assert_eq!(entry.state, PeerConnectionState::Connected);
        assert_eq!(entry.generation, out_gen);
        drop(entry);
        assert_eq!(manager.connected_count(), 1);
        assert_eq!(manager.outbound_count(), 1);
        assert_eq!(manager.inbound_count(), 0);
    }

    #[test]
    fn accept_inbound_replaces_connecting_outbound_without_underflow() {
        let manager = ConnectionManager::new();
        manager.set_local_ip("10.0.0.1".to_string());

        assert!(manager.mark_connecting("10.0.0.2"));
        let in_gen = manager
            .accept_inbound("10.0.0.2", true)
            .expect("inbound accepted");

        let entry = manager.connections.get("10.0.0.2").unwrap();
        assert_eq!(entry.direction, ConnectionDirection::Inbound);
        assert_eq!(entry.state, PeerConnectionState::Connected);
        assert_eq!(entry.generation, in_gen);
        drop(entry);
        assert_eq!(manager.connected_count(), 1);
        assert_eq!(manager.outbound_count(), 0);
        assert_eq!(manager.inbound_count(), 1);

        assert!(manager.mark_inbound_disconnected("10.0.0.2", in_gen));
        assert_eq!(manager.connected_count(), 0);
        assert_eq!(manager.outbound_count(), 0);
        assert_eq!(manager.inbound_count(), 0);
    }

    #[test]
    fn stale_inbound_cleanup_does_not_clear_replacement() {
        let manager = ConnectionManager::new();
        manager.set_local_ip("10.0.0.1".to_string());

        let gen1 = manager
            .accept_inbound("10.0.0.2", true)
            .expect("first inbound");
        let gen2 = manager
            .accept_inbound("10.0.0.2", true)
            .expect("whitelisted replace");
        assert_ne!(gen1, gen2);

        assert!(!manager.mark_inbound_disconnected("10.0.0.2", gen1));
        assert_eq!(manager.connected_count(), 1);
        assert_eq!(manager.inbound_count(), 1);

        assert!(manager.mark_inbound_disconnected("10.0.0.2", gen2));
        assert_eq!(manager.connected_count(), 0);
        assert_eq!(manager.inbound_count(), 0);
    }

    #[test]
    fn count_getters_reconcile_corrupted_counters() {
        let manager = ConnectionManager::new();
        manager
            .connected_count
            .store(usize::MAX - 4, Ordering::Relaxed);
        manager
            .inbound_count
            .store(usize::MAX - 5, Ordering::Relaxed);
        manager
            .outbound_count
            .store(usize::MAX - 6, Ordering::Relaxed);

        assert_eq!(manager.connected_count(), 0);
        assert_eq!(manager.inbound_count(), 0);
        assert_eq!(manager.outbound_count(), 0);
        assert!(manager.can_accept_inbound("10.0.0.2", false).is_ok());
    }

    #[test]
    fn count_connections_from_ip_is_exact_match() {
        let manager = ConnectionManager::new();
        assert!(manager.mark_connecting("10.0.0.10"));
        assert!(manager.mark_connected("10.0.0.10").is_some());
        // Prefix of a real peer key must not count as a hit.
        assert_eq!(manager.count_connections_from_ip("10.0.0.1"), 0);
        assert_eq!(manager.count_connections_from_ip("10.0.0.10"), 1);
    }

    #[test]
    fn inbound_reservation_blocks_outbound_dial_race() {
        // Simulates reserving inbound before TLS completes: PHASE3 must not
        // be able to mark_connecting the same peer and flip the session.
        let manager = ConnectionManager::new();
        manager.set_local_ip("10.0.0.9".to_string()); // would prefer outbound via tiebreaker

        let in_gen = manager
            .accept_inbound("10.0.0.2", false)
            .expect("inbound reserved");
        assert!(manager.is_active("10.0.0.2"));
        assert!(manager.is_connected("10.0.0.2"));
        assert!(!manager.mark_connecting("10.0.0.2"));
        assert!(manager.mark_connected("10.0.0.2").is_none());

        let entry = manager.connections.get("10.0.0.2").unwrap();
        assert_eq!(entry.direction, ConnectionDirection::Inbound);
        assert_eq!(entry.generation, in_gen);
        drop(entry);
        assert_eq!(manager.inbound_count(), 1);
        assert_eq!(manager.outbound_count(), 0);
    }

    #[test]
    fn preferred_dialer_is_higher_ip() {
        let manager = ConnectionManager::new();
        manager.set_local_ip("10.0.0.9".to_string());
        assert!(manager.is_preferred_dialer("10.0.0.2"));
        assert!(!manager.is_preferred_dialer("10.0.0.20"));
    }

    #[test]
    fn preferred_dialer_falls_back_to_dialing_on_unspecified_local_ip() {
        // Regression: full_external_address() falls back to the listen address
        // (0.0.0.0) when public-IP auto-detection fails and no externalip= is
        // configured. That must not make us permanently dial-passive against
        // every peer — treat it like an unknown local IP and keep dialing.
        let manager = ConnectionManager::new();
        manager.set_local_ip("0.0.0.0".to_string());
        assert!(manager.is_preferred_dialer("10.0.0.2"));
        assert!(manager.is_preferred_dialer("255.255.255.255"));
    }

    #[test]
    fn passive_wait_expires_and_forces_dial() {
        // Lower-IP side must eventually give up waiting for inbound from an
        // unreachable higher-IP peer and dial it anyway.
        let manager = ConnectionManager::new();
        manager.set_local_ip("10.0.0.2".to_string());
        assert!(!manager.is_preferred_dialer("10.0.0.9"));

        // First observation just starts the clock — not expired yet.
        assert!(!manager.passive_wait_expired_after("10.0.0.9", Duration::from_millis(20)));
        std::thread::sleep(Duration::from_millis(30));
        assert!(manager.passive_wait_expired_after("10.0.0.9", Duration::from_millis(20)));
    }

    #[test]
    fn passive_wait_clears_on_successful_connection() {
        // Once a connection actually succeeds, the wait clock resets so a
        // later disconnect doesn't inherit stale elapsed time.
        let manager = ConnectionManager::new();
        manager.set_local_ip("10.0.0.2".to_string());
        assert!(!manager.passive_wait_expired_after("10.0.0.9", Duration::from_millis(10)));
        std::thread::sleep(Duration::from_millis(20));

        // Inbound arrives from the higher-IP peer before the timeout check runs again.
        assert!(manager.accept_inbound("10.0.0.9", false).is_some());
        assert!(!manager.passive_wait_since.contains_key("10.0.0.9"));

        // Freshly re-seeded clock must not be considered expired immediately.
        assert!(!manager.passive_wait_expired_after("10.0.0.9", Duration::from_millis(10)));
    }

    #[test]
    fn heal_connected_without_writers_requires_two_confirmations() {
        let manager = ConnectionManager::new();
        assert!(manager.mark_connecting("10.0.0.2"));
        assert!(manager.mark_connected("10.0.0.2").is_some());
        assert!(manager.mark_connecting("10.0.0.3"));
        assert!(manager.mark_connected("10.0.0.3").is_some());
        assert_eq!(manager.connected_count(), 2);

        // Only 10.0.0.2 still has a "live writer".
        let mut live = std::collections::HashSet::new();
        live.insert("10.0.0.2".to_string());

        // First sighting of 10.0.0.3 as a zombie: flagged, but NOT disconnected —
        // we don't act on a single snapshot.
        let healed =
            manager.heal_connected_without_writers_with_window(&live, Duration::from_secs(0));
        assert!(healed.is_empty());
        assert!(manager.is_connected("10.0.0.3"));

        // Second sighting (confirm_window=0 so it's immediately "old enough"):
        // now it's confirmed still gone, so it gets disconnected.
        let healed =
            manager.heal_connected_without_writers_with_window(&live, Duration::from_secs(0));
        assert_eq!(healed, vec!["10.0.0.3".to_string()]);
        assert!(manager.is_connected("10.0.0.2"));
        assert!(!manager.is_connected("10.0.0.3"));
        assert_eq!(manager.connected_count(), 1);
        // Can redial the healed peer
        assert!(manager.mark_connecting("10.0.0.3"));
    }

    #[test]
    fn heal_connected_without_writers_spares_fresh_handshakes() {
        // Regression test: inbound reserves the CM slot before TLS even starts
        // (accept_inbound), and the writer isn't registered until TLS *and* the
        // handshake message complete — up to the 10s pre-handshake timeout in
        // drive_inbound. A single-snapshot heal pass would kill that connection
        // while it's still legitimately mid-handshake.
        let manager = ConnectionManager::new();
        let gen = manager
            .accept_inbound("10.0.0.2", false)
            .expect("inbound reserved");
        assert!(manager.is_connected("10.0.0.2"));

        // No live writer yet (handshake still in flight) — first sighting must
        // only flag, never disconnect, regardless of window length.
        let live = std::collections::HashSet::new();
        let healed =
            manager.heal_connected_without_writers_with_window(&live, Duration::from_secs(15));
        assert!(healed.is_empty());
        assert!(manager.is_connected("10.0.0.2"));

        // Handshake completes and registers a writer before the next heal tick —
        // the flag must be cleared so it's never disconnected later.
        let mut live = std::collections::HashSet::new();
        live.insert("10.0.0.2".to_string());
        let healed =
            manager.heal_connected_without_writers_with_window(&live, Duration::from_secs(0));
        assert!(healed.is_empty());
        assert!(manager.is_connected("10.0.0.2"));

        // The in-flight handshake can still complete normally afterwards.
        assert!(manager.mark_inbound_disconnected("10.0.0.2", gen));
    }
}
