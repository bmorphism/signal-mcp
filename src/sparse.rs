//! Sparse Capabilities: shun what you don't need, regret what you shouldn't have done
//!
//! Mode collapse for capabilities: O(n) trait enumeration → O(1) sparse signature
//!
//! # The Shunning Pattern
//!
//! Instead of positive capabilities (has X), we track negative bounds (shuns X).
//! An entity that shuns Colorable cannot be colored.
//! An entity that shuns Sendable cannot cross thread boundaries.
//!
//! # Regret
//!
//! Capabilities are reversible. Regret undoes capability grants.
//! The regret log enables time-travel debugging of capability flow.
//!
//! # Sparsity
//!
//! Most entities need few capabilities. Sparse representation:
//! - Default: shuns everything
//! - Grant: un-shun specific capabilities
//! - Regret: re-shun (revoke) capabilities

use crate::gay_loom::{GayRNG, ZXColor, ColorSignature};
use crate::gay_bridge::GAY_SEED;
use std::collections::{HashSet, VecDeque};

/// Capability types that can be shunned
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Capability {
    Colorable,   // Can receive ZXColor assignment
    Iterable,    // Can be traversed
    Sendable,    // Can cross thread boundaries (like Rust Send)
    Receivable,  // Can accept incoming messages
    Findable,    // Can be located/indexed
    Reachable,   // Can be reached from other entities
}

impl Capability {
    pub const ALL: [Capability; 6] = [
        Capability::Colorable,
        Capability::Iterable,
        Capability::Sendable,
        Capability::Receivable,
        Capability::Findable,
        Capability::Reachable,
    ];
    
    /// Color encoding for capability (for chromatic verification)
    pub fn color(&self) -> ZXColor {
        match self {
            Capability::Colorable => ZXColor::Green,
            Capability::Iterable => ZXColor::Red,
            Capability::Sendable => ZXColor::Green,
            Capability::Receivable => ZXColor::Red,
            Capability::Findable => ZXColor::Green,
            Capability::Reachable => ZXColor::Red,
        }
    }
    
    /// Bit position for sparse encoding
    pub fn bit(&self) -> u8 {
        match self {
            Capability::Colorable => 0,
            Capability::Iterable => 1,
            Capability::Sendable => 2,
            Capability::Receivable => 3,
            Capability::Findable => 4,
            Capability::Reachable => 5,
        }
    }
}

/// Sparse capability set: only track what's NOT shunned
#[derive(Clone, Debug, Default)]
pub struct SparseCapabilities {
    /// Capabilities that are NOT shunned (granted)
    granted: HashSet<Capability>,
    /// Fingerprint for O(1) comparison
    fingerprint: u64,
}

impl SparseCapabilities {
    /// New entity: shuns everything by default
    pub fn new() -> Self {
        Self {
            granted: HashSet::new(),
            fingerprint: 0,
        }
    }
    
    /// Full capabilities: shuns nothing
    pub fn full() -> Self {
        let mut caps = Self::new();
        for cap in Capability::ALL {
            caps.grant(cap);
        }
        caps
    }
    
    /// Grant a capability (un-shun)
    pub fn grant(&mut self, cap: Capability) {
        self.granted.insert(cap);
        self.fingerprint |= 1 << cap.bit();
    }
    
    /// Shun a capability (revoke)
    pub fn shun(&mut self, cap: Capability) {
        self.granted.remove(&cap);
        self.fingerprint &= !(1 << cap.bit());
    }
    
    /// Check if capability is shunned
    pub fn shuns(&self, cap: Capability) -> bool {
        !self.granted.contains(&cap)
    }
    
    /// Check if capability is granted (not shunned)
    pub fn has(&self, cap: Capability) -> bool {
        self.granted.contains(&cap)
    }
    
    /// Sparse size: number of granted capabilities
    pub fn density(&self) -> usize {
        self.granted.len()
    }
    
    /// Sparsity ratio: 1.0 = all shunned, 0.0 = nothing shunned
    pub fn sparsity(&self) -> f64 {
        1.0 - (self.granted.len() as f64 / Capability::ALL.len() as f64)
    }
    
    /// O(1) fingerprint comparison
    pub fn fingerprint(&self) -> u64 {
        self.fingerprint
    }
    
    /// Color signature of capabilities
    pub fn color_signature(&self) -> ColorSignature {
        let colors: Vec<_> = Capability::ALL.iter()
            .filter(|c| self.has(**c))
            .map(|c| c.color())
            .collect();
        ColorSignature::from_trace(&colors)
    }
    
    /// Intersection: capabilities both have
    pub fn intersect(&self, other: &Self) -> Self {
        let mut result = Self::new();
        for cap in &self.granted {
            if other.has(*cap) {
                result.grant(*cap);
            }
        }
        result
    }
    
    /// Union: capabilities either has
    pub fn union(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for cap in &other.granted {
            result.grant(*cap);
        }
        result
    }
}

/// Regret entry: a capability change that can be undone
#[derive(Clone, Debug)]
pub struct RegretEntry {
    pub timestamp: u64,
    pub capability: Capability,
    pub action: RegretAction,
    pub reason: String,
    pub color_before: ZXColor,
    pub color_after: ZXColor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegretAction {
    Granted,  // Capability was granted (can regret by shunning)
    Shunned,  // Capability was shunned (can regret by granting)
}

/// Regrettable capability holder: tracks history for undo
#[derive(Clone, Debug)]
pub struct Regrettable {
    pub id: String,
    pub capabilities: SparseCapabilities,
    pub regret_log: VecDeque<RegretEntry>,
    pub regret_limit: usize,
    pub rng: GayRNG,
    timestamp: u64,
}

impl Regrettable {
    pub fn new(id: &str, seed: u64) -> Self {
        Self {
            id: id.to_string(),
            capabilities: SparseCapabilities::new(),
            regret_log: VecDeque::new(),
            regret_limit: 100,
            rng: GayRNG::new(seed),
            timestamp: 0,
        }
    }
    
    /// Grant with regret tracking
    pub fn grant(&mut self, cap: Capability, reason: &str) {
        let color_before = self.color_parity();
        self.capabilities.grant(cap);
        let color_after = self.color_parity();
        
        self.timestamp += 1;
        self.regret_log.push_back(RegretEntry {
            timestamp: self.timestamp,
            capability: cap,
            action: RegretAction::Granted,
            reason: reason.to_string(),
            color_before,
            color_after,
        });
        
        if self.regret_log.len() > self.regret_limit {
            self.regret_log.pop_front();
        }
    }
    
    /// Shun with regret tracking
    pub fn shun(&mut self, cap: Capability, reason: &str) {
        let color_before = self.color_parity();
        self.capabilities.shun(cap);
        let color_after = self.color_parity();
        
        self.timestamp += 1;
        self.regret_log.push_back(RegretEntry {
            timestamp: self.timestamp,
            capability: cap,
            action: RegretAction::Shunned,
            reason: reason.to_string(),
            color_before,
            color_after,
        });
        
        if self.regret_log.len() > self.regret_limit {
            self.regret_log.pop_front();
        }
    }
    
    /// Regret: undo the last capability change
    pub fn regret(&mut self) -> Option<RegretEntry> {
        let entry = self.regret_log.pop_back()?;
        
        // Undo the action
        match entry.action {
            RegretAction::Granted => self.capabilities.shun(entry.capability),
            RegretAction::Shunned => self.capabilities.grant(entry.capability),
        }
        
        Some(entry)
    }
    
    /// Regret until color parity matches target
    pub fn regret_until_color(&mut self, target: ZXColor) -> Vec<RegretEntry> {
        let mut undone = Vec::new();
        
        while self.color_parity() != target {
            if let Some(entry) = self.regret() {
                undone.push(entry);
            } else {
                break;
            }
        }
        
        undone
    }
    
    /// Current color parity of capabilities
    pub fn color_parity(&self) -> ZXColor {
        let sig = self.capabilities.color_signature();
        sig.parity
    }
    
    /// Check if regret log shows color conservation
    pub fn color_conserved(&self) -> bool {
        if self.regret_log.len() < 2 {
            return true;
        }
        
        // Check that color changes alternate (conservation under flip)
        let colors: Vec<_> = self.regret_log.iter()
            .map(|e| e.color_after)
            .collect();
        
        // Count transitions
        let transitions: usize = colors.windows(2)
            .filter(|w| w[0] != w[1])
            .count();
        
        // Conserved if transitions are balanced
        transitions <= self.regret_log.len() / 2 + 1
    }
}

/// Sparse capability graph: entities with capability relationships
#[derive(Clone, Debug)]
pub struct SparseCapabilityGraph {
    pub entities: Vec<Regrettable>,
    /// Edge exists if source can reach dest (both have Reachable or source has Sendable + dest has Receivable)
    pub edges: Vec<(usize, usize)>,
    pub rng: GayRNG,
}

impl SparseCapabilityGraph {
    pub fn new(seed: u64) -> Self {
        Self {
            entities: Vec::new(),
            edges: Vec::new(),
            rng: GayRNG::new(seed),
        }
    }
    
    /// Add entity with sparse capabilities
    pub fn add_entity(&mut self, id: &str) -> usize {
        let seed = self.rng.split();
        let entity = Regrettable::new(id, seed);
        let idx = self.entities.len();
        self.entities.push(entity);
        idx
    }
    
    /// Check if edge is valid based on capabilities
    pub fn edge_valid(&self, from: usize, to: usize) -> bool {
        let src = &self.entities[from].capabilities;
        let dst = &self.entities[to].capabilities;
        
        // Source must be able to send or be reachable
        let src_can_send = src.has(Capability::Sendable) || src.has(Capability::Reachable);
        // Destination must be able to receive or be findable
        let dst_can_recv = dst.has(Capability::Receivable) || dst.has(Capability::Findable);
        
        src_can_send && dst_can_recv
    }
    
    /// Add edge if valid
    pub fn add_edge(&mut self, from: usize, to: usize) -> bool {
        if self.edge_valid(from, to) {
            self.edges.push((from, to));
            true
        } else {
            false
        }
    }
    
    /// Find reachable entities from source (respecting capabilities)
    pub fn reachable_from(&self, source: usize) -> Vec<usize> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(source);
        
        while let Some(current) = queue.pop_front() {
            if visited.contains(&current) {
                continue;
            }
            visited.insert(current);
            
            for &(from, to) in &self.edges {
                if from == current && !visited.contains(&to) {
                    if self.edge_valid(from, to) {
                        queue.push_back(to);
                    }
                }
            }
        }
        
        visited.into_iter().collect()
    }
    
    /// Overall sparsity of the graph
    pub fn graph_sparsity(&self) -> f64 {
        if self.entities.is_empty() {
            return 1.0;
        }
        
        let total_sparsity: f64 = self.entities.iter()
            .map(|e| e.capabilities.sparsity())
            .sum();
        total_sparsity / self.entities.len() as f64
    }
    
    /// Color signature of entire graph
    pub fn graph_signature(&self) -> ColorSignature {
        let colors: Vec<_> = self.entities.iter()
            .map(|e| e.color_parity())
            .collect();
        ColorSignature::from_trace(&colors)
    }
}

/// Capability requirement: what's needed vs what's shunned
#[derive(Clone, Debug)]
pub struct CapabilityRequirement {
    pub required: HashSet<Capability>,
    pub forbidden: HashSet<Capability>,
}

impl CapabilityRequirement {
    pub fn new() -> Self {
        Self {
            required: HashSet::new(),
            forbidden: HashSet::new(),
        }
    }
    
    pub fn require(&mut self, cap: Capability) -> &mut Self {
        self.required.insert(cap);
        self.forbidden.remove(&cap);
        self
    }
    
    pub fn forbid(&mut self, cap: Capability) -> &mut Self {
        self.forbidden.insert(cap);
        self.required.remove(&cap);
        self
    }
    
    /// Check if capabilities satisfy this requirement
    pub fn satisfied_by(&self, caps: &SparseCapabilities) -> bool {
        // All required must be granted
        for req in &self.required {
            if !caps.has(*req) {
                return false;
            }
        }
        
        // All forbidden must be shunned
        for forb in &self.forbidden {
            if caps.has(*forb) {
                return false;
            }
        }
        
        true
    }
}

impl Default for CapabilityRequirement {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_sparse_default_shuns_all() {
        let caps = SparseCapabilities::new();
        
        for cap in Capability::ALL {
            assert!(caps.shuns(cap));
        }
        
        assert_eq!(caps.sparsity(), 1.0);
    }
    
    #[test]
    fn test_grant_and_shun() {
        let mut caps = SparseCapabilities::new();
        
        caps.grant(Capability::Colorable);
        assert!(caps.has(Capability::Colorable));
        assert!(!caps.shuns(Capability::Colorable));
        
        caps.shun(Capability::Colorable);
        assert!(caps.shuns(Capability::Colorable));
    }
    
    #[test]
    fn test_fingerprint_o1() {
        let mut caps1 = SparseCapabilities::new();
        caps1.grant(Capability::Sendable);
        caps1.grant(Capability::Receivable);
        
        let mut caps2 = SparseCapabilities::new();
        caps2.grant(Capability::Sendable);
        caps2.grant(Capability::Receivable);
        
        // O(1) comparison via fingerprint
        assert_eq!(caps1.fingerprint(), caps2.fingerprint());
        
        caps2.grant(Capability::Colorable);
        assert_ne!(caps1.fingerprint(), caps2.fingerprint());
    }
    
    #[test]
    fn test_regret() {
        let mut entity = Regrettable::new("test", GAY_SEED);
        
        entity.grant(Capability::Colorable, "initial setup");
        entity.grant(Capability::Sendable, "enable communication");
        
        assert!(entity.capabilities.has(Capability::Colorable));
        assert!(entity.capabilities.has(Capability::Sendable));
        
        // Regret last action
        let regretted = entity.regret();
        assert!(regretted.is_some());
        assert_eq!(regretted.unwrap().capability, Capability::Sendable);
        
        assert!(entity.capabilities.has(Capability::Colorable));
        assert!(entity.capabilities.shuns(Capability::Sendable));
    }
    
    #[test]
    fn test_regret_until_color() {
        let mut entity = Regrettable::new("test", GAY_SEED);
        
        // Make changes that alter color parity
        entity.grant(Capability::Colorable, "a");  // Green
        let color_after_one = entity.color_parity();
        entity.grant(Capability::Iterable, "b");   // Red - flips parity
        entity.grant(Capability::Sendable, "c");   // Green
        
        // Regret until we get back to color_after_one
        let undone = entity.regret_until_color(color_after_one);
        
        // Verify we reached target color
        assert_eq!(entity.color_parity(), color_after_one);
        // May or may not have undone actions depending on color sequence
        println!("Undone {} actions to reach target color", undone.len());
    }
    
    #[test]
    fn test_capability_graph() {
        let mut graph = SparseCapabilityGraph::new(GAY_SEED);
        
        let a = graph.add_entity("alice");
        let b = graph.add_entity("bob");
        let c = graph.add_entity("charlie");
        
        // Grant capabilities
        graph.entities[a].grant(Capability::Sendable, "alice can send");
        graph.entities[b].grant(Capability::Receivable, "bob can receive");
        graph.entities[b].grant(Capability::Sendable, "bob can send");
        graph.entities[c].grant(Capability::Receivable, "charlie can receive");
        
        // Add edges
        assert!(graph.add_edge(a, b)); // alice → bob
        assert!(graph.add_edge(b, c)); // bob → charlie
        assert!(!graph.add_edge(c, a)); // charlie cannot send to alice
        
        // Check reachability
        let reachable = graph.reachable_from(a);
        assert!(reachable.contains(&b));
        assert!(reachable.contains(&c));
    }
    
    #[test]
    fn test_capability_requirement() {
        let mut req = CapabilityRequirement::new();
        req.require(Capability::Sendable)
           .require(Capability::Receivable)
           .forbid(Capability::Colorable);
        
        let mut caps = SparseCapabilities::new();
        caps.grant(Capability::Sendable);
        caps.grant(Capability::Receivable);
        
        assert!(req.satisfied_by(&caps));
        
        caps.grant(Capability::Colorable);
        assert!(!req.satisfied_by(&caps)); // Colorable is forbidden
    }
}
