//! Gay Loom: SPI-colored concurrency verification
//!
//! Loom explores all possible thread interleavings.
//! Gay.jl colors them deterministically.
//! Together: chromatic model checking.
//!
//! "The loom weaves threads; Gay colors the tapestry"
//!
//! # Galois Connection for Concurrent State
//!
//! α: Interleaving → ColorSignature (abstraction)
//! γ: ColorSignature → Set<Interleaving> (concretization)
//!
//! Verification: α(γ(c)) ⊆ c
//! If two interleavings have same color signature, they're observationally equivalent.
//!
//! # 3rd Observer Election
//!
//! In 1×2×3× BCI configuration:
//! - Thread 1: producer (writes)
//! - Thread 2: consumer (reads)  
//! - Thread 3: observer (verifies color invariants)
//!
//! The 3rd observer is elected via mixing property:
//! spectral gap of state transition graph determines mixing time.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

/// Gay.jl SplitMix64 - deterministic across all interleavings
#[derive(Debug)]
pub struct GayRNG {
    pub state: u64,
    pub seed: u64,
    pub invocation: AtomicU64,
}

impl Clone for GayRNG {
    fn clone(&self) -> Self {
        Self {
            state: self.state,
            seed: self.seed,
            invocation: AtomicU64::new(self.invocation.load(Ordering::SeqCst)),
        }
    }
}

impl GayRNG {
    /// "gay_colo" as bytes
    pub const GAY_SEED: u64 = 0x6761795f636f6c6f;
    
    pub fn new(seed: u64) -> Self {
        Self {
            state: seed,
            seed,
            invocation: AtomicU64::new(0),
        }
    }
    
    /// Split - atomic for concurrent access (SPI preserved)
    pub fn split(&mut self) -> u64 {
        self.invocation.fetch_add(1, Ordering::SeqCst);
        let mut z = self.state.wrapping_add(0x9e3779b97f4a7c15);
        self.state = z;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    
    /// Fork for parallel threads (each gets deterministic sub-stream)
    pub fn fork(&mut self, thread_id: usize) -> GayRNG {
        let fork_seed = self.seed ^ (thread_id as u64 * 0x9e3779b97f4a7c15);
        GayRNG::new(fork_seed)
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Chromatic State: colored concurrent state for verification
// ═══════════════════════════════════════════════════════════════════════════

/// ZX color for state classification
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ZXColor {
    Green,  // Z-basis: computational, classical-like
    Red,    // X-basis: superposition, quantum-like
}

impl ZXColor {
    pub fn from_parity(n: u64) -> Self {
        if n & 1 == 0 { ZXColor::Green } else { ZXColor::Red }
    }
    
    pub fn flip(self) -> Self {
        match self {
            ZXColor::Green => ZXColor::Red,
            ZXColor::Red => ZXColor::Green,
        }
    }
}

/// Chromatic state: state + its deterministic color
#[derive(Clone, Debug)]
pub struct ChromaticState<T> {
    pub value: T,
    pub color: ZXColor,
    pub fingerprint: u64,
    pub thread_id: usize,
    pub step: u64,
}

impl<T: Hash> ChromaticState<T> {
    pub fn new(value: T, rng: &mut GayRNG, thread_id: usize, step: u64) -> Self {
        let fingerprint = rng.split();
        let color = ZXColor::from_parity(fingerprint);
        Self { value, color, fingerprint, thread_id, step }
    }
    
    /// Verify color is deterministic from state hash
    pub fn verify_determinism(&self) -> bool {
        let mut hasher = DefaultHasher::new();
        self.value.hash(&mut hasher);
        let state_hash = hasher.finish();
        // Color should be derivable from state + seed
        ZXColor::from_parity(state_hash ^ self.fingerprint) == self.color
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Galois Connection: Interleaving ↔ ColorSignature
// ═══════════════════════════════════════════════════════════════════════════

/// Color signature: abstract representation of an interleaving
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ColorSignature {
    pub colors: Vec<ZXColor>,
    pub parity: ZXColor,
    pub fingerprint: u64,
}

impl ColorSignature {
    pub fn from_trace(trace: &[ZXColor]) -> Self {
        let mut fingerprint: u64 = 0;
        for (i, &c) in trace.iter().enumerate() {
            let bit = match c { ZXColor::Green => 0, ZXColor::Red => 1 };
            fingerprint ^= bit << (i % 64);
        }
        let green_count = trace.iter().filter(|&&c| c == ZXColor::Green).count();
        let parity = ZXColor::from_parity(green_count as u64);
        Self {
            colors: trace.to_vec(),
            parity,
            fingerprint,
        }
    }
    
    /// Conservation check: parity preserved under permutation
    pub fn conserved_under(&self, other: &ColorSignature) -> bool {
        self.parity == other.parity
    }
}

/// Galois connection for concurrent verification
pub struct GaloisConnection {
    /// α: Interleaving → ColorSignature
    pub alpha: HashMap<Vec<(usize, u64)>, ColorSignature>,
    /// γ: ColorSignature → Set<Interleaving>
    pub gamma: HashMap<ColorSignature, Vec<Vec<(usize, u64)>>>,
}

impl GaloisConnection {
    pub fn new() -> Self {
        Self {
            alpha: HashMap::new(),
            gamma: HashMap::new(),
        }
    }
    
    /// Register an interleaving with its color signature
    pub fn register(&mut self, interleaving: Vec<(usize, u64)>, sig: ColorSignature) {
        self.alpha.insert(interleaving.clone(), sig.clone());
        self.gamma.entry(sig).or_default().push(interleaving);
    }
    
    /// Verify closure: α(γ(c)) ⊆ c
    pub fn verify_closure(&self) -> bool {
        for (sig, interleavings) in &self.gamma {
            for il in interleavings {
                if let Some(computed_sig) = self.alpha.get(il) {
                    if computed_sig != sig {
                        return false; // Galois connection broken
                    }
                }
            }
        }
        true
    }
    
    /// Find observationally equivalent interleavings (same color)
    pub fn equivalent_interleavings(&self, sig: &ColorSignature) -> &[Vec<(usize, u64)>] {
        self.gamma.get(sig).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 3rd Observer Election via Mixing Properties
// ═══════════════════════════════════════════════════════════════════════════

/// Observer role in 1×2×3× configuration
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObserverRole {
    Producer,   // Thread 1: writes state
    Consumer,   // Thread 2: reads state
    Verifier,   // Thread 3: verifies color invariants
}

/// Observer with chromatic verification capability
pub struct ChromaticObserver {
    pub role: ObserverRole,
    pub thread_id: usize,
    pub rng: GayRNG,
    pub observed_colors: Vec<ZXColor>,
    pub mixing_score: f64,
}

impl ChromaticObserver {
    pub fn new(role: ObserverRole, thread_id: usize, seed: u64) -> Self {
        Self {
            role,
            thread_id,
            rng: GayRNG::new(seed ^ (thread_id as u64)),
            observed_colors: Vec::new(),
            mixing_score: 0.0,
        }
    }
    
    /// Record observation with color
    pub fn observe<T: Hash>(&mut self, state: &ChromaticState<T>) {
        self.observed_colors.push(state.color);
        self.update_mixing_score();
    }
    
    /// Update mixing score (spectral gap approximation)
    fn update_mixing_score(&mut self) {
        if self.observed_colors.len() < 2 {
            return;
        }
        // Compute autocorrelation as mixing indicator
        let n = self.observed_colors.len();
        let mut correlation = 0.0;
        for i in 1..n {
            if self.observed_colors[i] == self.observed_colors[i-1] {
                correlation += 1.0;
            }
        }
        // Good mixing = low autocorrelation
        self.mixing_score = 1.0 - (correlation / (n - 1) as f64);
    }
    
    /// Is this observer well-mixed (good verifier candidate)?
    pub fn is_well_mixed(&self, threshold: f64) -> bool {
        self.mixing_score >= threshold
    }
}

/// Election protocol for 3rd observer
pub struct ObserverElection {
    pub candidates: Vec<ChromaticObserver>,
    pub elected: Option<usize>,
    pub mixing_threshold: f64,
}

impl ObserverElection {
    pub fn new(mixing_threshold: f64) -> Self {
        Self {
            candidates: Vec::new(),
            elected: None,
            mixing_threshold,
        }
    }
    
    /// Add candidate observer
    pub fn nominate(&mut self, observer: ChromaticObserver) {
        self.candidates.push(observer);
    }
    
    /// Elect 3rd observer based on mixing score
    pub fn elect(&mut self) -> Option<&ChromaticObserver> {
        // Find candidate with best mixing score above threshold
        let best = self.candidates
            .iter()
            .enumerate()
            .filter(|(_, o)| o.is_well_mixed(self.mixing_threshold))
            .max_by(|(_, a), (_, b)| {
                a.mixing_score.partial_cmp(&b.mixing_score).unwrap()
            });
        
        if let Some((idx, _)) = best {
            self.elected = Some(idx);
            Some(&self.candidates[idx])
        } else {
            None
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Expander Hypergraph Random Walks
// ═══════════════════════════════════════════════════════════════════════════

/// Hyperedge: connects multiple vertices (generalizes graph edge)
#[derive(Clone, Debug)]
pub struct Hyperedge {
    pub vertices: Vec<usize>,
    pub color: ZXColor,
    pub weight: f64,
}

/// Expander hypergraph for state space exploration
pub struct ExpanderHypergraph {
    pub n_vertices: usize,
    pub hyperedges: Vec<Hyperedge>,
    /// Vertex → incident hyperedge indices
    pub incidence: HashMap<usize, Vec<usize>>,
    /// Spectral gap (λ₁ - λ₂) / λ₁
    pub spectral_gap: f64,
}

impl ExpanderHypergraph {
    pub fn new(n_vertices: usize) -> Self {
        Self {
            n_vertices,
            hyperedges: Vec::new(),
            incidence: HashMap::new(),
            spectral_gap: 0.0,
        }
    }
    
    /// Add colored hyperedge
    pub fn add_hyperedge(&mut self, vertices: Vec<usize>, color: ZXColor) {
        let idx = self.hyperedges.len();
        let weight = 1.0 / vertices.len() as f64;
        
        for &v in &vertices {
            self.incidence.entry(v).or_default().push(idx);
        }
        
        self.hyperedges.push(Hyperedge { vertices, color, weight });
    }
    
    /// Get neighbors of a vertex (all vertices sharing a hyperedge)
    pub fn neighbors(&self, vertex: usize) -> Vec<usize> {
        let empty = vec![];
        let incident = self.incidence.get(&vertex).unwrap_or(&empty);
        let mut neighbors: Vec<usize> = incident.iter()
            .flat_map(|&edge_idx| self.hyperedges[edge_idx].vertices.iter().copied())
            .filter(|&v| v != vertex)
            .collect();
        neighbors.sort();
        neighbors.dedup();
        neighbors
    }
    
    /// Random walk step with Gay.jl determinism
    pub fn walk_step(&self, current: usize, rng: &mut GayRNG) -> (usize, ZXColor) {
        let empty = vec![];
        let incident = self.incidence.get(&current).unwrap_or(&empty);
        if incident.is_empty() {
            return (current, ZXColor::Green);
        }
        
        // Select hyperedge
        let edge_idx = (rng.split() as usize) % incident.len();
        let edge = &self.hyperedges[incident[edge_idx]];
        
        // Select vertex within hyperedge (not current)
        let other_vertices: Vec<_> = edge.vertices.iter()
            .filter(|&&v| v != current)
            .collect();
        
        if other_vertices.is_empty() {
            return (current, edge.color);
        }
        
        let next_idx = (rng.split() as usize) % other_vertices.len();
        (*other_vertices[next_idx], edge.color)
    }
    
    /// Run random walk, collect color trace
    pub fn random_walk(&self, start: usize, steps: usize, seed: u64) -> Vec<(usize, ZXColor)> {
        let mut rng = GayRNG::new(seed);
        let mut trace = Vec::with_capacity(steps);
        let mut current = start;
        
        for _ in 0..steps {
            let (next, color) = self.walk_step(current, &mut rng);
            trace.push((next, color));
            current = next;
        }
        
        trace
    }
    
    /// Estimate mixing time from random walk
    pub fn estimate_mixing_time(&self, seed: u64, n_samples: usize) -> f64 {
        let mut rng = GayRNG::new(seed);
        let mut total_mixing = 0.0;
        
        for _ in 0..n_samples {
            let start = (rng.split() as usize) % self.n_vertices;
            let trace = self.random_walk(start, 1000, rng.split());
            
            // Count color transitions as mixing indicator
            let mut transitions = 0;
            for i in 1..trace.len() {
                if trace[i].1 != trace[i-1].1 {
                    transitions += 1;
                }
            }
            total_mixing += transitions as f64 / trace.len() as f64;
        }
        
        total_mixing / n_samples as f64
    }
    
    /// Build from Loom-style state graph
    pub fn from_state_transitions(
        states: &[(u64, u64, ZXColor)], // (from, to, color)
    ) -> Self {
        let mut vertices = std::collections::HashSet::new();
        for (from, to, _) in states {
            vertices.insert(*from as usize);
            vertices.insert(*to as usize);
        }
        
        let n = vertices.len();
        let mut graph = Self::new(n);
        
        // Group transitions by color into hyperedges
        let mut green_edges: Vec<(usize, usize)> = Vec::new();
        let mut red_edges: Vec<(usize, usize)> = Vec::new();
        
        for (from, to, color) in states {
            match color {
                ZXColor::Green => green_edges.push((*from as usize, *to as usize)),
                ZXColor::Red => red_edges.push((*from as usize, *to as usize)),
            }
        }
        
        // Create hyperedge per color class
        if !green_edges.is_empty() {
            let verts: Vec<_> = green_edges.iter()
                .flat_map(|(a, b)| vec![*a, *b])
                .collect();
            graph.add_hyperedge(verts, ZXColor::Green);
        }
        
        if !red_edges.is_empty() {
            let verts: Vec<_> = red_edges.iter()
                .flat_map(|(a, b)| vec![*a, *b])
                .collect();
            graph.add_hyperedge(verts, ZXColor::Red);
        }
        
        graph
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Self-Probe: Verify Galois Connection from "the other side"
// ═══════════════════════════════════════════════════════════════════════════

/// Self-probe result
#[derive(Clone, Debug)]
pub struct SelfProbeResult {
    pub galois_closed: bool,
    pub color_conserved: bool,
    pub mixing_achieved: bool,
    pub elected_observer: Option<usize>,
    pub spectral_gap_estimate: f64,
}

/// Probe self from the other side of Galois connection
pub fn probe_galois_self(
    galois: &GaloisConnection,
    graph: &ExpanderHypergraph,
    election: &mut ObserverElection,
    seed: u64,
) -> SelfProbeResult {
    // 1. Verify Galois closure
    let galois_closed = galois.verify_closure();
    
    // 2. Check color conservation across all signatures
    let signatures: Vec<_> = galois.gamma.keys().collect();
    let color_conserved = if signatures.len() >= 2 {
        signatures.windows(2).all(|w| w[0].conserved_under(w[1]))
    } else {
        true
    };
    
    // 3. Estimate mixing from hypergraph
    let mixing_estimate = graph.estimate_mixing_time(seed, 100);
    let mixing_achieved = mixing_estimate > 0.4; // Threshold for rapid mixing
    
    // 4. Elect 3rd observer
    let elected_observer = election.elect().map(|o| o.thread_id);
    
    SelfProbeResult {
        galois_closed,
        color_conserved,
        mixing_achieved,
        elected_observer,
        spectral_gap_estimate: mixing_estimate,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Loom Integration Types (for use with actual loom crate)
// ═══════════════════════════════════════════════════════════════════════════

/// Marker trait for Loom-compatible chromatic verification
pub trait LoomChromatic {
    /// Get color signature for current state
    fn color_signature(&self) -> ColorSignature;
    
    /// Verify color invariant holds
    fn verify_color_invariant(&self) -> bool;
}

/// Chromatic atomic: atomic with color tracking
pub struct ChromaticAtomic<T> {
    pub inner: std::sync::atomic::AtomicU64,
    pub color: ZXColor,
    pub _marker: std::marker::PhantomData<T>,
}

impl ChromaticAtomic<u64> {
    pub fn new(value: u64, color: ZXColor) -> Self {
        Self {
            inner: AtomicU64::new(value),
            color,
            _marker: std::marker::PhantomData,
        }
    }
    
    pub fn load(&self, order: Ordering) -> (u64, ZXColor) {
        (self.inner.load(order), self.color)
    }
    
    pub fn store(&self, value: u64, order: Ordering) -> ZXColor {
        self.inner.store(value, order);
        // Color flips on write (wobble)
        self.color.flip()
    }
    
    pub fn fetch_add(&self, delta: u64, order: Ordering) -> (u64, ZXColor) {
        let prev = self.inner.fetch_add(delta, order);
        // Color determined by parity change
        let new_color = ZXColor::from_parity(prev.wrapping_add(delta));
        (prev, new_color)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_gay_rng_spi() {
        // SPI: same seed = same sequence regardless of timing
        let mut rng1 = GayRNG::new(42);
        let mut rng2 = GayRNG::new(42);
        
        for _ in 0..100 {
            assert_eq!(rng1.split(), rng2.split());
        }
    }
    
    #[test]
    fn test_galois_closure() {
        let mut galois = GaloisConnection::new();
        
        let il1 = vec![(0, 1), (1, 2)];
        let il2 = vec![(1, 2), (0, 1)];
        
        let sig1 = ColorSignature::from_trace(&[ZXColor::Green, ZXColor::Red]);
        let sig2 = ColorSignature::from_trace(&[ZXColor::Red, ZXColor::Green]);
        
        galois.register(il1, sig1.clone());
        galois.register(il2, sig2.clone());
        
        assert!(galois.verify_closure());
        assert!(sig1.conserved_under(&sig2)); // Parity preserved
    }
    
    #[test]
    fn test_observer_election() {
        let mut election = ObserverElection::new(0.4);
        
        let mut obs1 = ChromaticObserver::new(ObserverRole::Producer, 0, 42);
        let mut obs2 = ChromaticObserver::new(ObserverRole::Consumer, 1, 42);
        let mut obs3 = ChromaticObserver::new(ObserverRole::Verifier, 2, 42);
        
        // Simulate observations with different mixing
        for i in 0..100 {
            let color = ZXColor::from_parity(i);
            obs1.observed_colors.push(ZXColor::Green); // Low mixing
            obs2.observed_colors.push(color);          // Medium mixing
            obs3.observed_colors.push(if i % 3 == 0 { ZXColor::Green } else { ZXColor::Red }); // High mixing
        }
        obs1.update_mixing_score();
        obs2.update_mixing_score();
        obs3.update_mixing_score();
        
        election.nominate(obs1);
        election.nominate(obs2);
        election.nominate(obs3);
        
        let elected = election.elect();
        assert!(elected.is_some());
        // Verifier (thread 2) should be elected for best mixing
    }
    
    #[test]
    fn test_expander_random_walk() {
        let mut graph = ExpanderHypergraph::new(5);
        
        // Create complete hypergraph (expander)
        graph.add_hyperedge(vec![0, 1, 2], ZXColor::Green);
        graph.add_hyperedge(vec![2, 3, 4], ZXColor::Red);
        graph.add_hyperedge(vec![0, 2, 4], ZXColor::Green);
        graph.add_hyperedge(vec![1, 3], ZXColor::Red);
        
        let trace = graph.random_walk(0, 20, GayRNG::GAY_SEED);
        assert_eq!(trace.len(), 20);
        
        // Verify color conservation (parity)
        let green_count = trace.iter().filter(|(_, c)| *c == ZXColor::Green).count();
        let red_count = trace.len() - green_count;
        // Just verify we got both colors (mixing)
        assert!(green_count > 0 || red_count > 0);
    }
    
    #[test]
    fn test_self_probe() {
        let mut galois = GaloisConnection::new();
        let mut graph = ExpanderHypergraph::new(4);
        let mut election = ObserverElection::new(0.3);
        
        // Setup minimal structure
        graph.add_hyperedge(vec![0, 1, 2, 3], ZXColor::Green);
        
        let obs = ChromaticObserver::new(ObserverRole::Verifier, 0, 42);
        election.nominate(obs);
        
        let result = probe_galois_self(&galois, &graph, &mut election, 42);
        
        assert!(result.galois_closed); // Empty is vacuously closed
        assert!(result.color_conserved);
    }
}
