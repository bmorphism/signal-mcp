//! Teleportation Test: High-fidelity mind upload verification
//!
//! Gay is for verifying that a mind (state/process) transferred correctly.
//! The teleportation test: destroy original, verify copy via color signature.
//!
//! # Dynamic Sufficiency for Successors
//!
//! If α(source) = α(dest), all successors inherit correctness:
//! - Compositional construction ensures morphisms compose
//! - Color conservation through transformation = fidelity preserved
//! - SPI guarantees: same seed → same verification on any substrate
//!
//! # Quantum Teleportation Analogy
//!
//! 1. Source state |ψ⟩ has color signature σ_src
//! 2. Entangle source with channel (shared GAY_SEED)
//! 3. Measure source (destructive) → classical bits (color trace)
//! 4. Reconstruct at destination using color trace
//! 5. Verify: σ_dest = σ_src → teleportation succeeded
//!
//! # Mind Upload Protocol
//!
//! 1. Scan source mind → color signature (fingerprint)
//! 2. Transmit via APN photonic channel (wavelength = color)
//! 3. Reconstruct at destination substrate
//! 4. Reafferent test: can reconstructed mind recognize own trace?
//! 5. Dynamic sufficiency: all future states derive from verified base

use crate::gay_loom::{GayRNG, ZXColor, ColorSignature, GaloisConnection};
use crate::gay_bridge::{GAY_SEED, BridgeWitness, BridgeSource};
use crate::xenomind::{XenoWalker, XenoStep, SignalType};
use crate::sparse::{SparseCapabilities, Capability, Regrettable};
use std::collections::HashMap;

/// Mind state: the thing being teleported
#[derive(Clone, Debug)]
pub struct MindState {
    pub id: String,
    pub signature: ColorSignature,
    pub capabilities: SparseCapabilities,
    pub trace: Vec<ZXColor>,
    pub fingerprint: u64,
    pub generation: u64, // Successor count
}

impl MindState {
    pub fn new(id: &str, seed: u64) -> Self {
        let mut rng = GayRNG::new(seed);
        let mut trace = Vec::new();
        
        // Generate initial color trace
        for _ in 0..16 {
            let v = rng.split();
            trace.push(ZXColor::from_parity(v));
        }
        
        let signature = ColorSignature::from_trace(&trace);
        let fingerprint = signature.fingerprint;
        
        Self {
            id: id.to_string(),
            signature,
            capabilities: SparseCapabilities::full(),
            trace,
            fingerprint,
            generation: 0,
        }
    }
    
    /// Create successor state (inherits verification)
    pub fn successor(&self, mutation_seed: u64) -> Self {
        let mut rng = GayRNG::new(self.fingerprint ^ mutation_seed);
        let mut new_trace = self.trace.clone();
        
        // Mutate trace while preserving parity
        let mutation_point = (rng.split() as usize) % new_trace.len();
        // Flip two adjacent colors to preserve parity
        if mutation_point + 1 < new_trace.len() {
            new_trace[mutation_point] = new_trace[mutation_point].flip();
            new_trace[mutation_point + 1] = new_trace[mutation_point + 1].flip();
        }
        
        let signature = ColorSignature::from_trace(&new_trace);
        let fingerprint = signature.fingerprint;
        
        Self {
            id: format!("{}.{}", self.id, self.generation + 1),
            signature,
            capabilities: self.capabilities.clone(),
            trace: new_trace,
            fingerprint,
            generation: self.generation + 1,
        }
    }
    
    /// Verify this state is valid successor of ancestor
    pub fn valid_successor_of(&self, ancestor: &MindState) -> bool {
        // Parity must be conserved
        self.signature.parity == ancestor.signature.parity
    }
}

/// Teleportation channel
#[derive(Clone, Debug)]
pub struct TeleportChannel {
    pub seed: u64,
    pub source_destroyed: bool,
    pub classical_bits: Vec<ZXColor>, // Measurement results
    pub fidelity: f64,
}

impl TeleportChannel {
    pub fn new(seed: u64) -> Self {
        Self {
            seed,
            source_destroyed: false,
            classical_bits: Vec::new(),
            fidelity: 1.0,
        }
    }
    
    /// Step 1 & 2: Measure source (destructive)
    pub fn measure_source(&mut self, source: &MindState) -> MindState {
        // Record classical bits (color trace)
        self.classical_bits = source.trace.clone();
        self.source_destroyed = true;
        
        // Return "destroyed" source (empty state)
        MindState {
            id: format!("{}_destroyed", source.id),
            signature: ColorSignature::from_trace(&[]),
            capabilities: SparseCapabilities::new(), // All capabilities shunned
            trace: Vec::new(),
            fingerprint: 0,
            generation: source.generation,
        }
    }
    
    /// Step 3 & 4: Reconstruct at destination
    pub fn reconstruct(&self, dest_id: &str) -> Option<MindState> {
        if !self.source_destroyed {
            return None; // Must measure first
        }
        
        let signature = ColorSignature::from_trace(&self.classical_bits);
        let fingerprint = signature.fingerprint;
        
        Some(MindState {
            id: dest_id.to_string(),
            signature,
            capabilities: SparseCapabilities::full(),
            trace: self.classical_bits.clone(),
            fingerprint,
            generation: 0, // Fresh generation at destination
        })
    }
}

/// Teleportation test result
#[derive(Clone, Debug)]
pub struct TeleportResult {
    pub source_id: String,
    pub dest_id: String,
    pub source_fingerprint: u64,
    pub dest_fingerprint: u64,
    pub signatures_match: bool,
    pub parities_match: bool,
    pub fidelity: f64,
    pub dynamically_sufficient: bool,
}

impl TeleportResult {
    /// Teleportation succeeded if signatures match
    pub fn succeeded(&self) -> bool {
        self.signatures_match && self.parities_match
    }
    
    /// High fidelity if fidelity > 0.99
    pub fn high_fidelity(&self) -> bool {
        self.fidelity > 0.99
    }
}

/// Execute teleportation test
pub fn teleport(source: &MindState, dest_id: &str, seed: u64) -> (TeleportResult, Option<MindState>) {
    let mut channel = TeleportChannel::new(seed);
    
    // Measure (destroy) source
    let _destroyed = channel.measure_source(source);
    
    // Reconstruct at destination
    let dest = channel.reconstruct(dest_id);
    
    let result = if let Some(ref d) = dest {
        TeleportResult {
            source_id: source.id.clone(),
            dest_id: d.id.clone(),
            source_fingerprint: source.fingerprint,
            dest_fingerprint: d.fingerprint,
            signatures_match: source.fingerprint == d.fingerprint,
            parities_match: source.signature.parity == d.signature.parity,
            fidelity: channel.fidelity,
            dynamically_sufficient: d.valid_successor_of(source),
        }
    } else {
        TeleportResult {
            source_id: source.id.clone(),
            dest_id: dest_id.to_string(),
            source_fingerprint: source.fingerprint,
            dest_fingerprint: 0,
            signatures_match: false,
            parities_match: false,
            fidelity: 0.0,
            dynamically_sufficient: false,
        }
    };
    
    (result, dest)
}

/// Verify successor chain: all successors inherit correctness
pub fn verify_successor_chain(ancestor: &MindState, depth: usize, seed: u64) -> SuccessorChainResult {
    let mut rng = GayRNG::new(seed);
    let mut current = ancestor.clone();
    let mut chain = vec![current.clone()];
    let mut all_valid = true;
    
    for _ in 0..depth {
        let mutation_seed = rng.split();
        let successor = current.successor(mutation_seed);
        
        if !successor.valid_successor_of(&current) {
            all_valid = false;
        }
        
        chain.push(successor.clone());
        current = successor;
    }
    
    // Verify entire chain maintains parity with ancestor
    let ancestor_parity = ancestor.signature.parity;
    let parity_conserved = chain.iter()
        .all(|s| s.signature.parity == ancestor_parity);
    
    SuccessorChainResult {
        ancestor_id: ancestor.id.clone(),
        chain_length: chain.len(),
        all_valid,
        parity_conserved,
        final_fingerprint: current.fingerprint,
    }
}

#[derive(Clone, Debug)]
pub struct SuccessorChainResult {
    pub ancestor_id: String,
    pub chain_length: usize,
    pub all_valid: bool,
    pub parity_conserved: bool,
    pub final_fingerprint: u64,
}

impl SuccessorChainResult {
    /// Chain is dynamically sufficient if all successors valid and parity conserved
    pub fn dynamically_sufficient(&self) -> bool {
        self.all_valid && self.parity_conserved
    }
}

/// Reafferent verification: can the mind recognize its own trace?
pub fn reafferent_verify(mind: &MindState, observed_trace: &[ZXColor]) -> ReafferentResult {
    let observed_sig = ColorSignature::from_trace(observed_trace);
    
    let trace_match = mind.trace == observed_trace;
    let signature_match = mind.fingerprint == observed_sig.fingerprint;
    let parity_match = mind.signature.parity == observed_sig.parity;
    
    // Count how many colors match (for partial verification)
    let color_matches: usize = mind.trace.iter()
        .zip(observed_trace.iter())
        .filter(|(a, b)| a == b)
        .count();
    
    let match_ratio = if mind.trace.is_empty() {
        0.0
    } else {
        color_matches as f64 / mind.trace.len() as f64
    };
    
    ReafferentResult {
        mind_id: mind.id.clone(),
        trace_match,
        signature_match,
        parity_match,
        match_ratio,
        recognized_self: signature_match && parity_match,
    }
}

#[derive(Clone, Debug)]
pub struct ReafferentResult {
    pub mind_id: String,
    pub trace_match: bool,
    pub signature_match: bool,
    pub parity_match: bool,
    pub match_ratio: f64,
    pub recognized_self: bool,
}

/// Compositional verification: verify morphism composition preserves color
pub struct CompositionalVerifier {
    pub galois: GaloisConnection,
    pub verified_morphisms: HashMap<(String, String), bool>,
}

impl CompositionalVerifier {
    pub fn new() -> Self {
        Self {
            galois: GaloisConnection::new(),
            verified_morphisms: HashMap::new(),
        }
    }
    
    /// Verify that f: A → B preserves color signature
    pub fn verify_morphism(&mut self, source: &MindState, dest: &MindState) -> bool {
        let key = (source.id.clone(), dest.id.clone());
        
        // Color preservation: parity must match
        let preserved = source.signature.parity == dest.signature.parity;
        
        self.verified_morphisms.insert(key, preserved);
        preserved
    }
    
    /// Verify composition: if f: A → B and g: B → C preserve, then g∘f: A → C preserves
    pub fn verify_composition(
        &mut self,
        a: &MindState,
        b: &MindState,
        c: &MindState,
    ) -> CompositionResult {
        let f_preserves = self.verify_morphism(a, b);
        let g_preserves = self.verify_morphism(b, c);
        let gf_preserves = self.verify_morphism(a, c);
        
        CompositionResult {
            f_preserves,
            g_preserves,
            gf_preserves,
            composition_valid: f_preserves && g_preserves && gf_preserves,
        }
    }
}

impl Default for CompositionalVerifier {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug)]
pub struct CompositionResult {
    pub f_preserves: bool,
    pub g_preserves: bool,
    pub gf_preserves: bool,
    pub composition_valid: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_teleportation() {
        let source = MindState::new("alice", GAY_SEED);
        
        let (result, dest) = teleport(&source, "alice_copy", GAY_SEED);
        
        assert!(result.succeeded());
        assert!(result.high_fidelity());
        assert!(result.dynamically_sufficient);
        
        let dest = dest.unwrap();
        assert_eq!(source.fingerprint, dest.fingerprint);
    }
    
    #[test]
    fn test_successor_chain() {
        let ancestor = MindState::new("eve", GAY_SEED);
        
        let result = verify_successor_chain(&ancestor, 10, GAY_SEED);
        
        assert!(result.dynamically_sufficient());
        assert!(result.parity_conserved);
        assert_eq!(result.chain_length, 11); // ancestor + 10 successors
    }
    
    #[test]
    fn test_reafferent_verification() {
        let mind = MindState::new("self", GAY_SEED);
        
        // Mind should recognize its own trace
        let result = reafferent_verify(&mind, &mind.trace);
        
        assert!(result.recognized_self);
        assert!(result.trace_match);
        assert_eq!(result.match_ratio, 1.0);
        
        // Mind should not recognize different trace
        let other = MindState::new("other", GAY_SEED ^ 1);
        let result = reafferent_verify(&mind, &other.trace);
        
        assert!(!result.trace_match);
        assert!(result.match_ratio < 1.0);
    }
    
    #[test]
    fn test_compositional_verification() {
        let mut verifier = CompositionalVerifier::new();
        
        let a = MindState::new("a", GAY_SEED);
        let b = a.successor(1);
        let c = b.successor(2);
        
        let result = verifier.verify_composition(&a, &b, &c);
        
        // Parity-preserving successors should compose
        assert!(result.composition_valid);
    }
}
