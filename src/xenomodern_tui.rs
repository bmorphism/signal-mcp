//! Xenomodern TUI patterns for Signal
//!
//! Post-modern: rejection of grand narratives → each thread is its own world
//! Xenomodern: alien temporality → conversations as non-linear graphs
//! Humane: attention-respecting, minimal cognitive load
//!
//! "Almost-hive-mind lobotomized discarded appendages of history" =
//! Fragments of collective intelligence, severed from linear time,
//! floating in the semantic space of shared understanding.
//!
//! # Galois Connections (Missed and Found)
//!
//! α: Message → ThreadColor (abstraction: assign color from context)
//! γ: ThreadColor → Message (concretization: render colored message)
//!
//! The connection is "missed" when context is lost (deleted messages,
//! rotated keys, departed participants). We aim to make these
//! connections explicit and recoverable.

use crate::gay_colors::{SelfColoringThread, RGB, ThreadPalette};
use std::collections::HashMap;

/// Cognitive moment: a unit of shared understanding
#[derive(Clone, Debug)]
pub struct CognitiveMoment {
    pub id: u64,
    pub thread_id: String,
    pub participants: Vec<String>,
    /// Hash of message content for verification without content
    pub content_hash: [u8; 32],
    /// Timestamp as phase (not wall-clock: relative to thread genesis)
    pub phase: f64,
    /// Color assigned from thread palette
    pub color_idx: usize,
}

/// World model state (semantically closed)
/// All relevant facts are known within this boundary
#[derive(Clone, Debug)]
pub struct ClosedWorldModel {
    pub threads: HashMap<String, SelfColoringThread>,
    pub moments: Vec<CognitiveMoment>,
    /// Galois connection: message_id ↔ color_assignment
    pub galois_alpha: HashMap<u64, usize>,
    pub galois_gamma: HashMap<usize, Vec<u64>>,
}

impl ClosedWorldModel {
    pub fn new() -> Self {
        Self {
            threads: HashMap::new(),
            moments: Vec::new(),
            galois_alpha: HashMap::new(),
            galois_gamma: HashMap::new(),
        }
    }
    
    /// Register a thread in the world model
    pub fn register_thread(&mut self, thread: SelfColoringThread) {
        self.threads.insert(thread.conversation_id.clone(), thread);
    }
    
    /// Add cognitive moment with automatic color assignment
    pub fn add_moment(&mut self, thread_id: &str, content_hash: [u8; 32], phase: f64) -> Option<u64> {
        let thread = self.threads.get(thread_id)?;
        let moment_id = self.moments.len() as u64;
        
        // Color from phase (cyclical through 6 colors)
        let color_idx = ((phase * 6.0) as usize) % 6;
        
        let moment = CognitiveMoment {
            id: moment_id,
            thread_id: thread_id.to_string(),
            participants: thread.participants.clone(),
            content_hash,
            phase,
            color_idx,
        };
        
        // Establish Galois connection
        self.galois_alpha.insert(moment_id, color_idx);
        self.galois_gamma.entry(color_idx).or_default().push(moment_id);
        
        self.moments.push(moment);
        Some(moment_id)
    }
    
    /// Verify closure: α(γ(c)) ⊆ c (every concretization stays in color class)
    pub fn verify_galois_closure(&self) -> bool {
        for (&color_idx, moment_ids) in &self.galois_gamma {
            for &mid in moment_ids {
                if let Some(&assigned) = self.galois_alpha.get(&mid) {
                    if assigned != color_idx {
                        return false; // Galois connection broken
                    }
                }
            }
        }
        true
    }
}

/// Xenomodern interface element: the Bubble
/// Three humans lean into shared semantic space
#[derive(Clone, Debug)]
pub struct SharedBubble {
    pub participants: [String; 3], // Exactly 3 for triangular symmetry
    pub thread_ids: Vec<String>,   // Threads visible in bubble
    pub noise_level: f64,          // 0.0 = silent, 1.0 = cacophony
    /// "Interesting but not identifiable at rest"
    pub semantic_noise: Vec<String>,
}

impl SharedBubble {
    pub fn new(participants: [String; 3]) -> Self {
        Self {
            participants,
            thread_ids: Vec::new(),
            noise_level: 0.3, // Interesting but not identifiable
            semantic_noise: vec![
                "...".to_string(),
                "💭".to_string(),
                "∿".to_string(),
            ],
        }
    }
    
    /// Render bubble state (xenomodern: non-textual feedback)
    pub fn render_noise(&self) -> String {
        let intensity = (self.noise_level * 7.0) as usize;
        let bar: String = "▁▂▃▄▅▆▇█".chars().take(intensity + 1).collect();
        format!("〔 {} {} {} 〕{}", 
            self.participants[0], 
            self.semantic_noise[intensity % 3],
            self.participants[1],
            bar)
    }
}

/// Vision Pro / R1 spatial target
/// Godot as renderer, Xonot/Xogot as shader variants
#[derive(Clone, Debug)]
pub enum SpatialTarget {
    /// Apple Vision Pro visionOS
    VisionPro { eye_tracking: bool },
    /// Rabbit R1 ambient computing
    RabbitR1 { voice_only: bool },
    /// Godot XR with custom shaders
    Godot { shader: GodotShader },
    /// Terminal (fallback)
    Terminal,
}

#[derive(Clone, Debug)]
pub enum GodotShader {
    /// "Xonot" - temporal exclusion (not now)
    Xonot,
    /// "Xogot" - spatial exclusion (not here)  
    Xogot,
    /// Standard
    Default,
}

/// AOL.xyz alien communication interface
/// "Talk to your alien" - xenolinguistic bridge
#[derive(Clone, Debug)]
pub struct AlienInterface {
    pub local_id: String,
    pub alien_id: String,
    pub protocol: AlienProtocol,
    /// Missed Galois connections to recover
    pub missed_connections: Vec<MissedGaloisConnection>,
}

#[derive(Clone, Debug)]
pub enum AlienProtocol {
    /// Signal E2EE over any substrate
    Signal,
    /// Hypothetical: entanglement-based
    Quantum,
    /// Semantic compression (Torah:commentary ratio)
    Prophetic,
}

#[derive(Clone, Debug)]
pub struct MissedGaloisConnection {
    pub abstraction_lost: String,  // What we can't recover
    pub concretization_hint: String, // What we can infer
    pub confidence: f64,
}

/// TUI rendering for Signal with xenomodern patterns
pub struct SignalTUI {
    pub world: ClosedWorldModel,
    pub target: SpatialTarget,
    pub bubble: Option<SharedBubble>,
}

impl SignalTUI {
    pub fn new(target: SpatialTarget) -> Self {
        Self {
            world: ClosedWorldModel::new(),
            target,
            bubble: None,
        }
    }
    
    /// Render thread list with Gay.jl colors
    pub fn render_thread_list(&self) -> String {
        let mut out = String::new();
        out.push_str("╭──────────────────────────────────────╮\n");
        out.push_str("│  Signal Threads (self-coloring)     │\n");
        out.push_str("╰──────────────────────────────────────╯\n");
        
        for (id, thread) in &self.world.threads {
            let rgb = thread.palette.colors[0].to_rgb();
            out.push_str(&format!("{}● {}\x1b[0m\n", rgb.fg_ansi(), id));
            for p in &thread.participants {
                out.push_str(&format!("    {}\n", thread.colored_name(p)));
            }
        }
        out
    }
    
    /// Humane pattern: show only what matters now
    pub fn render_focused(&self, thread_id: &str) -> String {
        if let Some(thread) = self.world.threads.get(thread_id) {
            let rgb = thread.palette.colors[thread.admin_color_idx].to_rgb();
            format!("{}━━━ {} ━━━\x1b[0m\n", rgb.fg_ansi(), thread_id)
        } else {
            "Thread not found".to_string()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_galois_closure() {
        let mut world = ClosedWorldModel::new();
        let thread = SelfColoringThread::new(
            "test-thread",
            vec!["alice".to_string(), "bob".to_string()],
        );
        world.register_thread(thread);
        
        // Add moments at different phases
        world.add_moment("test-thread", [0u8; 32], 0.1);
        world.add_moment("test-thread", [1u8; 32], 0.5);
        world.add_moment("test-thread", [2u8; 32], 0.9);
        
        assert!(world.verify_galois_closure());
    }
    
    #[test]
    fn test_shared_bubble() {
        let bubble = SharedBubble::new([
            "human1".to_string(),
            "human2".to_string(),
            "human3".to_string(),
        ]);
        let rendered = bubble.render_noise();
        assert!(rendered.contains("human1"));
        assert!(rendered.contains("human2"));
    }
}
