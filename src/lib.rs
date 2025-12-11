//! Signal MCP: Model Context Protocol Server for Signal Protocol
//!
//! This crate provides a formally verified MCP server implementation
//! that exposes Signal Protocol cryptographic operations.
//!
//! # Formal Verification
//!
//! All specifications and proofs are stored monadically under `.topos/`:
//! - Coq proof obligations
//! - Delegation operad structure
//! - BDD + dependent types specifications
//! - Property-based test strategies
//!
//! # Seed 1069
//!
//! Balanced ternary: [+1, -1, -1, +1, +1, +1, +1]
//! - 7 architectural layers
//! - 17 structural alignments
//! - 69 cognitive moments

pub mod error;
pub mod server;
pub mod resources;
pub mod tools;
pub mod prompts;
pub mod types;
pub mod gay_colors;
pub mod gay_loom;
pub mod gay_bridge;
pub mod xenomind;
pub mod photonic;
pub mod sparse;
pub mod teleport;
pub mod symmetric;
pub mod xenomodern_tui;

// Re-exports
pub use error::{SignalMcpError, Result};
pub use server::SignalMcpServer;

/// Balanced ternary seed for verification
pub const SEED_1069: [i8; 7] = [1, -1, -1, 1, 1, 1, 1];

/// Version of the Signal MCP implementation
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_seed_1069_sum() {
        let sum: i32 = SEED_1069.iter().map(|&x| x as i32).sum();
        assert_eq!(sum, 3, "Balanced ternary seed [+1,-1,-1,+1,+1,+1,+1] sums to 3");
    }

    #[test]
    fn test_seed_1069_length() {
        assert_eq!(SEED_1069.len(), 7, "Seed should have 7 trits");
    }
}
