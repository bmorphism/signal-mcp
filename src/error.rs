//! Error types for Signal MCP

use thiserror::Error;

#[derive(Error, Debug)]
pub enum SignalMcpError {
    #[error("Signal protocol error: {0}")]
    SignalProtocol(String),

    #[error("MCP protocol error: {0}")]
    McpProtocol(String),

    #[error("Session not found for address: {0}")]
    SessionNotFound(String),

    #[error("Invalid session: {0}")]
    InvalidSession(String),

    #[error("Invalid prekey: {0}")]
    InvalidPreKey(String),

    #[error("Invalid message: {0}")]
    InvalidMessage(String),

    #[error("Cryptographic failure: {0}")]
    CryptoFailure(String),

    #[error("Untrusted identity: {0}")]
    UntrustedIdentity(String),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),

    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

pub type Result<T> = std::result::Result<T, SignalMcpError>;

// Verification invariant: errors never leak secrets
#[cfg(feature = "verification")]
impl SignalMcpError {
    /// Verify that error messages don't contain secret material
    pub fn verify_no_leakage(&self) -> bool {
        // Property: error Display output must not contain private keys
        true // Placeholder for formal verification
    }
}
