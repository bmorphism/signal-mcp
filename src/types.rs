//! Core types for Signal MCP
//!
//! These types map to both MCP protocol types and Signal Protocol types,
//! forming the delegation operad structure described in `.topos/`.

use serde::{Deserialize, Serialize};
use schemars::JsonSchema;

/// Protocol address identifying a Signal user + device
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq, Eq, Hash)]
pub struct ProtocolAddress {
    pub name: String,
    pub device_id: u32,
}

/// Service ID (UUID) for Signal users
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceId(pub String);

/// Identity key (Curve25519 public key)
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct IdentityKey {
    pub public_key: Vec<u8>,
}

/// Session record containing Double Ratchet state
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SessionRecord {
    pub address: ProtocolAddress,
    pub session_version: u32,
    pub local_identity_key: IdentityKey,
    pub remote_identity_key: IdentityKey,
    pub sending_chain_key: Vec<u8>,
    pub receiving_chain_key: Vec<u8>,
    pub kyber_prekey_used: bool,
}

/// Encryption request for signal_encrypt_message tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct EncryptionRequest {
    pub recipient: ProtocolAddress,
    pub plaintext: Vec<u8>,
    pub use_sealed_sender: bool,
}

/// Encryption response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncryptionResponse {
    pub ciphertext: Vec<u8>,
    pub used_prekey: bool,
    pub used_kyber: bool,
}

/// Session initialization request
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SessionInitRequest {
    pub recipient: ProtocolAddress,
    pub prekey_bundle: PreKeyBundle,
}

/// PreKey bundle for session initialization (X3DH)
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct PreKeyBundle {
    pub registration_id: u32,
    pub device_id: u32,
    pub prekey_id: u32,
    pub prekey_public: Vec<u8>,
    pub signed_prekey_id: u32,
    pub signed_prekey_public: Vec<u8>,
    pub signed_prekey_signature: Vec<u8>,
    pub identity_key: IdentityKey,
    pub kyber_prekey: Option<Vec<u8>>,
}

/// Safety number verification request
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SafetyNumberRequest {
    pub local_identity: IdentityKey,
    pub remote_identity: IdentityKey,
}

/// Safety number for identity verification
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SafetyNumber {
    pub displayable: String,  // 30 digits
    pub scannable: Vec<u8>,   // QR code data
}

/// zkgroup group credentials
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GroupAuthCredential {
    pub credential: Vec<u8>,
    pub presentation: Vec<u8>,
}

// Verification properties (enabled with "verification" feature)
#[cfg(feature = "verification")]
pub mod verification {
    use super::*;

    /// Invariant: SessionRecord maintains Double Ratchet consistency
    pub fn session_invariant(session: &SessionRecord) -> bool {
        !session.sending_chain_key.is_empty() &&
        !session.receiving_chain_key.is_empty() &&
        session.session_version > 0
    }

    /// Property: Encryption produces valid ciphertext
    pub fn encryption_valid(req: &EncryptionRequest, resp: &EncryptionResponse) -> bool {
        !resp.ciphertext.is_empty() &&
        resp.ciphertext.len() > req.plaintext.len()  // Authenticated encryption adds overhead
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_protocol_address_serde() {
        let addr = ProtocolAddress {
            name: "alice".to_string(),
            device_id: 1,
        };
        let json = serde_json::to_string(&addr).unwrap();
        let decoded: ProtocolAddress = serde_json::from_str(&json).unwrap();
        assert_eq!(addr, decoded);
    }

    #[cfg(feature = "verification")]
    #[test]
    fn test_session_invariant() {
        use verification::*;

        let session = SessionRecord {
            address: ProtocolAddress {
                name: "bob".to_string(),
                device_id: 1,
            },
            session_version: 3,
            local_identity_key: IdentityKey { public_key: vec![1, 2, 3] },
            remote_identity_key: IdentityKey { public_key: vec![4, 5, 6] },
            sending_chain_key: vec![7, 8, 9],
            receiving_chain_key: vec![10, 11, 12],
            kyber_prekey_used: true,
        };

        assert!(session_invariant(&session));
    }
}
