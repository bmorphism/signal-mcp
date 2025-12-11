//! Signal MCP Server implementation
//!
//! This module provides the main MCP server that exposes Signal Protocol
//! operations as MCP Resources, Tools, and Prompts.

use crate::types::*;
use rmcp::{
    ErrorData as McpError, RoleServer, ServerHandler,
    handler::server::{
        router::tool::ToolRouter,
        wrapper::Parameters,
    },
    model::*,
    service::RequestContext,
    tool, tool_handler, tool_router,
};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;
use tracing::info;

/// Main Signal MCP Server
///
/// Implements the delegation operad structure:
/// - Resources: Sessions, Identities, Messages
/// - Tools: Encrypt, Decrypt, Initialize Session, Verify Safety Number
/// - Prompts: Conversation starters, Privacy audits
#[derive(Clone)]
pub struct SignalMcpServer {
    /// In-memory session store (production: use persistent storage)
    sessions: Arc<Mutex<HashMap<ProtocolAddress, SessionRecord>>>,

    /// Identity key store
    identities: Arc<Mutex<HashMap<ServiceId, IdentityKey>>>,

    /// Tool router for MCP tools
    tool_router: ToolRouter<SignalMcpServer>,
}

#[tool_router]
impl SignalMcpServer {
    pub fn new() -> Self {
        Self {
            sessions: Arc::new(Mutex::new(HashMap::new())),
            identities: Arc::new(Mutex::new(HashMap::new())),
            tool_router: Self::tool_router(),
        }
    }

    /// Encrypt a message using Signal Protocol
    #[tool(
        name = "signal_encrypt_message",
        description = "Encrypt a message using Signal Protocol (Double Ratchet + Sealed Sender)"
    )]
    async fn encrypt_message(
        &self,
        Parameters(req): Parameters<EncryptionRequest>,
    ) -> std::result::Result<CallToolResult, McpError> {
        info!("Encrypting message for {:?}", req.recipient);

        // TODO: Actual Signal Protocol encryption via libsignal
        // For now, return placeholder
        let response = EncryptionResponse {
            ciphertext: vec![0xDE, 0xAD, 0xBE, 0xEF],  // Placeholder
            used_prekey: false,
            used_kyber: false,
        };

        Ok(CallToolResult::success(vec![Content::text(
            serde_json::to_string(&response).unwrap(),
        )]))
    }

    /// Initialize a new Signal Protocol session
    #[tool(
        name = "signal_initialize_session",
        description = "Initialize a new Signal Protocol session using X3DH key agreement"
    )]
    async fn initialize_session(
        &self,
        Parameters(_req): Parameters<SessionInitRequest>,
    ) -> std::result::Result<CallToolResult, McpError> {
        info!("Initializing session");

        // TODO: Actual X3DH key agreement via libsignal

        Ok(CallToolResult::success(vec![Content::text(
            "Session initialized (placeholder)".to_string(),
        )]))
    }

    /// Verify safety numbers (fingerprints)
    #[tool(
        name = "signal_verify_safety_number",
        description = "Compute and verify safety numbers (fingerprints) for identity verification"
    )]
    async fn verify_safety_number(
        &self,
        Parameters(_req): Parameters<SafetyNumberRequest>,
    ) -> std::result::Result<CallToolResult, McpError> {
        info!("Verifying safety number");

        // TODO: Actual fingerprint computation via libsignal
        let safety_number = SafetyNumber {
            displayable: "123456789012345678901234567890".to_string(),
            scannable: vec![0x00; 32],
        };

        Ok(CallToolResult::success(vec![Content::text(
            serde_json::to_string(&safety_number).unwrap(),
        )]))
    }
}

#[tool_handler]
impl ServerHandler for SignalMcpServer {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: ProtocolVersion::V_2024_11_05,
            capabilities: ServerCapabilities::builder()
                .enable_resources()
                .enable_tools()
                .build(),
            server_info: Implementation::from_build_env(),
            instructions: Some(
                "Signal MCP provides cryptographic operations from Signal Protocol. \
                Tools: signal_encrypt_message, signal_initialize_session, signal_verify_safety_number. \
                Resources: signal://sessions (Double Ratchet state), signal://identities (Curve25519 keys)."
                .to_string()
            ),
        }
    }

    async fn list_resources(
        &self,
        _request: Option<PaginatedRequestParam>,
        _ctx: RequestContext<RoleServer>,
    ) -> std::result::Result<ListResourcesResult, McpError> {
        Ok(ListResourcesResult {
            resources: vec![
                RawResource {
                    uri: "signal://sessions".to_string(),
                    name: "Signal Sessions".to_string(),
                    title: None,
                    description: Some("All active Signal Protocol sessions with Double Ratchet state".to_string()),
                    mime_type: Some("application/json".to_string()),
                    size: None,
                    icons: None,
                }.no_annotation(),
                RawResource {
                    uri: "signal://identities".to_string(),
                    name: "Signal Identities".to_string(),
                    title: None,
                    description: Some("Identity keys for all known contacts".to_string()),
                    mime_type: Some("application/json".to_string()),
                    size: None,
                    icons: None,
                }.no_annotation(),
            ],
            next_cursor: None,
        })
    }

    async fn read_resource(
        &self,
        ReadResourceRequestParam { uri }: ReadResourceRequestParam,
        _ctx: RequestContext<RoleServer>,
    ) -> std::result::Result<ReadResourceResult, McpError> {
        match uri.as_str() {
            "signal://sessions" => {
                let sessions = self.sessions.lock().await;
                let sessions_json = serde_json::to_string(&*sessions)
                    .map_err(|_| McpError::internal_error("Failed to serialize sessions", None))?;

                Ok(ReadResourceResult {
                    contents: vec![ResourceContents::text(sessions_json, uri)],
                })
            }
            "signal://identities" => {
                let identities = self.identities.lock().await;
                let identities_json = serde_json::to_string(&*identities)
                    .map_err(|_| McpError::internal_error("Failed to serialize identities", None))?;

                Ok(ReadResourceResult {
                    contents: vec![ResourceContents::text(identities_json, uri)],
                })
            }
            _ => Err(McpError::resource_not_found(
                "Unknown resource",
                Some(serde_json::json!({ "uri": uri })),
            )),
        }
    }

    async fn list_resource_templates(
        &self,
        _request: Option<PaginatedRequestParam>,
        _ctx: RequestContext<RoleServer>,
    ) -> std::result::Result<ListResourceTemplatesResult, McpError> {
        Ok(ListResourceTemplatesResult {
            next_cursor: None,
            resource_templates: Vec::new(),
        })
    }

    async fn initialize(
        &self,
        _request: InitializeRequestParam,
        _ctx: RequestContext<RoleServer>,
    ) -> std::result::Result<InitializeResult, McpError> {
        Ok(self.get_info())
    }
}

impl Default for SignalMcpServer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_server_creation() {
        let server = SignalMcpServer::new();
        assert!(server.sessions.try_lock().is_ok());
        assert!(server.identities.try_lock().is_ok());
    }

    #[test]
    fn test_tool_router() {
        let server = SignalMcpServer::new();
        let router = &server.tool_router;

        assert!(router.has_route("signal_encrypt_message"));
        assert!(router.has_route("signal_initialize_session"));
        assert!(router.has_route("signal_verify_safety_number"));

        let tools = router.list_all();
        assert_eq!(tools.len(), 3);
    }

    #[test]
    fn test_server_info() {
        let server = SignalMcpServer::new();
        let info = server.get_info();

        // Implementation::from_build_env() uses the crate it's compiled in
        assert!(!info.server_info.name.is_empty());
        assert!(!info.server_info.version.is_empty());
        assert!(info.capabilities.tools.is_some());
        assert!(info.capabilities.resources.is_some());
    }
}
