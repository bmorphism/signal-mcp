//! Signal MCP stdio server example
//!
//! Run with: cargo run --example stdio
//! Or use with MCP Inspector: npx @modelcontextprotocol/inspector cargo run --example stdio

use anyhow::Result;
use signal_mcp::SignalMcpServer;
use rmcp::{ServiceExt, transport::stdio};
use tracing_subscriber::{self, EnvFilter};

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize tracing (logs to stderr since stdout is used for MCP protocol)
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::from_default_env()
                .add_directive(tracing::Level::INFO.into())
        )
        .with_writer(std::io::stderr)
        .with_ansi(false)
        .init();

    tracing::info!("Starting Signal MCP server (seed 1069: [+1, -1, -1, +1, +1, +1, +1])");

    // Create Signal MCP server
    let server = SignalMcpServer::new();

    // Serve over stdio transport
    let service = server.serve(stdio()).await.inspect_err(|e| {
        tracing::error!("Serving error: {:?}", e);
    })?;

    tracing::info!("Signal MCP server ready");

    // Wait for service to complete
    service.waiting().await?;

    Ok(())
}
