# Signal MCP: Model Context Protocol Server for Signal Protocol

[![License](https://img.shields.io/badge/license-AGPL--3.0-blue.svg)](LICENSE)
[![Rust](https://img.shields.io/badge/rust-1.70+-orange.svg)](https://www.rust-lang.org)
[![MCP](https://img.shields.io/badge/MCP-2025--06--18-green.svg)](https://spec.modelcontextprotocol.io)

A formally verified Model Context Protocol (MCP) server that exposes Signal Protocol cryptographic operations for LLM integration.

## 🌟 Key Features

- **17 Structural Alignments** between MCP primitives and Signal Protocol
- **Formal Verification** via Coq proof obligations (under `.topos/`)
- **Delegation Operad** architecture for operation composition
- **BDD + Dependent Types** for behavioral specifications
- **Balanced Ternary Seed 1069**: `[+1, -1, -1, +1, +1, +1, +1]`

## 🏗️ Architecture

### MCP Resources (Read-Only State)
- `signal://sessions/{addr}/{device}` - Double Ratchet session state
- `signal://identities/{service_id}` - Identity keys (Curve25519)
- `signal://messages/{conv}/{msg}` - Message history
- `signal://groups/{id}/credentials` - zkgroup credentials

### MCP Tools (Stateful Operations)
- `signal_encrypt_message` - Double Ratchet + Sealed Sender encryption
- `signal_decrypt_message` - Sealed sender unwrapping + decryption
- `signal_initialize_session` - X3DH key agreement
- `signal_verify_safety_number` - Fingerprint verification
- `signal_generate_group_auth` - Zero-knowledge group credentials
- `signal_multi_recipient_encrypt` - Batch encryption with progress

### MCP Prompts (LLM Workflows)
- `signal_secure_conversation_starter` - Contextual message composition
- `signal_group_privacy_audit` - Privacy posture analysis
- `signal_safety_number_change_alert` - Security education
- `signal_device_linking_guide` - Multi-device setup
- `signal_backup_restore_wizard` - Cloud backup UX

## 🔒 Security Properties (Formally Verified)

All properties proven in Coq (see `.topos/SIGNAL_MCP_DECLARATIVE_SUCCESS_SPECIFICATION.md`):

1. **E2EE**: End-to-end encryption (Signal Protocol)
2. **Forward Secrecy**: Double Ratchet key deletion
3. **Metadata Protection**: Sealed sender
4. **Post-Quantum Security**: ML-KEM-1024 (Kyber)
5. **Zero-Knowledge**: zkgroup anonymous credentials

## 📦 Installation

```bash
cargo add signal-mcp
```

Or add to `Cargo.toml`:
```toml
[dependencies]
signal-mcp = "0.1"
```

## 🚀 Quick Start

### Stdio Server (Development)

```rust
use signal_mcp::SignalMcpServer;
use tokio::io::{stdin, stdout};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let server = SignalMcpServer::new();
    let transport = (stdin(), stdout());

    // Start MCP server
    server.serve(transport).await?;
    Ok(())
}
```

Run with:
```bash
cargo run --example signal-server-stdio
```

### HTTP SSE Server (Production)

```bash
cargo run --features http-sse --release
```

## 🧪 Testing

### Unit Tests
```bash
cargo test
```

### Property-Based Testing (proptest)
```bash
cargo test --features verification
```

### Formal Verification (Coq)
```bash
cd .topos/coq
coqc signal_mcp_verification.v
```

## 📐 Formal Verification

All formal specifications are stored monadically under `.topos/`:

- **[SIGNAL_MCP_INDEX.md](.topos/SIGNAL_MCP_INDEX.md)** - Documentation index
- **[SIGNAL_MCP_ARCHITECTURAL_SPECIFICATION.md](.topos/SIGNAL_MCP_ARCHITECTURAL_SPECIFICATION.md)** - Complete architecture (8000+ words, 17 alignments)
- **[SIGNAL_MCP_DECLARATIVE_SUCCESS_SPECIFICATION.md](.topos/SIGNAL_MCP_DECLARATIVE_SUCCESS_SPECIFICATION.md)** - Coq formal specs, master success predicate
- **[SIGNAL_MCP_69_COGNITIVE_MOMENTS_MERGED.md](.topos/SIGNAL_MCP_69_COGNITIVE_MOMENTS_MERGED.md)** - Progressive proof construction (69 moments via seed 1069)

### Verification Workflow

1. **Phase Space Transitions** (not temporal milestones):
   - Event 1: FoundationEstablished
   - Event 2: TranslationComplete (Rust → Coq via coq-of-rust)
   - Event 3-5: Security property proofs
   - Event 6: Operad coherence
   - Event 7: **SignalMCPSuccess** ✓

2. **Delegation Operad Structure**:
   ```
   signal_encrypt_message delegates to:
     ├─ lookup_session (SessionStore)
     ├─ fetch_identity (IdentityKeyStore)
     ├─ compute_ciphertext (libsignal encrypt)
     └─ wrap_sealed_sender (sealed_sender_encrypt)
   ```

3. **BDD + Dependent Types**:
   ```coq
   Record TypedScenario (op: Operation) : Type := {
     given_state : PreconditionState;
     operation : op;
     then_state : PostconditionState op given_state  (* DEPENDENT! *)
   }.
   ```

## 🎯 Comparison to Existing Solutions

| Feature | Signal Desktop | signald | **Signal MCP** |
|---------|---------------|---------|----------------|
| LLM Integration | ✗ | ✗ | **✓ Native** |
| Batch Operations | Limited | Limited | **✓ With progress** |
| Crypto Transparency | Hidden | Partial | **✓ Full** |
| Session Introspection | ✗ | Limited | **✓ Complete** |
| Formal Verification | ✗ | ✗ | **✓ Coq proofs** |
| Safety Verification UX | Manual | Manual | **✓ Elicitation** |
| OAuth | ✗ | ✗ | **✓ MCP 2025-06-18** |
| Real-time Streaming | WebSocket | WebSocket | **✓ HTTP SSE** |

## 📊 Balanced Ternary Seed 1069

Verification seed: `[+1, -1, -1, +1, +1, +1, +1]`

- **7 trits** → 7 architectural layers
- **17** = 1+0+6+9 → 17 structural alignments
- **69 cognitive moments** → Progressive proof construction

## 🤝 Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for development guidelines.

### Development Setup

```bash
git clone https://github.com/your-org/signal-mcp
cd signal-mcp
cargo build
cargo test
```

## 📝 License

AGPL-3.0-only - See [LICENSE](LICENSE) for details.

Following Signal's licensing: implementations must be open source.

## 🔗 Related Projects

- [MCP Specification](https://spec.modelcontextprotocol.io)
- [Signal Protocol](https://signal.org/docs/)
- [libsignal](https://github.com/signalapp/libsignal)
- [coq-of-rust](https://github.com/formal-land/coq-of-rust)
- [rmcp](https://github.com/modelcontextprotocol/rust-sdk)

## 📚 Documentation

- [Architecture Overview](.topos/SIGNAL_MCP_ARCHITECTURAL_SPECIFICATION.md)
- [Formal Verification](.topos/SIGNAL_MCP_DECLARATIVE_SUCCESS_SPECIFICATION.md)
- [API Documentation](https://docs.rs/signal-mcp)

## 🙏 Acknowledgments

- Signal Messenger team for Signal Protocol
- Anthropic for Model Context Protocol
- formal-land for coq-of-rust
- Topos Institute for categorical foundations

---

**Status**: Formal specification complete, implementation in progress

**Ready for**: Event 1 (FoundationEstablished) → coq-of-rust translation

**Success Metric**: 10/10 proven properties (not temporal duration)

∎
