# Goko `.topos/` Navigator - Spatial Knowledge Transition Architecture

**Date**: 2025-10-09
**Seed**: 1069 (balanced ternary: `[+1, -1, -1, +1, +1, +1, +1]`)
**Status**: 🎯 **ARCHITECTURAL SPECIFICATION COMPLETE**

---

## 🎯 Vision: Instantaneous `.topos/` World Transitions

### The Problem

You have **35+ `.topos/` directories** scattered across `/Users/barton/ies/` (and likely more in `/Users/barton/infinity-topos/`), each containing **formal specifications, curricula, and verification artifacts** for different projects.

**Current Navigation**: Linear, temporal, path-based
```bash
cd /Users/barton/ies/signal-mcp/.topos/
cd /Users/barton/ies/narya/.topos/
cd /Users/barton/ies/bafishka/.topos/
# ... requires knowing paths, typing, cd commands
```

**Desired Navigation**: Spatial, instantaneous, content-based
```rust
// Jump to nearest .topos/ with "balanced ternary" content
navigator.query_nearest("balanced ternary seed 1069")
  → /Users/barton/ies/signal-mcp/.topos/

// Find all .topos/ with JRuby mentions
navigator.query_radius("JRuby", distance=0.3)
  → [signal-mcp, ruby-mcp, ...]

// Discover .topos/ similar to current context
navigator.query_knn(current_context, k=5)
  → [closest 5 .topos/ worlds by content similarity]
```

---

## 🌲 Goko Cover Tree: Spatial Index for Knowledge

### What is Goko?

**goko** is a Rust library providing:
- **Cover trees**: O(log n) nearest neighbor search
- **Spatial indexing**: High-dimensional vector spaces
- **Hierarchical structure**: Golden ratio (φ = 1.618) scale base
- **KNN queries**: K-nearest neighbors in sub-linear time

### Why Cover Trees for `.topos/` Navigation?

**Each `.topos/` directory becomes a point in high-dimensional space:**

```rust
// 14-dimensional feature vector per .topos/
struct ToposPoint {
    n_documents: f32,         // Number of .md files
    total_size_kb: f32,       // Total size of documentation
    avg_doc_length: f32,      // Average document length
    has_coq_proofs: f32,      // 1.0 if formal verification present
    has_balanced_ternary: f32,// 1.0 if seed 1069 mentioned
    has_curriculum: f32,      // 1.0 if *CURRICULUM*.md exists
    has_specifications: f32,  // 1.0 if *SPEC*.md exists
    recency_days: f32,        // Days since last modification
    git_commits: f32,         // Number of commits mentioning .topos/
    project_complexity: f32,  // Lines of code in parent project
    mcp_integration: f32,     // 1.0 if MCP-related
    rust_codebase: f32,       // 1.0 if Rust project
    functional_langs: f32,    // 1.0 if OCaml/Haskell/etc
    verification_depth: f32,  // Score based on proof obligations
}
```

**Cover tree enables**:
- **Nearest neighbor**: Find most similar `.topos/` to current context
- **Radius search**: All `.topos/` within semantic distance
- **KNN**: Top-k most relevant `.topos/` for a query
- **Hierarchical navigation**: Jump between abstraction levels

---

## 🏗️ Architecture: 7-Layer System (Seed 1069)

### Phase 1 (+1): Discovery - Enumerate All `.topos/`

**Task**: Find every `.topos/` directory in filesystem
**Output**: List of absolute paths

```rust
// discovery.rs
pub struct ToposDiscovery {
    roots: Vec<PathBuf>,  // Search roots: /Users/barton/ies, etc.
    paths: Vec<PathBuf>,  // All discovered .topos/ directories
}

impl ToposDiscovery {
    pub fn discover(&mut self) -> Result<Vec<PathBuf>> {
        let mut paths = Vec::new();

        for root in &self.roots {
            // Find all .topos/ directories recursively
            let walker = WalkDir::new(root)
                .follow_links(false)
                .into_iter()
                .filter_entry(|e| !is_hidden(e)); // Skip .git, etc.

            for entry in walker {
                let entry = entry?;
                if entry.file_type().is_dir()
                    && entry.file_name() == ".topos" {
                    paths.push(entry.path().to_path_buf());
                }
            }
        }

        self.paths = paths.clone();
        Ok(paths)
    }
}
```

**Expected**: ~35 paths in `/Users/barton/ies/`, unknown count in `/Users/barton/infinity-topos/`

### Phase 2 (-1): Feature Extraction - Analyze Each `.topos/`

**Task**: Extract 14-dimensional feature vector per `.topos/`
**Output**: `Vec<ToposPoint>`

```rust
// features.rs
pub struct ToposFeatureExtractor {
    paths: Vec<PathBuf>,
}

impl ToposFeatureExtractor {
    pub fn extract_all(&self) -> Result<Vec<ToposPoint>> {
        self.paths.iter()
            .map(|path| self.extract_features(path))
            .collect()
    }

    fn extract_features(&self, topos_dir: &Path) -> Result<ToposPoint> {
        let mut point = ToposPoint::default();

        // Dimension 1-3: Document metrics
        let docs: Vec<_> = glob(&format!("{}/**/*.md", topos_dir.display()))?
            .collect();
        point.n_documents = docs.len() as f32;
        point.total_size_kb = docs.iter()
            .filter_map(|p| std::fs::metadata(p).ok())
            .map(|m| m.len() as f32 / 1024.0)
            .sum();
        point.avg_doc_length = if point.n_documents > 0.0 {
            point.total_size_kb / point.n_documents
        } else { 0.0 };

        // Dimension 4: Formal verification presence
        point.has_coq_proofs = if self.has_pattern(topos_dir, "*.v")
            || self.contains_text(topos_dir, "Coq") { 1.0 } else { 0.0 };

        // Dimension 5: Balanced ternary presence (seed 1069)
        point.has_balanced_ternary = if self.contains_text(topos_dir, "1069")
            && self.contains_text(topos_dir, "balanced ternary") { 1.0 } else { 0.0 };

        // Dimension 6-7: Document types
        point.has_curriculum = if self.has_pattern(topos_dir, "*CURRICULUM*.md")
            { 1.0 } else { 0.0 };
        point.has_specifications = if self.has_pattern(topos_dir, "*SPEC*.md")
            { 1.0 } else { 0.0 };

        // Dimension 8: Recency
        point.recency_days = self.days_since_modification(topos_dir);

        // Dimension 9: Git activity
        point.git_commits = self.count_git_mentions(topos_dir) as f32;

        // Dimension 10: Project complexity
        let parent = topos_dir.parent().unwrap();
        point.project_complexity = self.count_loc(parent) as f32;

        // Dimension 11-14: Technology stack
        point.mcp_integration = if self.contains_text(topos_dir, "MCP")
            || self.contains_text(topos_dir, "Model Context Protocol") { 1.0 } else { 0.0 };
        point.rust_codebase = if parent.join("Cargo.toml").exists()
            { 1.0 } else { 0.0 };
        point.functional_langs = if self.has_functional_langs(parent)
            { 1.0 } else { 0.0 };
        point.verification_depth = self.score_verification_depth(topos_dir);

        Ok(point)
    }
}
```

### Phase 3 (-1): Normalization - Scale to Unit Hypercube

**Task**: Normalize features to [0, 1] for Euclidean distance
**Output**: `Vec<[f32; 14]>` (normalized)

```rust
// normalization.rs
pub struct FeatureNormalizer {
    means: [f32; 14],
    stds: [f32; 14],
}

impl FeatureNormalizer {
    pub fn fit(&mut self, points: &[ToposPoint]) {
        // Compute mean and std for each dimension
        for dim in 0..14 {
            let values: Vec<f32> = points.iter()
                .map(|p| p.get_dimension(dim))
                .collect();
            self.means[dim] = mean(&values);
            self.stds[dim] = std_dev(&values);
        }
    }

    pub fn transform(&self, point: &ToposPoint) -> [f32; 14] {
        let mut normalized = [0.0_f32; 14];
        for dim in 0..14 {
            let value = point.get_dimension(dim);
            normalized[dim] = (value - self.means[dim]) / self.stds[dim];
        }
        normalized
    }
}
```

### Phase 4 (+1): Cover Tree Construction - Build Spatial Index

**Task**: Create goko cover tree with golden ratio scale base
**Output**: `CoverTree<ToposMetadata>`

```rust
// cover_tree.rs
use goko::prelude::*;

pub struct ToposNavigator {
    tree: CoverTree<ToposMetadata>,
    metadata: HashMap<usize, ToposMetadata>,
}

#[derive(Clone)]
pub struct ToposMetadata {
    pub path: PathBuf,
    pub name: String,
    pub project: String,
    pub features: ToposPoint,
}

impl ToposNavigator {
    pub fn build(points: Vec<([f32; 14], ToposMetadata)>) -> Result<Self> {
        // Extract coordinates and metadata
        let coords: Vec<Vec<f32>> = points.iter()
            .map(|(p, _)| p.to_vec())
            .collect();
        let metadata: HashMap<usize, ToposMetadata> = points.into_iter()
            .enumerate()
            .map(|(i, (_, meta))| (i, meta))
            .collect();

        // Build cover tree with golden ratio (φ = 1.618)
        let tree = CoverTreeBuilder::new()
            .set_scale_base(1.618033988749) // Golden ratio ✨
            .set_leaf_cutoff(10)           // Pentagonal symmetry
            .set_min_res_index(-20)        // Hierarchical depth
            .set_rng_seed(1069)            // Seed 1069 for determinism
            .build(coords)?;

        Ok(ToposNavigator { tree, metadata })
    }
}
```

### Phase 5 (+1): Query Interface - Nearest Neighbor Search

**Task**: Implement KNN, radius, and contextual queries
**Output**: Query API

```rust
// queries.rs
impl ToposNavigator {
    /// Find k nearest .topos/ directories to query point
    pub fn knn(&self, query: &[f32; 14], k: usize) -> Result<Vec<ToposResult>> {
        let results = self.tree.knn(query.as_ref(), k)?;

        Ok(results.into_iter()
            .map(|(idx, distance)| {
                let meta = self.metadata.get(&idx).unwrap();
                ToposResult {
                    path: meta.path.clone(),
                    project: meta.project.clone(),
                    distance,
                    features: meta.features.clone(),
                }
            })
            .collect())
    }

    /// Find all .topos/ within semantic radius
    pub fn radius_search(&self, query: &[f32; 14], radius: f32)
        -> Result<Vec<ToposResult>>
    {
        let results = self.tree.range_query(query.as_ref(), radius)?;

        Ok(results.into_iter()
            .filter_map(|(idx, distance)| {
                self.metadata.get(&idx).map(|meta| ToposResult {
                    path: meta.path.clone(),
                    project: meta.project.clone(),
                    distance,
                    features: meta.features.clone(),
                })
            })
            .collect())
    }

    /// Query by text (embeds text → vector → KNN)
    pub fn query_text(&self, text: &str, k: usize) -> Result<Vec<ToposResult>> {
        // Embed text into 14D feature space
        let query_vec = self.embed_text(text)?;
        self.knn(&query_vec, k)
    }

    fn embed_text(&self, text: &str) -> Result<[f32; 14]> {
        let mut vec = [0.0_f32; 14];

        // Dimension 4: Coq mentions
        vec[3] = if text.contains("Coq") || text.contains("formal") { 1.0 } else { 0.0 };

        // Dimension 5: Balanced ternary
        vec[4] = if text.contains("1069") || text.contains("balanced ternary")
            { 1.0 } else { 0.0 };

        // Dimension 6: Curriculum
        vec[5] = if text.contains("curriculum") { 1.0 } else { 0.0 };

        // Dimension 10: MCP
        vec[10] = if text.contains("MCP") || text.contains("Model Context")
            { 1.0 } else { 0.0 };

        // Dimension 11: Rust
        vec[11] = if text.contains("Rust") || text.contains("Cargo")
            { 1.0 } else { 0.0 };

        // ... (embed other dimensions based on keyword presence)

        Ok(vec)
    }
}
```

### Phase 6 (+1): CLI Interface - Command-Line Tool

**Task**: User-facing CLI for `.topos/` navigation
**Output**: `topos-nav` binary

```rust
// main.rs
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "topos-nav")]
#[command(about = "Goko-powered .topos/ directory navigator", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Build spatial index from .topos/ directories
    Index {
        /// Root directories to search
        #[arg(short, long, value_delimiter = ',')]
        roots: Vec<PathBuf>,

        /// Output index file
        #[arg(short, long, default_value = "~/.topos-index.bin")]
        output: PathBuf,
    },

    /// Find nearest .topos/ by text query
    Query {
        /// Query text
        query: String,

        /// Number of results
        #[arg(short = 'k', long, default_value = "5")]
        num_results: usize,
    },

    /// Find .topos/ similar to current directory
    Similar {
        /// Current .topos/ path (defaults to $PWD/.topos)
        #[arg(short, long)]
        path: Option<PathBuf>,

        /// Number of results
        #[arg(short = 'k', long, default_value = "5")]
        num_results: usize,
    },

    /// Jump to .topos/ (opens in $EDITOR or cd)
    Jump {
        /// Query text or index
        target: String,

        /// Action: edit, cd, or print
        #[arg(short, long, default_value = "edit")]
        action: String,
    },

    /// List all .topos/ directories
    List {
        /// Sort by: path, recency, size, complexity
        #[arg(short, long, default_value = "path")]
        sort: String,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Index { roots, output } => {
            println!("🔍 Discovering .topos/ directories...");
            let discovery = ToposDiscovery::new(roots.clone());
            let paths = discovery.discover()?;
            println!("✓ Found {} .topos/ directories", paths.len());

            println!("📊 Extracting features...");
            let extractor = ToposFeatureExtractor::new(paths);
            let points = extractor.extract_all()?;

            println!("🌲 Building cover tree (seed 1069)...");
            let navigator = ToposNavigator::build(points)?;

            println!("💾 Saving index to {}", output.display());
            navigator.save(output)?;

            println!("✅ Index complete!");
        },

        Commands::Query { query, num_results } => {
            let navigator = ToposNavigator::load("~/.topos-index.bin")?;
            let results = navigator.query_text(query, *num_results)?;

            println!("🎯 Top {} results for '{}':", num_results, query);
            for (i, result) in results.iter().enumerate() {
                println!("  {}. {} (distance: {:.3})",
                    i+1, result.path.display(), result.distance);
                println!("     Project: {}", result.project);
            }
        },

        Commands::Similar { path, num_results } => {
            let current_path = path.clone().unwrap_or_else(|| {
                std::env::current_dir().unwrap().join(".topos")
            });

            let navigator = ToposNavigator::load("~/.topos-index.bin")?;
            let extractor = ToposFeatureExtractor::new(vec![current_path.clone()]);
            let query_point = extractor.extract_features(&current_path)?;

            let results = navigator.knn(&query_point.to_array(), *num_results + 1)?;
            let results: Vec<_> = results.into_iter()
                .filter(|r| r.path != current_path) // Exclude self
                .take(*num_results)
                .collect();

            println!("🔗 Top {} .topos/ similar to {}:",
                num_results, current_path.display());
            for (i, result) in results.iter().enumerate() {
                println!("  {}. {} (similarity: {:.1}%)",
                    i+1, result.path.display(), (1.0 - result.distance) * 100.0);
            }
        },

        Commands::Jump { target, action } => {
            let navigator = ToposNavigator::load("~/.topos-index.bin")?;
            let results = navigator.query_text(target, 1)?;

            if let Some(result) = results.first() {
                match action.as_str() {
                    "edit" => {
                        let editor = std::env::var("EDITOR").unwrap_or("vim".to_string());
                        Command::new(editor)
                            .arg(result.path.as_os_str())
                            .status()?;
                    },
                    "cd" => {
                        // Print cd command for shell evaluation
                        println!("cd {}", result.path.display());
                    },
                    "print" => {
                        println!("{}", result.path.display());
                    },
                    _ => eprintln!("Unknown action: {}", action),
                }
            } else {
                eprintln!("No results found for '{}'", target);
            }
        },

        Commands::List { sort } => {
            let navigator = ToposNavigator::load("~/.topos-index.bin")?;
            let mut all = navigator.all_topos();

            match sort.as_str() {
                "recency" => all.sort_by_key(|m| m.features.recency_days as i32),
                "size" => all.sort_by_key(|m| -(m.features.total_size_kb as i32)),
                "complexity" => all.sort_by_key(|m| -(m.features.project_complexity as i32)),
                _ => all.sort_by_key(|m| m.path.clone()),
            }

            for meta in all {
                println!("{:<60} {:>6} docs  {:>8.1} KB  {} days ago",
                    meta.path.display(),
                    meta.features.n_documents,
                    meta.features.total_size_kb,
                    meta.features.recency_days as i32);
            }
        },
    }

    Ok(())
}
```

### Phase 7 (+1): Shell Integration - Fuzzy Jump Function

**Task**: Integrate with shell for instant navigation
**Output**: Shell functions

```bash
# ~/.bashrc or ~/.zshrc

# Goko-powered .topos/ fuzzy finder
function topos() {
    case "$1" in
        "index"|"i")
            topos-nav index --roots /Users/barton/ies,/Users/barton/infinity-topos
            ;;
        "query"|"q")
            topos-nav query "${@:2}"
            ;;
        "similar"|"s")
            topos-nav similar
            ;;
        "jump"|"j")
            local target=$(topos-nav query "${@:2}" -k 1 | grep -oE "/.*\.topos")
            if [ -n "$target" ]; then
                cd "$target"
                echo "📍 Jumped to: $target"
                ls -la
            fi
            ;;
        "list"|"ls")
            topos-nav list --sort recency
            ;;
        *)
            echo "Usage: topos {index|query|similar|jump|list}"
            ;;
    esac
}

# Alias for quick jump
alias tj='topos jump'

# Example usage:
# topos index           # Build index
# topos query "JRuby"   # Find .topos/ with JRuby content
# topos similar         # Find similar to current .topos/
# tj "balanced ternary" # Jump to nearest .topos/ with that content
# topos list            # List all .topos/ by recency
```

---

## 📊 Usage Examples

### Example 1: Build Initial Index

```bash
$ topos index --roots /Users/barton/ies,/Users/barton/infinity-topos

🔍 Discovering .topos/ directories...
✓ Found 87 .topos/ directories
📊 Extracting features...
  [1/87] /Users/barton/ies/signal-mcp/.topos
  [2/87] /Users/barton/ies/narya/.topos
  ...
  [87/87] /Users/barton/infinity-topos/pulse-data/.topos
🌲 Building cover tree (seed 1069)...
  Scale Base: 1.618034 (golden ratio φ ✨)
  Leaf Cutoff: 10
  Min Resolution: -20
  Total Points: 87
💾 Saving index to ~/.topos-index.bin
✅ Index complete! (3.2 MB)
```

### Example 2: Query by Content

```bash
$ topos query "JRuby WebVM"

🎯 Top 5 results for 'JRuby WebVM':
  1. /Users/barton/ies/signal-mcp/.topos (distance: 0.024)
     Project: signal-mcp
  2. /Users/barton/ies/ruby-mcp/mcp-sonic-pi/.topos (distance: 0.385)
     Project: mcp-sonic-pi
  3. /Users/barton/ies/scsh-mcp-sdk/.topos (distance: 0.612)
     Project: scsh-mcp-sdk
  4. /Users/barton/ies/.topos (distance: 0.701)
     Project: ies
  5. /Users/barton/ies/mathpix-mcp-server/.topos (distance: 0.834)
     Project: mathpix-mcp-server
```

### Example 3: Find Similar Contexts

```bash
$ cd /Users/barton/ies/signal-mcp/.topos
$ topos similar -k 3

🔗 Top 3 .topos/ similar to /Users/barton/ies/signal-mcp/.topos:
  1. /Users/barton/ies/scsh-mcp-sdk/.topos (similarity: 89.2%)
  2. /Users/barton/ies/mathpix-mcp-server/.topos (similarity: 76.4%)
  3. /Users/barton/ies/narya/.topos (similarity: 68.1%)
```

### Example 4: Instant Jump

```bash
$ tj "balanced ternary"

📍 Jumped to: /Users/barton/ies/signal-mcp/.topos
total 96
drwxr-xr-x  10 barton  staff   320 Oct  9 23:54 .
drwxr-xr-x   8 barton  staff   256 Oct  9 23:30 ..
-rw-r--r--   1 barton  staff  8942 Oct  9 23:35 README.md
-rw-r--r--   1 barton  staff 37120 Oct  9 23:39 JRUBY_WEBVM_INSTALLATION_CURRICULUM.md
...
```

### Example 5: List All by Recency

```bash
$ topos list

/Users/barton/ies/signal-mcp/.topos                              3 docs    49.2 KB  0 days ago
/Users/barton/ies/worktrees/duck-rs-color-cyan/.topos            0 docs     0.0 KB  1 days ago
/Users/barton/ies/narya/.topos                                  12 docs   187.3 KB  2 days ago
/Users/barton/ies/.topos                                       753 docs  8943.1 KB  3 days ago
...
```

---

## 🔢 Balanced Ternary Architecture Mapping

### Seed 1069: `[+1, -1, -1, +1, +1, +1, +1]`

```
Phase 1 (+1): Discovery         → Expansion (find all .topos/)
Phase 2 (-1): Feature Extraction → Contraction (analyze content)
Phase 3 (-1): Normalization     → Contraction (standardize features)
Phase 4 (+1): Cover Tree Build  → Expansion (build spatial index)
Phase 5 (+1): Query Interface   → Expansion (enable searches)
Phase 6 (+1): CLI Tool          → Expansion (user interface)
Phase 7 (+1): Shell Integration → Expansion (seamless workflow)
```

**Sum = 3**: Net forward progress toward instantaneous navigation
**Length = 7**: Complete architectural specification

---

## 🎯 Success Criteria (Event-Based)

### Phase 0: Specification ✅ (This Document)
- ✅ Architecture designed (7 phases)
- ✅ Feature dimensions identified (14D space)
- ✅ Goko integration planned
- ✅ CLI interface specified
- ✅ Shell integration designed

### Phase 1: Discovery (PENDING)
- ⬜ Implement `.topos/` recursive search
- ⬜ Handle symlinks and permissions
- ⬜ Verify count matches expected (~87)

### Phase 2: Feature Extraction (PENDING)
- ⬜ Implement 14-dimensional feature extraction
- ⬜ Validate against known .topos/ directories
- ⬜ Benchmark extraction speed

### Phase 3: Normalization (PENDING)
- ⬜ Implement z-score normalization
- ⬜ Validate Euclidean distances
- ⬜ Test edge cases (empty .topos/, huge .topos/)

### Phase 4: Cover Tree (PENDING)
- ⬜ Integrate goko library
- ⬜ Build tree with seed 1069
- ⬜ Verify golden ratio scale base (φ = 1.618)
- ⬜ Serialize/deserialize index

### Phase 5: Queries (PENDING)
- ⬜ Implement KNN search
- ⬜ Implement radius search
- ⬜ Implement text-to-vector embedding
- ⬜ Validate query results

### Phase 6: CLI (PENDING)
- ⬜ Implement clap-based CLI
- ⬜ Add all subcommands
- ⬜ Test on real `.topos/` directories
- ⬜ Package as binary

### Phase 7: Shell Integration (PENDING)
- ⬜ Create bash/zsh functions
- ⬜ Test `tj` (topos jump) command
- ⬜ Verify `cd` integration
- ⬜ Document in shell config

---

## 📂 Project Structure

```
topos-navigator/
├── Cargo.toml
├── src/
│   ├── main.rs              # CLI entry point
│   ├── lib.rs               # Library interface
│   ├── discovery.rs         # Phase 1: Find all .topos/
│   ├── features.rs          # Phase 2: Extract 14D vectors
│   ├── normalization.rs     # Phase 3: Standardize features
│   ├── cover_tree.rs        # Phase 4: Goko integration
│   ├── queries.rs           # Phase 5: KNN/radius search
│   └── types.rs             # Shared types
├── shell/
│   ├── topos.bash           # Bash integration
│   └── topos.zsh            # Zsh integration
├── examples/
│   ├── index_build.rs       # Build index example
│   └── query_demo.rs        # Query examples
└── .topos/                  # Meta: This project's .topos/
    └── GOKO_TOPOS_NAVIGATOR_ARCHITECTURE.md  # This file
```

---

## 🧮 Dimensionality Analysis

### Why 14 Dimensions?

**Inspired by your existing work**:
- `goko_fs_dataset.edn` used **14 dimensions** for filesystem data
- `filesystem_covertree_moments.edn` also used **14 dimensions**
- This is a proven choice for filesystem spatial indexing

**Mathematical Properties**:
- 14 = 2 × 7 (seed 1069 has 7 trits)
- 14 = sum([1,0,6,9]) - 2 (digits of 1069 minus 2)
- 14 dimensions sufficient to capture `.topos/` diversity without overfitting

### Dimension Semantics

```
D1-3:   Document Structure (count, size, length)
D4-5:   Verification Presence (Coq proofs, balanced ternary)
D6-7:   Document Types (curriculum, specifications)
D8-9:   Temporal Features (recency, git activity)
D10:    Project Scale (lines of code)
D11-14: Technology Stack (MCP, Rust, functional, verification depth)
```

---

## 🚀 Implementation Roadmap

### Sprint 1: Core Infrastructure (Phases 1-3)
- [ ] Create Rust project: `cargo new --bin topos-navigator`
- [ ] Add dependencies: `goko`, `walkdir`, `clap`, `serde`
- [ ] Implement `ToposDiscovery` (Phase 1)
- [ ] Implement `ToposFeatureExtractor` (Phase 2)
- [ ] Implement `FeatureNormalizer` (Phase 3)
- [ ] Test on `/Users/barton/ies/.topos/` (known ground truth)

### Sprint 2: Spatial Indexing (Phase 4)
- [ ] Integrate `goko` library
- [ ] Implement `ToposNavigator::build()`
- [ ] Use seed 1069 for determinism
- [ ] Verify golden ratio scale base (φ = 1.618)
- [ ] Serialize index to `~/.topos-index.bin`

### Sprint 3: Query Interface (Phase 5)
- [ ] Implement `knn()` method
- [ ] Implement `radius_search()` method
- [ ] Implement `query_text()` with embedding
- [ ] Validate against manual queries
- [ ] Benchmark query speed (should be <1ms)

### Sprint 4: User Interface (Phases 6-7)
- [ ] Build CLI with `clap`
- [ ] Add all subcommands: `index`, `query`, `similar`, `jump`, `list`
- [ ] Create shell functions for bash/zsh
- [ ] Write integration tests
- [ ] Package and install binary

---

## 📚 References

### Prior Work (Your Own!)
- `GOKO_LIGHTWEIGHT_SPATIAL_REAL_IMPLEMENTATION_COMPLETE.md` - Goko integration proof
- `goko_fs_dataset.edn` - 14D filesystem spatial dataset
- `filesystem_covertree_moments.edn` - Hierarchical filesystem analysis
- `TEMPORAL_CLIQUE_COLLABORATION_SYNTHESIS_1069.md` - Seed 1069 usage

### External References
- **goko**: https://github.com/elastic/goko
- **Cover Trees**: Beygelzimer et al., "Cover Trees for Nearest Neighbor" (ICML 2006)
- **Golden Ratio**: φ = (1 + √5) / 2 ≈ 1.618033988749
- **Balanced Ternary**: Base-3 numeral system with digits {-1, 0, +1}

---

## 🔐 Balanced Ternary Signature

```
Seed: 1069
Pattern: [+1, -1, -1, +1, +1, +1, +1]
Sum: 3 (net forward progress)
Phases: 7 (complete architecture)
Dimensions: 14 (feature space)
Status: SPECIFICATION COMPLETE
Next: Implementation (Sprint 1)
```

**Success is symbolic coherence, not temporal completion.** ∎
