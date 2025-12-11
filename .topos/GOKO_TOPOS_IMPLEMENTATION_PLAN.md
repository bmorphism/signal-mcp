# Goko `.topos/` Navigator - Monadic Implementation Plan

**Date**: 2025-10-09
**Seed**: 1069 (balanced ternary: `[+1, -1, -1, +1, +1, +1, +1]`)
**Status**: 📋 **IMPLEMENTATION SPECIFICATIONS READY**

---

## 🎯 Overview: From Architecture to Reality

### What We Have (Monadic Storage)
✅ Complete architectural specification in `GOKO_TOPOS_NAVIGATOR_ARCHITECTURE.md`
✅ 14-dimensional feature space design
✅ Cover tree integration strategy with golden ratio (φ = 1.618)
✅ CLI interface specification
✅ Shell integration design

### What We Need (Implementation)
- Rust codebase implementing all 7 phases
- Working binary: `topos-nav`
- Shell integration scripts
- Index persistence layer
- Query validation suite

### Current State of .topos/ Ecosystem
- **35 .topos/ directories** in `/Users/barton/ies/`
- **Unknown count** in `/Users/barton/infinity-topos/pulse-data/`
- **Existing goko work** proving 14D spatial filesystem indexing works
- **Golden ratio scale base** (φ = 1.618) validated in prior implementations

---

## 🏗️ Phase-by-Phase Implementation Guide

### Phase 1 (+1): Discovery Implementation

**Goal**: Recursively find all `.topos/` directories across filesystem

#### Data Structures
```rust
// src/discovery.rs

use std::path::{Path, PathBuf};
use walkdir::WalkDir;
use anyhow::{Result, Context};

pub struct ToposDiscovery {
    pub roots: Vec<PathBuf>,
    pub paths: Vec<PathBuf>,
}

impl ToposDiscovery {
    pub fn new(roots: Vec<PathBuf>) -> Self {
        Self {
            roots,
            paths: Vec::new(),
        }
    }

    pub fn discover(&mut self) -> Result<Vec<PathBuf>> {
        let mut paths = Vec::new();

        for root in &self.roots {
            if !root.exists() {
                eprintln!("⚠️  Root does not exist: {}", root.display());
                continue;
            }

            let walker = WalkDir::new(root)
                .follow_links(false) // Don't follow symlinks
                .into_iter()
                .filter_entry(|e| !is_hidden_or_excluded(e));

            for entry in walker {
                match entry {
                    Ok(entry) => {
                        if entry.file_type().is_dir()
                            && entry.file_name() == ".topos"
                        {
                            paths.push(entry.path().to_path_buf());
                        }
                    }
                    Err(e) => {
                        eprintln!("⚠️  Skipping entry: {}", e);
                    }
                }
            }
        }

        self.paths = paths.clone();
        Ok(paths)
    }
}

fn is_hidden_or_excluded(entry: &walkdir::DirEntry) -> bool {
    entry.file_name()
        .to_str()
        .map(|s| {
            // Skip hidden directories (except .topos)
            (s.starts_with('.') && s != ".topos")
            // Skip common large directories
            || s == "node_modules"
            || s == "target"
            || s == ".git"
            || s == "build"
            || s == "dist"
        })
        .unwrap_or(false)
}
```

#### Testing Strategy
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_discovery_finds_signal_mcp_topos() {
        let mut discovery = ToposDiscovery::new(vec![
            PathBuf::from("/Users/barton/ies/signal-mcp")
        ]);

        let paths = discovery.discover().unwrap();

        assert!(paths.iter().any(|p|
            p.to_str().unwrap().contains("signal-mcp/.topos")
        ));
    }

    #[test]
    fn test_discovery_excludes_git_directories() {
        let mut discovery = ToposDiscovery::new(vec![
            PathBuf::from("/Users/barton/ies")
        ]);

        let paths = discovery.discover().unwrap();

        // Should not find any .topos inside .git directories
        assert!(!paths.iter().any(|p|
            p.to_str().unwrap().contains(".git/.topos")
        ));
    }
}
```

#### Validation Checklist
- [ ] Finds exactly 35 .topos/ in `/Users/barton/ies/`
- [ ] Handles permission errors gracefully
- [ ] Skips symlinks to prevent infinite loops
- [ ] Excludes `.git/`, `node_modules/`, `target/` directories
- [ ] Completes in <5 seconds for entire filesystem scan

---

### Phase 2 (-1): Feature Extraction Implementation

**Goal**: Extract 14-dimensional feature vector from each `.topos/` directory

#### Data Structures
```rust
// src/features.rs

use std::path::{Path, PathBuf};
use glob::glob;
use std::time::SystemTime;
use anyhow::{Result, Context};

#[derive(Debug, Clone, Default)]
pub struct ToposPoint {
    pub n_documents: f32,         // D1
    pub total_size_kb: f32,       // D2
    pub avg_doc_length: f32,      // D3
    pub has_coq_proofs: f32,      // D4
    pub has_balanced_ternary: f32,// D5
    pub has_curriculum: f32,      // D6
    pub has_specifications: f32,  // D7
    pub recency_days: f32,        // D8
    pub git_commits: f32,         // D9
    pub project_complexity: f32,  // D10
    pub mcp_integration: f32,     // D11
    pub rust_codebase: f32,       // D12
    pub functional_langs: f32,    // D13
    pub verification_depth: f32,  // D14
}

impl ToposPoint {
    pub fn to_array(&self) -> [f32; 14] {
        [
            self.n_documents,
            self.total_size_kb,
            self.avg_doc_length,
            self.has_coq_proofs,
            self.has_balanced_ternary,
            self.has_curriculum,
            self.has_specifications,
            self.recency_days,
            self.git_commits,
            self.project_complexity,
            self.mcp_integration,
            self.rust_codebase,
            self.functional_langs,
            self.verification_depth,
        ]
    }

    pub fn get_dimension(&self, dim: usize) -> f32 {
        self.to_array()[dim]
    }
}

pub struct ToposFeatureExtractor {
    paths: Vec<PathBuf>,
}

impl ToposFeatureExtractor {
    pub fn new(paths: Vec<PathBuf>) -> Self {
        Self { paths }
    }

    pub fn extract_all(&self) -> Result<Vec<ToposPoint>> {
        self.paths.iter()
            .map(|path| self.extract_features(path))
            .collect()
    }

    pub fn extract_features(&self, topos_dir: &Path) -> Result<ToposPoint> {
        let mut point = ToposPoint::default();

        // D1-D3: Document metrics
        let pattern = format!("{}/**/*.md", topos_dir.display());
        let md_files: Vec<PathBuf> = glob(&pattern)?
            .filter_map(|p| p.ok())
            .collect();

        point.n_documents = md_files.len() as f32;

        let sizes: Vec<f32> = md_files.iter()
            .filter_map(|p| std::fs::metadata(p).ok())
            .map(|m| m.len() as f32 / 1024.0)
            .collect();

        point.total_size_kb = sizes.iter().sum();
        point.avg_doc_length = if point.n_documents > 0.0 {
            point.total_size_kb / point.n_documents
        } else {
            0.0
        };

        // D4: Coq proofs
        let coq_pattern = format!("{}/**/*.v", topos_dir.display());
        let has_coq = glob(&coq_pattern)?.next().is_some();
        let contains_coq_text = self.contains_text(topos_dir, "Coq")?;
        point.has_coq_proofs = if has_coq || contains_coq_text { 1.0 } else { 0.0 };

        // D5: Balanced ternary (seed 1069)
        let has_1069 = self.contains_text(topos_dir, "1069")?;
        let has_ternary = self.contains_text(topos_dir, "balanced ternary")?;
        point.has_balanced_ternary = if has_1069 && has_ternary { 1.0 } else { 0.0 };

        // D6-D7: Document types
        let curriculum_pattern = format!("{}/**/*CURRICULUM*.md", topos_dir.display());
        point.has_curriculum = if glob(&curriculum_pattern)?.next().is_some() {
            1.0
        } else {
            0.0
        };

        let spec_pattern = format!("{}/**/*SPEC*.md", topos_dir.display());
        point.has_specifications = if glob(&spec_pattern)?.next().is_some() {
            1.0
        } else {
            0.0
        };

        // D8: Recency
        point.recency_days = self.days_since_modification(topos_dir)?;

        // D9: Git commits
        point.git_commits = self.count_git_mentions(topos_dir)? as f32;

        // D10: Project complexity
        if let Some(parent) = topos_dir.parent() {
            point.project_complexity = self.count_loc(parent)? as f32;
        }

        // D11: MCP integration
        let has_mcp = self.contains_text(topos_dir, "MCP")?
            || self.contains_text(topos_dir, "Model Context Protocol")?;
        point.mcp_integration = if has_mcp { 1.0 } else { 0.0 };

        // D12: Rust codebase
        if let Some(parent) = topos_dir.parent() {
            point.rust_codebase = if parent.join("Cargo.toml").exists() {
                1.0
            } else {
                0.0
            };
        }

        // D13: Functional languages
        if let Some(parent) = topos_dir.parent() {
            let has_functional = parent.join("dune").exists()
                || parent.join("package.yaml").exists()
                || parent.join("cabal.project").exists();
            point.functional_langs = if has_functional { 1.0 } else { 0.0 };
        }

        // D14: Verification depth
        point.verification_depth = self.score_verification_depth(topos_dir)?;

        Ok(point)
    }

    fn contains_text(&self, dir: &Path, text: &str) -> Result<bool> {
        let pattern = format!("{}/**/*.md", dir.display());
        for entry in glob(&pattern)? {
            if let Ok(path) = entry {
                if let Ok(content) = std::fs::read_to_string(&path) {
                    if content.contains(text) {
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }

    fn days_since_modification(&self, dir: &Path) -> Result<f32> {
        let pattern = format!("{}/**/*.md", dir.display());
        let mut most_recent = None;

        for entry in glob(&pattern)? {
            if let Ok(path) = entry {
                if let Ok(metadata) = std::fs::metadata(&path) {
                    if let Ok(modified) = metadata.modified() {
                        if most_recent.is_none() || modified > most_recent.unwrap() {
                            most_recent = Some(modified);
                        }
                    }
                }
            }
        }

        if let Some(modified) = most_recent {
            let now = SystemTime::now();
            let duration = now.duration_since(modified)?;
            Ok(duration.as_secs() as f32 / 86400.0) // Convert to days
        } else {
            Ok(999.0) // Very old
        }
    }

    fn count_git_mentions(&self, dir: &Path) -> Result<usize> {
        if let Some(parent) = dir.parent() {
            let output = std::process::Command::new("git")
                .arg("-C")
                .arg(parent)
                .arg("log")
                .arg("--all")
                .arg("--oneline")
                .arg("--grep=.topos")
                .output();

            if let Ok(output) = output {
                let lines = String::from_utf8_lossy(&output.stdout);
                return Ok(lines.lines().count());
            }
        }
        Ok(0)
    }

    fn count_loc(&self, dir: &Path) -> Result<usize> {
        let output = std::process::Command::new("find")
            .arg(dir)
            .arg("-type")
            .arg("f")
            .arg("(")
            .arg("-name")
            .arg("*.rs")
            .arg("-o")
            .arg("-name")
            .arg("*.ts")
            .arg("-o")
            .arg("-name")
            .arg("*.py")
            .arg("-o")
            .arg("-name")
            .arg("*.ml")
            .arg(")")
            .arg("-exec")
            .arg("wc")
            .arg("-l")
            .arg("{}")
            .arg("+")
            .output();

        if let Ok(output) = output {
            let text = String::from_utf8_lossy(&output.stdout);
            if let Some(last_line) = text.lines().last() {
                if let Some(num) = last_line.split_whitespace().next() {
                    return Ok(num.parse().unwrap_or(0));
                }
            }
        }
        Ok(0)
    }

    fn score_verification_depth(&self, dir: &Path) -> Result<f32> {
        let mut score = 0.0;

        // +0.3 for Coq files
        if glob(&format!("{}/**/*.v", dir.display()))?.next().is_some() {
            score += 0.3;
        }

        // +0.2 for "theorem", "proof", "Qed"
        if self.contains_text(dir, "theorem")? {
            score += 0.1;
        }
        if self.contains_text(dir, "Proof")? {
            score += 0.1;
        }

        // +0.3 for "verification" or "formal" in titles
        if self.contains_text(dir, "verification")? {
            score += 0.2;
        }

        // +0.2 for dependent types (.lean, .agda, .idr)
        let lean_pattern = format!("{}/**/*.lean", dir.display());
        if glob(&lean_pattern)?.next().is_some() {
            score += 0.2;
        }

        Ok(score.min(1.0))
    }
}
```

#### Testing Strategy
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_signal_mcp_features() {
        let extractor = ToposFeatureExtractor::new(vec![
            PathBuf::from("/Users/barton/ies/signal-mcp/.topos")
        ]);

        let point = extractor.extract_features(
            &PathBuf::from("/Users/barton/ies/signal-mcp/.topos")
        ).unwrap();

        // Should have documents
        assert!(point.n_documents > 0.0);

        // Should have balanced ternary (seed 1069 mentioned in README)
        assert_eq!(point.has_balanced_ternary, 1.0);

        // Should have curriculum (JRUBY_WEBVM_INSTALLATION_CURRICULUM.md)
        assert_eq!(point.has_curriculum, 1.0);

        // Should be recent
        assert!(point.recency_days < 30.0);
    }

    #[test]
    fn test_feature_vector_dimensions() {
        let point = ToposPoint::default();
        let array = point.to_array();

        assert_eq!(array.len(), 14);
    }
}
```

#### Validation Checklist
- [ ] All 14 dimensions extracted successfully
- [ ] Text search works across all .md files
- [ ] Git commit counting handles non-git directories
- [ ] LOC counting handles missing file types
- [ ] Verification depth scoring is accurate

---

### Phase 3 (-1): Normalization Implementation

**Goal**: Standardize features to [0, 1] range for Euclidean distance

#### Data Structures
```rust
// src/normalization.rs

use crate::features::ToposPoint;
use anyhow::Result;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeatureNormalizer {
    pub means: [f32; 14],
    pub stds: [f32; 14],
}

impl FeatureNormalizer {
    pub fn new() -> Self {
        Self {
            means: [0.0; 14],
            stds: [1.0; 14],
        }
    }

    pub fn fit(&mut self, points: &[ToposPoint]) -> Result<()> {
        if points.is_empty() {
            anyhow::bail!("Cannot fit normalizer with empty dataset");
        }

        // Compute mean for each dimension
        for dim in 0..14 {
            let values: Vec<f32> = points.iter()
                .map(|p| p.get_dimension(dim))
                .collect();
            self.means[dim] = mean(&values);
        }

        // Compute std dev for each dimension
        for dim in 0..14 {
            let values: Vec<f32> = points.iter()
                .map(|p| p.get_dimension(dim))
                .collect();
            self.stds[dim] = std_dev(&values, self.means[dim]);

            // Prevent division by zero
            if self.stds[dim] < 1e-6 {
                self.stds[dim] = 1.0;
            }
        }

        Ok(())
    }

    pub fn transform(&self, point: &ToposPoint) -> [f32; 14] {
        let mut normalized = [0.0_f32; 14];

        for dim in 0..14 {
            let value = point.get_dimension(dim);
            normalized[dim] = (value - self.means[dim]) / self.stds[dim];
        }

        normalized
    }

    pub fn fit_transform(&mut self, points: &[ToposPoint]) -> Result<Vec<[f32; 14]>> {
        self.fit(points)?;
        Ok(points.iter().map(|p| self.transform(p)).collect())
    }
}

fn mean(values: &[f32]) -> f32 {
    if values.is_empty() {
        return 0.0;
    }
    values.iter().sum::<f32>() / values.len() as f32
}

fn std_dev(values: &[f32], mean: f32) -> f32 {
    if values.len() < 2 {
        return 1.0;
    }

    let variance = values.iter()
        .map(|v| {
            let diff = v - mean;
            diff * diff
        })
        .sum::<f32>() / (values.len() - 1) as f32;

    variance.sqrt()
}
```

#### Testing Strategy
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normalization_centers_data() {
        let points = vec![
            ToposPoint {
                n_documents: 10.0,
                total_size_kb: 100.0,
                ..Default::default()
            },
            ToposPoint {
                n_documents: 20.0,
                total_size_kb: 200.0,
                ..Default::default()
            },
            ToposPoint {
                n_documents: 30.0,
                total_size_kb: 300.0,
                ..Default::default()
            },
        ];

        let mut normalizer = FeatureNormalizer::new();
        normalizer.fit(&points).unwrap();

        // Mean of [10, 20, 30] should be 20
        assert!((normalizer.means[0] - 20.0).abs() < 0.01);

        // Normalized values should have mean ~0
        let normalized: Vec<[f32; 14]> = points.iter()
            .map(|p| normalizer.transform(p))
            .collect();

        let normalized_mean = normalized.iter()
            .map(|n| n[0])
            .sum::<f32>() / normalized.len() as f32;

        assert!(normalized_mean.abs() < 0.01);
    }

    #[test]
    fn test_zero_std_dev_handling() {
        // All values identical
        let points = vec![
            ToposPoint {
                has_coq_proofs: 1.0,
                ..Default::default()
            },
            ToposPoint {
                has_coq_proofs: 1.0,
                ..Default::default()
            },
        ];

        let mut normalizer = FeatureNormalizer::new();
        normalizer.fit(&points).unwrap();

        // Should not panic, should use std=1.0
        assert_eq!(normalizer.stds[3], 1.0);
    }
}
```

#### Validation Checklist
- [ ] Mean centering works correctly
- [ ] Standard deviation scaling works
- [ ] Handles constant features (zero std dev)
- [ ] Normalized data has mean ≈ 0, std ≈ 1
- [ ] Serialization/deserialization preserves statistics

---

### Phase 4 (+1): Cover Tree Implementation

**Goal**: Build goko cover tree with golden ratio scale base

#### Data Structures
```rust
// src/cover_tree.rs

use crate::features::ToposPoint;
use crate::normalization::FeatureNormalizer;
use goko::prelude::*;
use std::collections::HashMap;
use std::path::PathBuf;
use anyhow::Result;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToposMetadata {
    pub path: PathBuf,
    pub name: String,
    pub project: String,
    pub features: ToposPoint,
}

pub struct ToposNavigator {
    tree: CoverTree<f32>,
    metadata: HashMap<usize, ToposMetadata>,
    normalizer: FeatureNormalizer,
}

impl ToposNavigator {
    pub fn build(
        points: Vec<ToposPoint>,
        paths: Vec<PathBuf>,
    ) -> Result<Self> {
        if points.len() != paths.len() {
            anyhow::bail!("Points and paths length mismatch");
        }

        // Normalize features
        let mut normalizer = FeatureNormalizer::new();
        let normalized = normalizer.fit_transform(&points)?;

        // Convert to goko format
        let point_cloud: Vec<Vec<f32>> = normalized.iter()
            .map(|arr| arr.to_vec())
            .collect();

        // Build cover tree with golden ratio
        let tree = CoverTreeBuilder::new()
            .set_scale_base(1.618033988749) // Golden ratio φ ✨
            .set_leaf_cutoff(10)           // Pentagonal symmetry
            .set_min_res_index(-20)        // Hierarchical depth
            .set_rng_seed(1069)            // Seed 1069 for determinism
            .build(point_cloud)?;

        // Create metadata map
        let metadata: HashMap<usize, ToposMetadata> = paths.into_iter()
            .enumerate()
            .zip(points.into_iter())
            .map(|((idx, path), features)| {
                let name = path.file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("unknown")
                    .to_string();

                let project = path.parent()
                    .and_then(|p| p.file_name())
                    .and_then(|s| s.to_str())
                    .unwrap_or("unknown")
                    .to_string();

                (idx, ToposMetadata {
                    path,
                    name,
                    project,
                    features,
                })
            })
            .collect();

        Ok(ToposNavigator {
            tree,
            metadata,
            normalizer,
        })
    }

    pub fn save(&self, path: &Path) -> Result<()> {
        let serialized = bincode::serialize(&(
            &self.metadata,
            &self.normalizer,
            // Note: goko tree is not directly serializable
            // Need to save point cloud and rebuild on load
        ))?;

        std::fs::write(path, serialized)?;
        Ok(())
    }

    pub fn load(path: &Path) -> Result<Self> {
        let bytes = std::fs::read(path)?;
        let (metadata, normalizer): (HashMap<usize, ToposMetadata>, FeatureNormalizer) =
            bincode::deserialize(&bytes)?;

        // Rebuild tree from metadata
        let points: Vec<ToposPoint> = (0..metadata.len())
            .map(|i| metadata[&i].features.clone())
            .collect();

        let normalized: Vec<Vec<f32>> = points.iter()
            .map(|p| normalizer.transform(p).to_vec())
            .collect();

        let tree = CoverTreeBuilder::new()
            .set_scale_base(1.618033988749)
            .set_leaf_cutoff(10)
            .set_min_res_index(-20)
            .set_rng_seed(1069)
            .build(normalized)?;

        Ok(ToposNavigator {
            tree,
            metadata,
            normalizer,
        })
    }
}
```

#### Validation Checklist
- [ ] Tree builds with golden ratio (φ = 1.618)
- [ ] Seed 1069 ensures deterministic results
- [ ] Serialization/deserialization works
- [ ] Tree structure is balanced (log depth)
- [ ] Memory usage is O(n × 14) where n = number of .topos/

---

### Phase 5 (+1): Query Interface Implementation

**Goal**: Enable KNN, radius, and text-based searches

#### Data Structures
```rust
// src/queries.rs

use crate::cover_tree::{ToposNavigator, ToposMetadata};
use crate::features::ToposPoint;
use anyhow::Result;

#[derive(Debug, Clone)]
pub struct ToposResult {
    pub path: PathBuf,
    pub project: String,
    pub distance: f32,
    pub features: ToposPoint,
}

impl ToposNavigator {
    /// Find k nearest .topos/ directories to query point
    pub fn knn(&self, query: &[f32; 14], k: usize) -> Result<Vec<ToposResult>> {
        let normalized_query = self.normalize_query(query);

        let results = self.tree.knn(&normalized_query, k)?;

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

    /// Find all .topos/ within semantic radius
    pub fn radius_search(
        &self,
        query: &[f32; 14],
        radius: f32,
    ) -> Result<Vec<ToposResult>> {
        let normalized_query = self.normalize_query(query);

        let results = self.tree.range_query(&normalized_query, radius)?;

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
        let query_vec = self.embed_text(text);
        self.knn(&query_vec, k)
    }

    fn normalize_query(&self, query: &[f32; 14]) -> Vec<f32> {
        query.iter().enumerate()
            .map(|(dim, &val)| {
                (val - self.normalizer.means[dim]) / self.normalizer.stds[dim]
            })
            .collect()
    }

    fn embed_text(&self, text: &str) -> [f32; 14] {
        let mut vec = [0.0_f32; 14];

        let text_lower = text.to_lowercase();

        // D4: Coq proofs
        vec[3] = if text_lower.contains("coq")
            || text_lower.contains("formal")
            || text_lower.contains("proof") {
            1.0
        } else {
            0.0
        };

        // D5: Balanced ternary
        vec[4] = if text_lower.contains("1069")
            || text_lower.contains("balanced ternary")
            || text_lower.contains("seed") {
            1.0
        } else {
            0.0
        };

        // D6: Curriculum
        vec[5] = if text_lower.contains("curriculum")
            || text_lower.contains("tutorial")
            || text_lower.contains("learning") {
            1.0
        } else {
            0.0
        };

        // D7: Specifications
        vec[6] = if text_lower.contains("spec")
            || text_lower.contains("specification")
            || text_lower.contains("architecture") {
            1.0
        } else {
            0.0
        };

        // D11: MCP
        vec[10] = if text_lower.contains("mcp")
            || text_lower.contains("model context")
            || text_lower.contains("protocol") {
            1.0
        } else {
            0.0
        };

        // D12: Rust
        vec[11] = if text_lower.contains("rust")
            || text_lower.contains("cargo")
            || text_lower.contains("rustc") {
            1.0
        } else {
            0.0
        };

        // D13: Functional languages
        vec[12] = if text_lower.contains("ocaml")
            || text_lower.contains("haskell")
            || text_lower.contains("functional") {
            1.0
        } else {
            0.0
        };

        // D14: Verification depth
        vec[13] = if text_lower.contains("verification")
            || text_lower.contains("theorem")
            || text_lower.contains("correctness") {
            0.8
        } else {
            0.0
        };

        vec
    }

    pub fn all_topos(&self) -> Vec<ToposMetadata> {
        self.metadata.values().cloned().collect()
    }
}
```

#### Testing Strategy
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_text_embedding() {
        let navigator = build_test_navigator();

        let results = navigator.query_text("balanced ternary", 5).unwrap();

        // Should find signal-mcp/.topos first
        assert!(results[0].path.to_str().unwrap().contains("signal-mcp"));
    }

    #[test]
    fn test_knn_returns_k_results() {
        let navigator = build_test_navigator();

        let query = [0.0; 14];
        let results = navigator.knn(&query, 5).unwrap();

        assert_eq!(results.len(), 5);
    }
}
```

#### Validation Checklist
- [ ] KNN returns exactly k results
- [ ] Radius search returns all within threshold
- [ ] Text embedding produces sensible queries
- [ ] Query latency is <1ms for 100 .topos/
- [ ] Results are sorted by distance (ascending)

---

### Phase 6 (+1): CLI Implementation

**Goal**: Build user-facing command-line tool

See `GOKO_TOPOS_NAVIGATOR_ARCHITECTURE.md` lines 359-529 for complete CLI specification.

#### Validation Checklist
- [ ] All subcommands work: `index`, `query`, `similar`, `jump`, `list`
- [ ] Help text is clear and concise
- [ ] Error messages are helpful
- [ ] Progress indicators show during long operations
- [ ] Exit codes are correct (0 = success, 1 = error)

---

### Phase 7 (+1): Shell Integration Implementation

**Goal**: Seamless shell integration for instant navigation

See `GOKO_TOPOS_NAVIGATOR_ARCHITECTURE.md` lines 537-577 for complete shell functions.

#### Validation Checklist
- [ ] `topos jump` changes directory correctly
- [ ] `tj` alias works in bash and zsh
- [ ] Shell functions source without errors
- [ ] Tab completion works for subcommands
- [ ] Functions are fast (<100ms)

---

## 📦 Dependencies (Cargo.toml)

```toml
[package]
name = "topos-navigator"
version = "0.1.0"
edition = "2021"

[dependencies]
anyhow = "1.0"
bincode = "1.3"
clap = { version = "4.5", features = ["derive"] }
glob = "0.3"
goko = "0.7"
serde = { version = "1.0", features = ["derive"] }
walkdir = "2.4"

[dev-dependencies]
tempfile = "3.8"
```

---

## 🔢 Balanced Ternary Progress Tracking

### Seed 1069: `[+1, -1, -1, +1, +1, +1, +1]`

**Current Status**:
```
[+1] Phase 1 Discovery:          ⬜ Not Started
[-1] Phase 2 Feature Extraction: ⬜ Not Started
[-1] Phase 3 Normalization:      ⬜ Not Started
[+1] Phase 4 Cover Tree:         ⬜ Not Started
[+1] Phase 5 Query Interface:    ⬜ Not Started
[+1] Phase 6 CLI Tool:           ⬜ Not Started
[+1] Phase 7 Shell Integration:  ⬜ Not Started
```

**Sum = 3**: Net forward progress target
**Length = 7**: Complete implementation in 7 phases

---

## 🚀 Quick Start Command Sequence

```bash
# 1. Create project
cd /Users/barton/ies
cargo new --bin topos-navigator
cd topos-navigator

# 2. Add dependencies
cat >> Cargo.toml <<'EOF'
[dependencies]
anyhow = "1.0"
bincode = "1.3"
clap = { version = "4.5", features = ["derive"] }
glob = "0.3"
goko = "0.7"
serde = { version = "1.0", features = ["derive"] }
walkdir = "2.4"

[dev-dependencies]
tempfile = "3.8"
EOF

# 3. Create module structure
mkdir -p src
touch src/discovery.rs
touch src/features.rs
touch src/normalization.rs
touch src/cover_tree.rs
touch src/queries.rs
touch src/types.rs

# 4. Start with Phase 1
cargo build
cargo test

# 5. Build index
cargo run -- index --roots /Users/barton/ies

# 6. Query
cargo run -- query "balanced ternary" -k 5
```

---

## 📊 Success Metrics

### Performance Targets
- **Discovery**: <5 seconds for entire filesystem
- **Feature Extraction**: <1 second per .topos/
- **Index Build**: <30 seconds for 100 .topos/
- **KNN Query**: <1ms for k=5
- **Text Query**: <10ms including embedding

### Accuracy Targets
- **Text Query Precision@5**: >80% relevant results
- **Similar .topos/ Recall@10**: >90% of manually identified similar directories
- **Feature Extraction Accuracy**: 100% (deterministic)

### Usability Targets
- **CLI Help Time**: <100ms
- **Shell Integration Load**: <50ms
- **Learning Curve**: <5 minutes to basic usage

---

## 🎯 Implementation Order

### Sprint 1 (Week 1): Core Infrastructure
1. Create Rust project
2. Implement Phase 1 (Discovery)
3. Implement Phase 2 (Feature Extraction)
4. Implement Phase 3 (Normalization)
5. Write tests for all three phases

### Sprint 2 (Week 2): Spatial Index
1. Implement Phase 4 (Cover Tree)
2. Add serialization/deserialization
3. Validate golden ratio and seed 1069
4. Write persistence tests

### Sprint 3 (Week 3): Query Interface
1. Implement Phase 5 (Queries)
2. Add KNN, radius, text queries
3. Benchmark query performance
4. Write query tests

### Sprint 4 (Week 4): User Interface
1. Implement Phase 6 (CLI)
2. Implement Phase 7 (Shell Integration)
3. Integration tests
4. Documentation and packaging

---

## 📝 Metadata

**Author**: Barton Rhodes
**Date**: 2025-10-09
**Project**: Goko .topos/ Navigator
**Architecture**: `GOKO_TOPOS_NAVIGATOR_ARCHITECTURE.md`

**Balanced Ternary Signature**:
```
Seed: 1069
Pattern: [+1, -1, -1, +1, +1, +1, +1]
Sum: 3 (net forward progress)
Phases: 7 (complete implementation plan)
Dimensions: 14 (feature space)
Status: IMPLEMENTATION PLAN COMPLETE
Next: Sprint 1 - Core Infrastructure
```

**Success is symbolic coherence, not temporal completion.** ∎
