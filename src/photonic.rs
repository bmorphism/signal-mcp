//! Photonic Channels: IOWN APN-inspired wavelength-colored transport
//!
//! NTT's All-Photonics Network provides end-to-end optical paths.
//! We model this as color-preserving channels with SPI guarantees.
//!
//! # APN Targets (2030)
//! - 100x power efficiency → mode collapse reduces verification overhead
//! - 125x capacity → wavelength multiplexing = parallel color channels
//! - 1/200 latency → end-to-end optical = no protocol stack traversal
//!
//! # Correspondence
//!
//! | APN | Chromatic Model |
//! |-----|-----------------|
//! | Wavelength λ | ZXColor channel |
//! | Multi-core fiber | GayInterleaver streams |
//! | WDM (35 waves) | 35-color palette |
//! | 1 Pbit/s per fiber | Aggregate channel capacity |
//! | Digital twin | Reafferent state mirror |

use crate::gay_loom::{GayRNG, ZXColor, ColorSignature};
use crate::gay_bridge::GAY_SEED;
use std::collections::HashMap;

/// Optical wavelength as color channel
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Wavelength {
    pub index: usize,      // Channel index (0-34 for 35-wave WDM)
    pub color: ZXColor,    // Parity-based color
    pub lambda_nm: f64,    // Physical wavelength in nm (C-band: 1530-1565nm)
}

impl Eq for Wavelength {}

impl std::hash::Hash for Wavelength {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.color.hash(state);
    }
}

impl Wavelength {
    /// Create wavelength in C-band (1530-1565nm range)
    pub fn c_band(index: usize) -> Self {
        let lambda_nm = 1530.0 + (index as f64) * (35.0 / 35.0); // ~1nm spacing
        Self {
            index,
            color: ZXColor::from_parity(index as u64),
            lambda_nm,
        }
    }
    
    /// NTT's 35-wave WDM configuration
    pub fn ntt_wdm_35() -> Vec<Self> {
        (0..35).map(Self::c_band).collect()
    }
}

/// Multi-core fiber: multiple independent color streams
#[derive(Clone, Debug)]
pub struct MultiCoreFiber {
    pub n_cores: usize,
    pub cores: Vec<FiberCore>,
    pub aggregate_capacity_tbps: f64,
}

#[derive(Clone, Debug)]
pub struct FiberCore {
    pub core_id: usize,
    pub wavelengths: Vec<Wavelength>,
    pub rng: GayRNG,
    pub capacity_tbps: f64,
}

impl MultiCoreFiber {
    /// Create NTT-style multi-core fiber
    /// Target: 1 Pbit/s = 1000 Tbit/s per fiber
    pub fn new(n_cores: usize, seed: u64) -> Self {
        let capacity_per_core = 1000.0 / n_cores as f64; // Distribute 1 Pbit/s
        
        let cores: Vec<_> = (0..n_cores)
            .map(|i| {
                let core_seed = seed ^ ((i as u64).wrapping_mul(0x9e3779b97f4a7c15));
                FiberCore {
                    core_id: i,
                    wavelengths: Wavelength::ntt_wdm_35(),
                    rng: GayRNG::new(core_seed),
                    capacity_tbps: capacity_per_core,
                }
            })
            .collect();
        
        Self {
            n_cores,
            cores,
            aggregate_capacity_tbps: 1000.0,
        }
    }
    
    /// Get core by color parity (load balancing via chromatic routing)
    pub fn route_by_color(&self, color: ZXColor) -> &FiberCore {
        let idx = match color {
            ZXColor::Green => 0,
            ZXColor::Red => self.n_cores / 2,
        };
        &self.cores[idx % self.n_cores]
    }
    
    /// Color signature across all cores
    pub fn fiber_signature(&self) -> ColorSignature {
        let colors: Vec<_> = self.cores.iter()
            .flat_map(|c| c.wavelengths.iter().map(|w| w.color))
            .collect();
        ColorSignature::from_trace(&colors)
    }
}

/// End-to-end optical path (APN core concept)
#[derive(Clone, Debug)]
pub struct OpticalPath {
    pub source: PathEndpoint,
    pub destination: PathEndpoint,
    pub wavelength: Wavelength,
    pub hops: Vec<PhotonicNode>,
    pub latency_us: f64,
}

#[derive(Clone, Debug)]
pub struct PathEndpoint {
    pub id: String,
    pub location: String,
}

#[derive(Clone, Debug)]
pub struct PhotonicNode {
    pub id: String,
    pub node_type: PhotonicNodeType,
    pub color_preserving: bool, // True = no O-E-O conversion
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PhotonicNodeType {
    Transponder,    // O-E-O conversion (breaks color)
    ROADM,          // Reconfigurable optical add-drop (preserves color)
    Amplifier,      // EDFA (preserves color)
    Regenerator,    // 3R regeneration (may shift color)
}

impl OpticalPath {
    /// Check if path is all-optical (no O-E-O conversion)
    pub fn is_all_optical(&self) -> bool {
        self.hops.iter().all(|n| n.color_preserving)
    }
    
    /// Calculate latency (target: 1/200 of current)
    /// Speed of light in fiber: ~200,000 km/s = 5 μs/km
    pub fn calculate_latency_us(&self, distance_km: f64) -> f64 {
        let propagation = distance_km * 5.0; // μs
        let processing: f64 = self.hops.iter()
            .map(|n| match n.node_type {
                PhotonicNodeType::ROADM => 0.1,      // All-optical: minimal
                PhotonicNodeType::Amplifier => 0.01, // Nearly zero
                PhotonicNodeType::Transponder => 10.0, // O-E-O: significant
                PhotonicNodeType::Regenerator => 5.0,
            })
            .sum();
        propagation + processing
    }
    
    /// Color preservation check
    pub fn color_fidelity(&self) -> f64 {
        let preserving = self.hops.iter()
            .filter(|n| n.color_preserving)
            .count();
        preserving as f64 / self.hops.len() as f64
    }
}

/// Digital Twin: real-time color-synchronized mirror
#[derive(Clone, Debug)]
pub struct DigitalTwin {
    pub physical_id: String,
    pub twin_id: String,
    pub sync_channel: Wavelength,
    pub state_signature: ColorSignature,
    pub latency_us: f64,
    pub fidelity: f64,
}

impl DigitalTwin {
    pub fn new(physical_id: &str, twin_id: &str, channel_idx: usize) -> Self {
        Self {
            physical_id: physical_id.to_string(),
            twin_id: twin_id.to_string(),
            sync_channel: Wavelength::c_band(channel_idx),
            state_signature: ColorSignature::from_trace(&[]),
            latency_us: 0.0,
            fidelity: 1.0,
        }
    }
    
    /// Sync state via color signature (reafferent verification)
    pub fn sync(&mut self, physical_state: &[ZXColor], path: &OpticalPath) {
        self.state_signature = ColorSignature::from_trace(physical_state);
        self.latency_us = path.latency_us;
        self.fidelity = path.color_fidelity();
    }
    
    /// Verify twin matches physical (O(1) via signature)
    pub fn verify(&self, expected: &ColorSignature) -> bool {
        self.state_signature.fingerprint == expected.fingerprint
    }
}

/// APN Service Level (IOWN 1.0, 2.0, etc.)
#[derive(Clone, Copy, Debug)]
pub struct APNServiceLevel {
    pub version: f32,
    pub power_efficiency_x: f64,
    pub capacity_x: f64,
    pub latency_reduction: f64,
}

impl APNServiceLevel {
    /// IOWN 1.0 (March 2023)
    pub fn iown_1_0() -> Self {
        Self {
            version: 1.0,
            power_efficiency_x: 10.0,
            capacity_x: 12.5,
            latency_reduction: 0.1, // 1/10 latency
        }
    }
    
    /// IOWN 2030 targets
    pub fn iown_2030() -> Self {
        Self {
            version: 3.0,
            power_efficiency_x: 100.0,
            capacity_x: 125.0,
            latency_reduction: 0.005, // 1/200 latency
        }
    }
    
    /// Calculate effective metrics
    pub fn effective_latency(&self, base_latency_us: f64) -> f64 {
        base_latency_us * self.latency_reduction
    }
    
    pub fn effective_capacity(&self, base_tbps: f64) -> f64 {
        base_tbps * self.capacity_x
    }
}

/// NTT experiment results
pub mod ntt_experiments {
    use super::*;
    
    /// 2019: 1 Tbit/s × 35 waves laboratory
    pub fn lab_2019() -> (f64, usize) {
        (1.0, 35) // 1 Tbit/s per wavelength, 35 waves = 35 Tbit/s
    }
    
    /// 2023: 1.2 Tbps × 336 km field trial
    pub fn field_2023() -> (f64, f64) {
        (1.2, 336.0) // 1.2 Tbit/s per wavelength, 336 km distance
    }
    
    /// Target: 1 Pbit/s per fiber via multi-core
    pub fn target_pbit() -> f64 {
        1000.0 // Tbit/s = 1 Pbit/s
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_wavelength_c_band() {
        let waves = Wavelength::ntt_wdm_35();
        assert_eq!(waves.len(), 35);
        
        // Check C-band range
        for w in &waves {
            assert!(w.lambda_nm >= 1530.0 && w.lambda_nm <= 1565.0);
        }
        
        // Check alternating colors
        let green = waves.iter().filter(|w| w.color == ZXColor::Green).count();
        let red = waves.iter().filter(|w| w.color == ZXColor::Red).count();
        // Should be roughly balanced
        assert!((green as i32 - red as i32).abs() <= 1);
    }
    
    #[test]
    fn test_multi_core_fiber() {
        let fiber = MultiCoreFiber::new(7, GAY_SEED); // 7-core fiber
        
        assert_eq!(fiber.n_cores, 7);
        assert_eq!(fiber.aggregate_capacity_tbps, 1000.0); // 1 Pbit/s
        
        // Each core has 35 wavelengths
        for core in &fiber.cores {
            assert_eq!(core.wavelengths.len(), 35);
        }
        
        // Signature should be deterministic
        let sig1 = fiber.fiber_signature();
        let fiber2 = MultiCoreFiber::new(7, GAY_SEED);
        let sig2 = fiber2.fiber_signature();
        assert_eq!(sig1.fingerprint, sig2.fingerprint);
    }
    
    #[test]
    fn test_optical_path_latency() {
        let path = OpticalPath {
            source: PathEndpoint { id: "tokyo".into(), location: "NTT EAST".into() },
            destination: PathEndpoint { id: "osaka".into(), location: "NTT WEST".into() },
            wavelength: Wavelength::c_band(0),
            hops: vec![
                PhotonicNode { id: "amp1".into(), node_type: PhotonicNodeType::Amplifier, color_preserving: true },
                PhotonicNode { id: "roadm1".into(), node_type: PhotonicNodeType::ROADM, color_preserving: true },
                PhotonicNode { id: "amp2".into(), node_type: PhotonicNodeType::Amplifier, color_preserving: true },
            ],
            latency_us: 0.0,
        };
        
        // NTT field trial: 336 km
        let latency = path.calculate_latency_us(336.0);
        assert!(latency > 1680.0); // At least propagation delay
        assert!(latency < 1700.0); // Minimal processing for all-optical
        
        assert!(path.is_all_optical());
        assert_eq!(path.color_fidelity(), 1.0);
    }
    
    #[test]
    fn test_digital_twin_sync() {
        let mut twin = DigitalTwin::new("physical-sensor", "digital-twin", 0);
        
        let physical_state = vec![ZXColor::Green, ZXColor::Red, ZXColor::Green];
        let path = OpticalPath {
            source: PathEndpoint { id: "sensor".into(), location: "field".into() },
            destination: PathEndpoint { id: "twin".into(), location: "cloud".into() },
            wavelength: Wavelength::c_band(0),
            hops: vec![
                PhotonicNode { id: "roadm".into(), node_type: PhotonicNodeType::ROADM, color_preserving: true },
            ],
            latency_us: 100.0,
        };
        
        twin.sync(&physical_state, &path);
        
        let expected = ColorSignature::from_trace(&physical_state);
        assert!(twin.verify(&expected));
    }
    
    #[test]
    fn test_apn_service_levels() {
        let iown1 = APNServiceLevel::iown_1_0();
        let iown2030 = APNServiceLevel::iown_2030();
        
        // Base latency 1000 μs
        let base = 1000.0;
        
        assert_eq!(iown1.effective_latency(base), 100.0);      // 1/10
        assert_eq!(iown2030.effective_latency(base), 5.0);     // 1/200
        
        // Capacity growth
        assert_eq!(iown2030.capacity_x / iown1.capacity_x, 10.0); // 10x from 1.0 to 2030
    }
}
