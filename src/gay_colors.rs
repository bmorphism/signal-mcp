//! Gay.jl-style deterministic color seeds for Signal threads
//!
//! Each conversation/thread has a unique seed → 6-color LCH palette
//! Strong Parallelism Invariance (SPI): same seed = same colors always
//!
//! # Perspectival World Model
//!
//! "Almost-hive-mind lobotomized discarded appendages of history" =
//! each participant sees thread colors from their own perspective,
//! but colors are jointly verified via shared seed.

use std::collections::HashMap;

/// SplitMix64 - same algorithm as Gay.jl/SplittableRandoms.jl
#[derive(Clone, Debug)]
pub struct GayRNG {
    state: u64,
    seed: u64,
    invocation: u64,
}

impl GayRNG {
    /// Default seed: "gay_colo" as bytes (matches Gay.jl GAY_SEED)
    pub const GAY_SEED: u64 = 0x6761795f636f6c6f;
    
    pub fn new(seed: u64) -> Self {
        Self { state: seed, seed, invocation: 0 }
    }
    
    /// Split the RNG for SPI (Strong Parallelism Invariance)
    pub fn split(&mut self) -> u64 {
        self.invocation += 1;
        let mut z = self.state.wrapping_add(0x9e3779b97f4a7c15);
        self.state = z;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    
    /// Get float in [0, 1)
    pub fn next_f64(&mut self) -> f64 {
        self.split() as f64 / u64::MAX as f64
    }
}

/// LCH color (Lightness, Chroma, Hue)
#[derive(Clone, Copy, Debug)]
pub struct LCH {
    pub l: f64, // 0-100
    pub c: f64, // 0-100
    pub h: f64, // 0-360
}

/// RGB color (0-255 per channel)
#[derive(Clone, Copy, Debug)]
pub struct RGB {
    pub r: u8,
    pub g: u8,
    pub b: u8,
}

impl LCH {
    /// Convert LCH to RGB via Lab → XYZ → sRGB
    pub fn to_rgb(&self) -> RGB {
        let h_rad = self.h.to_radians();
        let a = self.c * h_rad.cos();
        let b = self.c * h_rad.sin();
        
        let fy = (self.l + 16.0) / 116.0;
        let fx = a / 500.0 + fy;
        let fz = fy - b / 200.0;
        
        let delta = 6.0 / 29.0;
        let xn = 0.95047;
        let yn = 1.0;
        let zn = 1.08883;
        
        let finv = |t: f64, n: f64| -> f64 {
            if t > delta { n * t.powi(3) } 
            else { (t - 16.0/116.0) * 3.0 * delta * delta * n }
        };
        
        let x = finv(fx, xn);
        let y = finv(fy, yn);
        let z = finv(fz, zn);
        
        // XYZ to sRGB
        let r_linear = 3.2404542 * x - 1.5371385 * y - 0.4985314 * z;
        let g_linear = -0.969266 * x + 1.8760108 * y + 0.041556 * z;
        let b_linear = 0.0556434 * x - 0.2040259 * y + 1.0572252 * z;
        
        let gamma = |v: f64| -> f64 {
            if v > 0.0031308 { 1.055 * v.powf(1.0/2.4) - 0.055 }
            else { 12.92 * v }
        };
        
        let clamp = |v: f64| -> u8 {
            (v.clamp(0.0, 1.0) * 255.0).round() as u8
        };
        
        RGB {
            r: clamp(gamma(r_linear)),
            g: clamp(gamma(g_linear)),
            b: clamp(gamma(b_linear)),
        }
    }
}

impl RGB {
    pub fn to_hex(&self) -> String {
        format!("#{:02x}{:02x}{:02x}", self.r, self.g, self.b)
    }
    
    /// ANSI truecolor escape sequence
    pub fn fg_ansi(&self) -> String {
        format!("\x1b[38;2;{};{};{}m", self.r, self.g, self.b)
    }
    
    pub fn bg_ansi(&self) -> String {
        format!("\x1b[48;2;{};{};{}m", self.r, self.g, self.b)
    }
}

/// Thread color palette (6 colors from seed)
#[derive(Clone, Debug)]
pub struct ThreadPalette {
    pub seed: u64,
    pub colors: [LCH; 6],
}

impl ThreadPalette {
    /// Generate palette from seed (SPI: deterministic)
    pub fn from_seed(seed: u64) -> Self {
        let mut rng = GayRNG::new(seed);
        let mut colors = [LCH { l: 0.0, c: 0.0, h: 0.0 }; 6];
        
        for i in 0..6 {
            colors[i] = LCH {
                l: rng.next_f64() * 100.0,
                c: rng.next_f64() * 100.0,
                h: rng.next_f64() * 360.0,
            };
        }
        
        Self { seed, colors }
    }
    
    /// Generate seed from conversation UUID
    pub fn seed_from_uuid(uuid: &str) -> u64 {
        // FNV-1a hash
        let mut hash: u64 = 0xcbf29ce484222325;
        for byte in uuid.bytes() {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash
    }
    
    /// Get RGB colors
    pub fn rgb_colors(&self) -> [RGB; 6] {
        let mut rgbs = [RGB { r: 0, g: 0, b: 0 }; 6];
        for i in 0..6 {
            rgbs[i] = self.colors[i].to_rgb();
        }
        rgbs
    }
}

/// Self-coloring thread state for perspectival world model
#[derive(Clone, Debug)]
pub struct SelfColoringThread {
    pub conversation_id: String,
    pub palette: ThreadPalette,
    pub participants: Vec<String>,
    /// Each participant's color index (0-5)
    pub participant_colors: HashMap<String, usize>,
    /// Admin color (gold/primary)
    pub admin_color_idx: usize,
}

impl SelfColoringThread {
    pub fn new(conversation_id: &str, participants: Vec<String>) -> Self {
        let seed = ThreadPalette::seed_from_uuid(conversation_id);
        let palette = ThreadPalette::from_seed(seed);
        
        // Assign colors to participants (mod 6)
        let mut participant_colors = HashMap::new();
        for (i, p) in participants.iter().enumerate() {
            participant_colors.insert(p.clone(), i % 6);
        }
        
        Self {
            conversation_id: conversation_id.to_string(),
            palette,
            participants,
            participant_colors,
            admin_color_idx: 0, // First color = admin
        }
    }
    
    /// Get ANSI-colored participant name
    pub fn colored_name(&self, participant: &str) -> String {
        let idx = self.participant_colors.get(participant).copied().unwrap_or(0);
        let rgb = self.palette.colors[idx].to_rgb();
        format!("{}{}\x1b[0m", rgb.fg_ansi(), participant)
    }
}

/// Poll action with colored options
#[derive(Clone, Debug)]
pub struct ColoredPoll {
    pub question: String,
    pub options: Vec<String>,
    pub palette: ThreadPalette,
    pub votes: HashMap<String, usize>, // participant -> option_idx
}

impl ColoredPoll {
    pub fn new(question: &str, options: Vec<String>, seed: u64) -> Self {
        Self {
            question: question.to_string(),
            options,
            palette: ThreadPalette::from_seed(seed),
            votes: HashMap::new(),
        }
    }
    
    /// Render poll with colored options
    pub fn render(&self) -> String {
        let mut out = format!("📊 {}\n", self.question);
        for (i, opt) in self.options.iter().enumerate() {
            let rgb = self.palette.colors[i % 6].to_rgb();
            let count = self.votes.values().filter(|&&v| v == i).count();
            out.push_str(&format!("  {}[{}] {}\x1b[0m ({} votes)\n", 
                rgb.fg_ansi(), i + 1, opt, count));
        }
        out
    }
}

/// Admin action (assign/revoke) as semantic operation
#[derive(Clone, Debug)]
pub enum AdminAction {
    AssignAdmin { target: String, by: String },
    RevokeAdmin { target: String, by: String },
}

impl AdminAction {
    /// Color-coded action string
    pub fn render(&self, thread: &SelfColoringThread) -> String {
        match self {
            AdminAction::AssignAdmin { target, by } => {
                format!("👑 {} granted admin to {}", 
                    thread.colored_name(by), thread.colored_name(target))
            }
            AdminAction::RevokeAdmin { target, by } => {
                format!("🚫 {} revoked admin from {}", 
                    thread.colored_name(by), thread.colored_name(target))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_splitmix64_determinism() {
        let mut rng1 = GayRNG::new(42);
        let mut rng2 = GayRNG::new(42);
        
        for _ in 0..100 {
            assert_eq!(rng1.split(), rng2.split());
        }
    }
    
    #[test]
    fn test_thread_palette_determinism() {
        let p1 = ThreadPalette::from_seed(0xDEADBEEF);
        let p2 = ThreadPalette::from_seed(0xDEADBEEF);
        
        for i in 0..6 {
            assert_eq!(p1.colors[i].l, p2.colors[i].l);
            assert_eq!(p1.colors[i].c, p2.colors[i].c);
            assert_eq!(p1.colors[i].h, p2.colors[i].h);
        }
    }
    
    #[test]
    fn test_uuid_to_seed() {
        let uuid = "T-019b0a69-a672-7199-b12c-aa0f8f934fd7";
        let seed = ThreadPalette::seed_from_uuid(uuid);
        assert_ne!(seed, 0);
        // Reproducible
        assert_eq!(seed, ThreadPalette::seed_from_uuid(uuid));
    }
}
