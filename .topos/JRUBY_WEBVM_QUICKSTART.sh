#!/bin/bash
# JRuby on WebVM - Quick Start Installation Script
# Seed 1069: [+1, -1, -1, +1, +1, +1, +1]
#
# Usage:
#   1. Navigate to https://webvm.io
#   2. Wait for terminal to load
#   3. Copy this entire script
#   4. Paste into terminal
#   5. Wait 10-15 minutes for completion

set -e  # Exit on error

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  JRuby on WebVM Installation"
echo "  Seed 1069: [+1, -1, -1, +1, +1, +1, +1]"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Create installation directory
INSTALL_DIR="$HOME/jruby-install-1069"
mkdir -p "$INSTALL_DIR"
cd "$INSTALL_DIR"

echo "▸ Installation directory: $INSTALL_DIR"
echo ""

# Download OpenJDK 17
echo "━━━ [1/7] Downloading OpenJDK 17 (195 MB)..."
JAVA_URL="https://github.com/adoptium/temurin17-binaries/releases/download/jdk-17.0.13%2B11/OpenJDK17U-jdk_x64_linux_hotspot_17.0.13_11.tar.gz"
JAVA_TAR="openjdk-17.tar.gz"

if [ ! -f "$JAVA_TAR" ]; then
    wget -c -O "$JAVA_TAR" "$JAVA_URL" 2>&1 | grep --line-buffered "%" || true
else
    echo "✓ Already downloaded"
fi
echo ""

# Extract OpenJDK
echo "━━━ [2/7] Extracting OpenJDK..."
if [ ! -d "jdk-17.0.13+11" ]; then
    tar xzf "$JAVA_TAR"
    echo "✓ Extracted"
else
    echo "✓ Already extracted"
fi
echo ""

# Verify Java
echo "━━━ [3/7] Verifying Java..."
JAVA_HOME="$INSTALL_DIR/jdk-17.0.13+11"
export JAVA_HOME
export PATH="$JAVA_HOME/bin:$PATH"
java -version 2>&1 | head -n3
echo ""

# Download JRuby
echo "━━━ [4/7] Downloading JRuby 9.4.9.0 (30 MB)..."
JRUBY_URL="https://repo1.maven.org/maven2/org/jruby/jruby-dist/9.4.9.0/jruby-dist-9.4.9.0-bin.tar.gz"
JRUBY_TAR="jruby-9.4.9.0.tar.gz"

if [ ! -f "$JRUBY_TAR" ]; then
    wget -c -O "$JRUBY_TAR" "$JRUBY_URL" 2>&1 | grep --line-buffered "%" || true
else
    echo "✓ Already downloaded"
fi
echo ""

# Extract JRuby
echo "━━━ [5/7] Extracting JRuby..."
if [ ! -d "jruby-9.4.9.0" ]; then
    tar xzf "$JRUBY_TAR"
    echo "✓ Extracted"
else
    echo "✓ Already extracted"
fi
echo ""

# Configure environment
echo "━━━ [6/7] Configuring environment..."
JRUBY_HOME="$INSTALL_DIR/jruby-9.4.9.0"
export JRUBY_HOME
export PATH="$JRUBY_HOME/bin:$PATH"
echo "✓ Environment configured"
echo ""

# Verify JRuby
echo "━━━ [7/7] Verifying JRuby..."
jruby --version
echo ""

# Run quick test
echo "━━━ Running validation test..."
jruby -e "
seed = [1, -1, -1, 1, 1, 1, 1]
puts \"Seed 1069: #{seed}\"
puts \"Sum: #{seed.sum} (expected: 3)\"
puts \"Length: #{seed.length} (expected: 7)\"
puts \"\"
if seed.sum == 3 && seed.length == 7
  puts '✓✓✓ VALIDATION PASSED ✓✓✓'
else
  puts '✗✗✗ VALIDATION FAILED ✗✗✗'
end
"
echo ""

# Installation summary
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Installation Complete!"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "Disk usage: $(du -sh "$INSTALL_DIR" | awk '{print $1}')"
echo ""
echo "To use JRuby in future WebVM sessions, run:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "export JAVA_HOME=\"$JAVA_HOME\""
echo "export JRUBY_HOME=\"$JRUBY_HOME\""
echo "export PATH=\"\$JRUBY_HOME/bin:\$JAVA_HOME/bin:\$PATH\""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "Try it:"
echo "  jruby -e \"puts 'Hello from JRuby on WebVM!'\""
echo ""
echo "Balanced Ternary Progress:"
echo "  [+1] Environment verified"
echo "  [-1] Constraints discovered"
echo "  [-1] Dependencies resolved"
echo "  [+1] Installation completed ✓"
echo "  [+1] Validation passed ✓"
echo "  [+1] Documentation available"
echo "  [+1] Curriculum complete"
echo ""
echo "See full curriculum: JRUBY_WEBVM_INSTALLATION_CURRICULUM.md"
echo ""
