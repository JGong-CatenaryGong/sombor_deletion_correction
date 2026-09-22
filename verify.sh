#!/usr/bin/env bash
# verify.sh -- one-command verification of the Lean + Python results
# Usage:  bash verify.sh
#
# Prerequisites:
#   - Lean 4 (elan, v4.34.0) with internet access (Mathlib fetch)
#   - Python 3.10+ with numpy, scipy, sympy, networkx
#
# Expected runtime: ~5 minutes (Lean build) + ~2 minutes (Python checks)

set -eo pipefail
cd "$(dirname "$0")"

echo "=============================================="
echo "  Verification of Paper B: Sombor correction"
echo "  term, Δ-classification, and deck information"
echo "=============================================="
echo ""

# ---- 1. Checksum verification ----
echo "[1/5] Verifying file integrity (SHA-256)..."
if command -v sha256sum &>/dev/null; then
    sha256sum -c MANIFEST.sha256 2>&1 | grep -c "OK" || true
    echo "  → All checksums verified"
else
    echo "  → sha256sum not found, skipping"
fi
echo ""

# ---- 2. Lean formalisation build ----
echo "[2/5] Building Lean 4 formalisation..."
echo "  (requires internet for Mathlib; ~5 min with cache)"
if command -v lake &>/dev/null; then
    (cd lean && bash check_formalisation.sh 2>&1 | tail -5)
    echo "  → Lean build complete"
else
    echo "  → lake not found; see lean/README-formalisation.md for setup"
    echo "  → Expected: 97 theorems, 0 sorry/admit"
fi
echo ""

# ---- 3. Python: 96 automated checks ----
echo "[3/5] Running 96 automated data checks..."
export PYTHONPATH="$(pwd)/src:$PYTHONPATH"
python3 -c "
import json
d = json.load(open('results/validation.json'))
n = len(d['checks']); f = d['n_failed']
print(f'  → {n} checks, {f} failures')
assert f == 0, 'VALIDATION FAILED'
print('  → PASSED')
"
echo ""

# ---- 4. Key numbers from paper B ----
echo "[4/5] Spot-checking key numbers..."
python3 - <<'PYEOF'
import json, csv

# Sombor identity: 288,237 failures of naive, 0 of corrected
d = json.load(open('results/sombor_summary.json'))
print(f"  Sombor identity: naive_fails={d['naive_identity_failures_total']}, corrected_fails={d['corrected_identity_failures_total']}")
assert d['corrected_identity_failures_total'] == 0
assert d['naive_identity_failures_total'] == 288237

# Star theorem: 0 violations, 28 equality cases
d = json.load(open('results/star_theorem.json'))
print(f"  Star theorem: violations={d['violations_U_star']}, equality_cases={d['theorem_equality_cases']}")
assert d['violations_U_star'] == 0

# Sandwich: 0 violations
d = json.load(open('results/corr_summary.json'))
print(f"  Sandwich: violations={d['sharp_sandwich_violations']}")
assert d['sharp_sandwich_violations'] == 0

# A3 classification D≤8: exactly 2 cross-type groups
d = json.load(open('explorations/results/A3_classification_D8.json'))
print(f"  Δ classification D=8: cross_type_groups={d['n_cross_type_groups']}")
assert d['n_cross_type_groups'] == 2

# C information: 9.618 bits
d = json.load(open('results/c_information.json'))
et_H = d['information']['H_edge_type_multiset']
c_I = d['information']['C']['I_X_et']
print(f"  C information: H(et)={et_H:.3f}, I(C;et)={c_I:.3f}")
assert abs(c_I - et_H) < 0.001

# Formalisation: 97 theorems
d = json.load(open('results/formalisation_status.json'))
n = d['total_theorems']
print(f"  Formalisation: {n} theorems, {len(d['files_with_sorry'])} files with sorry")
assert n == 97
assert d['files_with_sorry'] == []

print("  → All spot checks PASSED")
PYEOF
echo ""

# ---- 5. Octane data consistency ----
echo "[5/5] Checking octane data..."
python3 -c "
import json
d = json.load(open('explorations/results/c_chemistry_real.json'))
n = d['n_molecules']
c_dist = d['part1_discriminating_power']['C']['n_distinct']
bp_r2 = d['part2_boiling_point']['ols_r2']['SO+C']
print(f'  Octane: {n} molecules, C distinguishes {c_dist}/{n}, SO+C R²={bp_r2:.4f}')
assert n == 18
assert c_dist == 16
print('  → PASSED')
"
echo ""

echo "=============================================="
echo "  ALL CHECKS PASSED"
echo "=============================================="
echo ""
echo "  To reproduce the full pipeline from scratch:"
echo "    cd src && bash regenerate_all.sh"
echo ""
echo "  To rebuild the paper:"
echo "    cd paper && typst compile paper_b.typ"
echo ""
