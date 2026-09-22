#!/usr/bin/env bash
# regenerate_all.sh -- regenerate every derived result file and then the report.
#
# The pipeline is deterministic (fixed random seeds; the deck/combo/report steps
# use no randomness) and is meant to be run after any change to src/ that can
# alter results.  Each step appends to logs/regenerate.log.
#
# Usage:  bash src/regenerate_all.sh [--skip-slow]
#   --skip-slow   skip delta_exact.py (~20 min) and sombor_analysis.py (~4 min)
set -u
cd "$(dirname "$0")/.."
export PYTHONPATH="$PWD/.pylibs:$PWD/src"
LOG=logs/regenerate.log
: > "$LOG"
SKIP_SLOW=0
[ "${1:-}" = "--skip-slow" ] && SKIP_SLOW=1

run () {                      # run <label> <command...>
  local label="$1"; shift
  echo "=== [$label] $*" | tee -a "$LOG"
  if "$@" >> "$LOG" 2>&1; then
    echo "    ok" | tee -a "$LOG"
  else
    echo "    FAILED (exit $?)" | tee -a "$LOG"
    return 1
  fi
}

run "decks/edge"   python3 src/compute_decks.py --graphs results/graphs.jsonl.gz \
                        --out results/deck_edge.jsonl.gz --workers 22
run "decks/vertex" python3 src/compute_decks.py --graphs results/graphs.jsonl.gz \
                        --out results/deck_vertex.jsonl.gz --kind vertex --workers 20
run "collisions/edge"   python3 src/analyze_collisions.py --kind edge
run "collisions/vertex" python3 src/analyze_collisions.py --kind vertex \
                        --out results/invariant_collisions_vertex.csv \
                        --examples results/collision_examples_vertex.json
run "reconstruct"  python3 src/reconstruct_check.py
run "determine"    python3 src/determination_matrix.py
run "determine_m4" python3 src/determination_matrix.py --sets chem_m4_n9,conn_m4_n9 \
                        --out results/determination_matrix_m4.csv
run "determine_C"  python3 src/determination_matrix.py --sets chem_n9,chem_m4_n9,conn_n9,conn_m4_n9 \
                        --out results/determination_matrix_C.csv
run "combos"       python3 src/analyze_combos.py
run "general_id"   python3 src/general_identity.py
run "corr"         python3 src/corr_analysis.py
run "framework"    python3 src/framework_analysis.py
run "star"         python3 src/star_theorem.py
run "spectral"     python3 src/spectral_products.py
run "c_info"       python3 src/c_information.py
run "deck_degree"  python3 src/deck_degree_check.py
run "symbolic"     python3 src/symbolic_certificates.py
run "adversarial"  python3 src/adversarial_check.py
run "witnesses"    python3 src/verify_witnesses.py
run "audit"        python3 src/audit_inequalities.py
run "naive_id"     python3 src/naive_identity_check.py
run "bounds"       python3 src/bound_comparison.py
run "regular"      python3 src/regular_closed_form.py
if [ "$SKIP_SLOW" = "0" ]; then
  run "sombor"     python3 src/sombor_analysis.py
  run "delta_exact" python3 src/delta_exact.py
fi
run "coinc_class"  python3 src/coincidence_classification.py
run "validate"     python3 src/validate.py
run "formal"       python3 src/formalisation_status.py
run "plots"        python3 src/plots.py
run "report"       python3 src/make_report.py
echo "=== done" | tee -a "$LOG"
