#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

run() {
  echo "+ $*"
  "$@"
}

run mkdir -p "$ROOT_DIR/artifacts"

if [[ ! -d "$ROOT_DIR/lean/.lake/packages" ]]; then
  run bash -lc "cd \"$ROOT_DIR/lean\" && lake update"
fi
run bash -lc "cd \"$ROOT_DIR/lean\" && lake build"

PY=python
command -v python >/dev/null 2>&1 || PY=python3

run "$PY" "$ROOT_DIR/python/sim_dpi_kl.py"
run "$PY" "$ROOT_DIR/python/sim_idempotence_defect.py"
run "$PY" "$ROOT_DIR/python/sim_failure_modes.py"
run "$PY" "$ROOT_DIR/python/sim_definability_counts.py"

artifacts=(
  "artifacts/dpi_kl_summary.csv"
  "artifacts/dpi_kl_trials.csv"
  "artifacts/dpi_kl_hist.png"
  "artifacts/idempotence_defect.csv"
  "artifacts/idempotence_defect_summary.csv"
  "artifacts/idempotence_defect.png"
  "artifacts/failure_modes.csv"
  "artifacts/failure_modes.png"
  "artifacts/definability_ratio.csv"
  "artifacts/definability_ratio.png"
)

for rel in "${artifacts[@]}"; do
  path="$ROOT_DIR/$rel"
  if [[ ! -s "$path" ]]; then
    echo "Missing or empty artifact: $rel" >&2
    exit 1
  fi
done

echo "OK (research check)"
echo "Artifacts verified:"
for rel in "${artifacts[@]}"; do
  echo "- $rel"
done
