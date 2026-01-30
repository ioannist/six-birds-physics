#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REQUIRED_FILE="$ROOT_DIR/physics/artifacts/required_artifacts.txt"
PY=python
command -v python >/dev/null 2>&1 || PY=python3

run() {
  echo "+ $*"
  "$@"
}

run mkdir -p "$ROOT_DIR/physics/artifacts"
export MPLBACKEND=Agg

if [[ ! -f "$REQUIRED_FILE" ]]; then
  echo "Missing required artifacts list: physics/artifacts/required_artifacts.txt" >&2
  exit 1
fi

while IFS= read -r rel_path; do
  rel_path="${rel_path%$'\r'}"
  [[ -z "$rel_path" ]] && continue
  [[ "$rel_path" =~ ^# ]] && continue
  run rm -f "$ROOT_DIR/$rel_path"
done < "$REQUIRED_FILE"

if [[ ! -d "$ROOT_DIR/lean/.lake/packages" ]]; then
  run bash -lc "cd \"$ROOT_DIR/lean\" && lake update"
fi

run bash -lc "cd \"$ROOT_DIR/lean\" && lake build"
run "$PY" -m compileall "$ROOT_DIR/physics/python"
run "$PY" "$ROOT_DIR/physics/python/run_all.py"
run "$PY" "$ROOT_DIR/physics/scripts/check_physics_artifacts.py"

echo "Verified required physics artifacts:"
cat "$REQUIRED_FILE"
echo "OK (physics check)"
