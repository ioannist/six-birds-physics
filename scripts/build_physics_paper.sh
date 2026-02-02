#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
TEX_DIR="$ROOT_DIR/physics/tex"
MAIN="physics_instantiation.tex"
OUT_DIR="$ROOT_DIR/physics/build"

run() {
  echo "+ $*"
  "$@"
}

run rm -rf "$OUT_DIR"
run mkdir -p "$OUT_DIR"
run rm -f "$TEX_DIR/physics_instantiation.pdf"

if ! command -v latexmk >/dev/null 2>&1; then
  echo "Error: latexmk not found in PATH." >&2
  exit 1
fi

PY=python
if ! command -v python >/dev/null 2>&1; then
  PY=python3
fi

run "$PY" "$ROOT_DIR/physics/python/export_figures_for_tex.py"
run "$PY" "$ROOT_DIR/physics/python/export_tables_for_tex.py"
run "$PY" "$ROOT_DIR/physics/python/export_repro_appendix.py"
run "$PY" "$ROOT_DIR/physics/python/export_lean_appendix.py"

run bash -lc "cd \"$TEX_DIR\" && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=\"$OUT_DIR\" \"$MAIN\""

# Generate flattened TeX file
FLAT_TEX="$OUT_DIR/physics_instantiation_flat.tex"
if command -v latexpand >/dev/null 2>&1; then
  run bash -c "cd \"$TEX_DIR\" && latexpand \"$MAIN\" > \"$FLAT_TEX\""
  echo "Flattened TeX: physics/build/physics_instantiation_flat.tex"
else
  echo "Warning: latexpand not found, skipping flattened TeX generation" >&2
fi

if [ ! -s "$OUT_DIR/physics_instantiation.pdf" ]; then
  echo "Error: PDF not produced or empty: $OUT_DIR/physics_instantiation.pdf" >&2
  exit 1
fi

run bash "$ROOT_DIR/physics/scripts/tex_lint.sh"

echo "PDF: physics/build/physics_instantiation.pdf"
