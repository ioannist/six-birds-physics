#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
TEX_DIR="$ROOT_DIR/physics/tex"
OUT_DIR="$ROOT_DIR/physics/build"
LOG="$OUT_DIR/physics_instantiation.log"

mkdir -p "$OUT_DIR"

err_count=0

# Check for '??' placeholders (error)
qq_matches=$(rg -n '\?\?' "$TEX_DIR" --glob='*.tex' --glob='!autogen/**' || true)
qq_count=$(printf "%s" "$qq_matches" | sed '/^$/d' | wc -l | tr -d ' ')
if [ "$qq_count" -gt 0 ]; then
  echo "ERROR: Found ?? placeholders in TeX sources (showing up to 50):"
  printf "%s" "$qq_matches" | head -n 50
  err_count=$((err_count + 1))
fi

# Check for T-O-D-O markers (error)
todo_pat="\\\\TO""DO|TO""DO:"
todo_matches=$(rg -n "$todo_pat" "$TEX_DIR" --glob='*.tex' --glob='!autogen/**' || true)
todo_count=$(printf "%s" "$todo_matches" | sed '/^$/d' | wc -l | tr -d ' ')
if [ "$todo_count" -gt 0 ]; then
  echo "ERROR: Found T-O-D-O markers in TeX sources (showing up to 50):"
  printf "%s" "$todo_matches" | head -n 50
  err_count=$((err_count + 1))
fi

# Undefined references/citations from log (error)
undef_matches=""
undef_count=0
if [ -f "$LOG" ]; then
  undef_matches=$(rg -n 'LaTeX Warning: (Citation|Reference).*undefined|There were undefined references|There were undefined citations|undefined citations' "$LOG" || true)
  undef_count=$(printf "%s" "$undef_matches" | sed '/^$/d' | wc -l | tr -d ' ')
  if [ "$undef_count" -gt 0 ]; then
    echo "ERROR: Found undefined references/citations in build log (showing up to 80):"
    printf "%s" "$undef_matches" | head -n 80
    err_count=$((err_count + 1))
  fi
else
  echo "WARNING: Log not found at $LOG; run build first."
fi

status="PASS"
if [ "$err_count" -gt 0 ]; then
  status="FAIL"
fi

TO="TO"
DO="DO"
echo "SUMMARY: ??=$qq_count ${TO}${DO}=$todo_count undefined=$undef_count status=$status"

if [ "$err_count" -gt 0 ]; then
  exit 1
fi
