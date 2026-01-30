#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

run() {
  echo "+ $*"
  "$@"
}

run bash "$ROOT_DIR/scripts/check_physics.sh"
run bash "$ROOT_DIR/scripts/check_foundations.sh"

echo "OK (all checks)"
