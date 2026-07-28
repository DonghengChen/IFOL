#!/usr/bin/env bash
# Launch the Lean 4 REPL with the IFOL project's environment (Mathlib + CLM oleans).
#
# Usage:
#   echo '{"cmd": "import CLM.IFOL\n#check @Formula", "env": null}' | ./run-repl.sh
#
# The REPL reads newline-separated JSON commands on stdin (blank line terminates
# each command) and writes JSON responses to stdout.

set -euo pipefail

PROJ="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPL_DIR="${REPL_DIR:-/home/chen_dongheng/others/repl}"

export PATH="$HOME/.elan/bin:$PATH"

PKGS="$PROJ/lake-packages"
export LEAN_PATH="$PROJ/build/lib:$PKGS/mathlib/build/lib:$PKGS/std/build/lib:$PKGS/aesop/build/lib:$PKGS/Qq/build/lib:$PKGS/proofwidgets/build/lib:$PKGS/Cli/build/lib"
export LD_LIBRARY_PATH="$PROJ/build/lib:${LD_LIBRARY_PATH:-}"

cd "$PROJ"
exec "$REPL_DIR/build/bin/repl" "$@"
