#!/usr/bin/env bash
# Check the two published theorem statements with Lean, NanoDa, and con-ron bundled in the pinned toolchain.
set -euo pipefail
cd "$(dirname "$0")/.."
cfg=$(mktemp)
trap 'rm -f "$cfg"' EXIT
python3 - "$cfg" "$(lean --print-prefix)/bin" <<'PY'
import json
import os
from pathlib import Path
import sys

cfg = json.loads(Path("comparator.json").read_text())
bin_dir = Path(sys.argv[2])
kernels = {"nanoda": bin_dir / "nanoda_bin", "con-ron": bin_dir / "con-ron"}
for checker in kernels.values():
    if not checker.is_file() or not os.access(checker, os.X_OK):
        raise SystemExit(f"Required checker is unavailable: {checker}")
cfg["external_kernels"] = {key: [str(checker)] for key, checker in kernels.items()}
Path(sys.argv[1]).write_text(json.dumps(cfg))
PY
lake comparator --config "$cfg"
