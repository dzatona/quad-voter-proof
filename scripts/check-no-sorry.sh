#!/usr/bin/env bash
# Thin wrapper around scripts/check-no-sorry.py: runs the self-test (proving
# the checker actually catches `sorry -- TODO`-style bypasses of a plain
# `grep -v ':.*--'`, and other comment/modifier tricks — see the docstring
# in check-no-sorry.py), then checks every `.lean` file in `lean/`
# (`lakefile.lean` included — it is Lean DSL, not just config data).
#
# Usage: scripts/check-no-sorry.sh
# This is the same script CI runs (.github/workflows/ci.yml, "No sorry /
# axiom" step) and the one to run locally before every commit that touches
# a `.lean` file. Scope: this project's own `lean/*.lean`. It does not scan
# `rust/src/lib.rs` (Rust has no `axiom`/`sorry`; the crate is instead
# checked by `cargo build`/`clippy`, which reject unknown items) and does
# not scan Aeneas's own stdlib (its pre-existing `sorry`s, in unused
# models, are outside this project — see `reports/PROOF.md`).

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

echo "== self-test =="
python3 scripts/check-no-sorry.py --self-test

echo "== project files (every lean/*.lean) =="
shopt -s nullglob
lean_files=(lean/*.lean)
shopt -u nullglob
python3 scripts/check-no-sorry.py "${lean_files[@]}"
