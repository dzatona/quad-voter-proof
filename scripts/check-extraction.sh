#!/usr/bin/env bash
# Re-runs Charon and Aeneas at the pins recorded in reports/TOOLCHAIN.md and
# fails if the freshly generated LLBC / Lean differ from what is committed.
#
# This is the freshness gate described in reports/TOOLCHAIN.md's
# "scripts/check-extraction.sh requirements" section: CI does not run
# Charon/Aeneas (they are not installable in a few CI minutes; see
# reports/TOOLCHAIN.md), so this script is how a human (or an agent, before
# every commit that touches rust/src/lib.rs) checks that
# llbc/quad_voter_proof.llbc and lean/QuadVoterProof.lean are not stale.
#
# Usage: scripts/check-extraction.sh
# Requires: charon (909ff09a) on PATH or at $HOME/charon/bin/charon,
#           aeneas (c2015b86) at $HOME/aeneas/bin/aeneas (AENEAS_BIN
#           overrides), an opam switch with Aeneas's OCaml deps.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

charon_bin="${CHARON_BIN:-}"
if [ -z "$charon_bin" ]; then
  if command -v charon >/dev/null 2>&1; then
    charon_bin="$(command -v charon)"
  elif [ -x "$HOME/charon/bin/charon" ]; then
    charon_bin="$HOME/charon/bin/charon"
  else
    echo "error: charon not found (set CHARON_BIN, or install per reports/TOOLCHAIN.md)" >&2
    exit 1
  fi
fi

aeneas_bin="${AENEAS_BIN:-$HOME/aeneas/bin/aeneas}"
if [ ! -x "$aeneas_bin" ]; then
  echo "error: aeneas not found at $aeneas_bin (set AENEAS_BIN, or install per reports/TOOLCHAIN.md)" >&2
  exit 1
fi

echo "== charon: $("$charon_bin" version)"
echo "== aeneas: $("$aeneas_bin" -version)"

work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT

fresh_llbc="$work_dir/quad_voter_proof.llbc"
fresh_lean_dir="$work_dir/lean"
mkdir -p "$fresh_lean_dir"

echo "== cargo test (rust/)"
(cd "$repo_root/rust" && cargo test --quiet)

echo "== charon cargo --preset=aeneas"
(
  cd "$repo_root/rust"
  PATH="$(dirname "$charon_bin"):$PATH" "$charon_bin" cargo --preset=aeneas --dest-file "$fresh_llbc"
)

if command -v opam >/dev/null 2>&1 && opam env --switch=5.3.0 >/dev/null 2>&1; then
  eval "$(opam env --switch=5.3.0)"
fi

echo "== aeneas -backend lean"
"$aeneas_bin" -backend lean -dest "$fresh_lean_dir" "$fresh_llbc"

status=0

# Charon's LLBC JSON is not byte-reproducible across runs of the identical
# crate: `translated.options.dest_file` records the (necessarily different,
# since this script writes to a scratch path) output path, and the
# `short_names` / `item_names` / `assoc_item_names` debug-naming tables come
# out in a different list order each run (observed directly: two consecutive
# `charon cargo --preset=aeneas` runs on an unmodified crate produced
# differently-ordered name tables but byte-identical `fun_decls` /
# `type_decls` / `global_decls` / `trait_decls` / `trait_impls` /
# `ordered_decls`, and Aeneas produced a byte-identical generated Lean file
# from both). So this compares the LLBC ignoring exactly those two things —
# the destination-path field and the order of the three naming tables — not
# a looser check on anything that affects the extracted program.
echo "== diff: llbc/quad_voter_proof.llbc (semantic: ignores dest_file path and debug name-table order)"
if ! python3 "$repo_root/scripts/normalize-llbc-diff.py" \
    "$repo_root/llbc/quad_voter_proof.llbc" "$fresh_llbc"; then
  echo "STALE: committed llbc/quad_voter_proof.llbc differs from a fresh Charon run" >&2
  status=1
else
  echo "fresh (matches committed)"
fi

echo "== diff: lean/QuadVoterProof.lean"
if ! diff -q "$repo_root/lean/QuadVoterProof.lean" "$fresh_lean_dir/QuadVoterProof.lean" >/dev/null 2>&1; then
  echo "STALE: committed lean/QuadVoterProof.lean differs from a fresh Aeneas run" >&2
  status=1
else
  echo "fresh (matches committed)"
fi

exit "$status"
