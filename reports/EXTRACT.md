# EXTRACT — the comparison-scheme step

Unlike `cose-parse-nopanic`, this crate is not a remodel of code from
another repository: `rust/src/lib.rs` is a small model written for this
proof, from scratch, against the open-source description of "Biser-4"
(see `README.md`'s "The model: source vs. ours" section for the sources
and which rules are ours). There is no external
source tree to quote line numbers from. What follows instead is what would
normally be an `// EXTRACT:` / `// REMODEL:` table: the two implementation
choices made specifically so Charon/Aeneas would accept and cleanly extract
the code, plus the one correctness bug the exhaustive test caught before
extraction.

## Entry points

- `step(active: ActiveSet, words: [Word; 4]) -> StepResult` — the one
  function the theorems in `reports/PROOF.md` are stated about.
- `quad_step`, `triple_step`, `pair_step`, `disable` — private helpers
  `step` dispatches to; Aeneas extracts them too (all four active, exactly
  three active, exactly two active, and "clear one channel" respectively),
  and `reports/PROOF.md`'s proofs unfold them along with `step`.

No loop, no recursion, no allocation, no `unsafe` anywhere in
`rust/src/lib.rs`'s non-test code, so there is no `-loops-to-rec` /
`loop.spec_decr_nat` concern here the way `cose-parse-nopanic`'s
`slice_validated_uints` had one.

## REMODEL: `match` on precomputed equalities, not `&&`-chained `if`/`else if`

First version of `step`, `triple_step`, and `quad_step` used ordinary
`if c1 { .. } else if c2 { .. } else if c3 { .. } ...` chains, with `c1`,
`c2`, ... themselves `&&`-combined boolean expressions (`a0 && a1 && a2 &&
a3`, `wa == wb && wb == wc`, and so on) — the direct transcription of the
source rules (see `README.md`'s model table). `cargo test` passed. `charon cargo --preset=aeneas`
also exited `0`, but the LLBC it wrote was **≈662 MB on disk** for a
39-function, 13-type crate (`cose-parse-nopanic`'s LLBC, a materially
bigger parser, is 1.6 MB). Almost the entire size was one function's
translated body: `step`'s.

**Measurement method and units, exact.** "Whole file" below is bytes on
disk, `ls -la` / `wc -c` (decimal MB = 10⁶ bytes throughout this section,
not MiB = 2²⁰ bytes). "One function's share" is the exact byte span of
that function's JSON value *as it appears in that same file* — found by
scanning `{`/`[` … `}`/`]` depth while skipping over string contents (so a
bracket inside a string doesn't miscount), not `len(json.dumps(...))` of a
value `json.load`-ed and then re-serialized. An earlier draft of this
section used the `json.dumps` re-serialization method and reported
`step`'s share as 745 MB against a 661 MB whole file — a part larger than
the whole, which cannot happen for a byte span taken from the same file,
and was wrong. Re-serializing a parsed copy measures the size of a new
string Python builds, not the number of bytes the original file actually
spent on that subtree, and on this file the two diverged enough to
produce a nonsensical result; the byte-span method above cannot produce
one, because a substring's length cannot exceed its string's.

**Numbers, re-derived.** The original oversized file was not kept (each
`charon cargo --preset=aeneas` run overwrote it, and the final, committed
`llbc/quad_voter_proof.llbc` is the small, fixed-code one), so the
`&&`-chain version of `rust/src/lib.rs` was reconstructed in a scratch
copy outside this repository and re-extracted at the same Charon/Aeneas
pins, rather than leaving the original claim unverifiable:

| | whole file | `step` | `quad_step` | `triple_step` | `disable` | `pair_step` |
|---|---|---|---|---|---|---|
| `&&`-chain (reproduced) | 662,259,380 B (≈662.3 MB) | 661,480,177 B (≈661.5 MB, 99.88% of the file) | 452,393 B | 58,190 B | 21,190 B | 8,694 B |
| `match` (committed) | 526,561 B (≈526.6 KB) | 149,321 B (28.4% of the file) | 65,797 B | 40,829 B | 21,142 B | 8,694 B |

The committed row is for `llbc/quad_voter_proof.llbc` as it stands right
now; Charon/Aeneas embed the Rust source's line and column numbers in
several places in the LLBC (doc comments, spans), so this row's exact
byte counts shift by a few dozen to a few hundred bytes whenever
`rust/src/lib.rs` is edited above the measured functions, even when the
edit is comment-only and changes no code — see `scripts/check-extraction.sh`
for the freshness check that keeps the *committed* file in sync with the
*current* source; this table is not re-measured on every such edit.

The three whole-file byte counts actually observed for `&&`-chain runs
during this project (661,968,010 and 661,847,852 bytes, from two runs
this session's own transcript recorded; 662,259,380 bytes, from the
scratch reproduction above) agree to within 0.06% — consistent with the
small, already-documented run-to-run nondeterminism in Charon's debug
naming tables (see "Freshness" below), not a sign the bug is only
sometimes present. `step`'s share was not re-measured for those first two
runs (the files no longer exist); the 661.5 MB / 99.88% figure is from
the scratch reproduction only.

**Remodel:** compute each pairwise comparison once into a named `bool`
local, then dispatch on a `match` over the tuple of those booleans (16-way
for `step` on `(a0, a1, a2, a3)`, 8-way collapsed to 5 arms + wildcard for
`triple_step` on `(eq_ab, eq_ac, eq_bc)`, 64-way collapsed to 6 arms +
wildcard for `quad_step` on the six pairwise word equalities), instead of a
chain of compound `&&` tests. Same truth table, same `StepResult` in every
case (`cargo test`'s `step_matches_oracle_exhaustively` — 1296 cases — is
unchanged by the rewrite and still passes). After the rewrite, the LLBC is
≈526 KB, not ≈662 MB — see the table above for the committed file's exact
current byte count.

This project does not know precisely why Charon's (or the underlying MIR
lowering's) handling of a long `&&`-chained `if`/`else if` ladder blew up
like this — only that it did, reproducibly, and that a `match` on the same
booleans did not. Anyone extending `rust/src/lib.rs` with more branches
should watch `llbc/quad_voter_proof.llbc`'s size after `charon cargo
--preset=aeneas` and prefer `match` over `&&`-chained `if`/`else if` if it
jumps.

## REMODEL: `Debug` is `#[cfg_attr(test, derive(Debug))]`, not unconditional

A first version derived `Debug` unconditionally on `StepResult` (needed for
`assert_eq!` in the doctest). This is the pattern
`cose-parse-nopanic/reports/EXTRACT.md` layer 1 warns about ("dropped
unused `CodecError` variants" / "`Clone`/`Copy`/`Debug` dropped ... so
Aeneas does not emit an unused `fmt` axiom") — but on this crate it was
**not** a meaningful contributor to the ≈662 MB bloat above, unlike the
`&&`-chain remodel, which was. This project checked, rather than assumed:
two `&&`-chain runs were compared, one with `Debug` derived
unconditionally (661,968,010 bytes) and one with `Debug` gated to
`#[cfg(test)]` only, both other code unchanged (661,847,852 bytes) — a
difference of 120,158 bytes, ≈0.018% of the file. The unconditional
`Debug` derive is still worth avoiding (extra `core::fmt` axiom surface,
same reasoning as `cose-parse-nopanic`), but it was not the cause of the
hundred-megabyte-scale bloat; the `&&`-chain remodel above was, on its
own, both necessary and sufficient to bring the file from ≈662 MB to
≈526 KB. `rust/src/lib.rs`'s own comment on the `Debug` derive states
this same 120,158-byte figure, not "hundreds of megabytes". `Debug` is
derived only under `#[cfg(test)]`; doctest examples use
`assert!(matches!(...))` instead of `assert_eq!` so they do not need it
outside `cfg(test)`.

## Bug the exhaustive test caught (not an extraction issue)

While writing the cross-check `oracle` function for
`step_matches_oracle_exhaustively` (a second, differently-structured
implementation of the same rules, used only by that test — see
`rust/src/lib.rs`), an early version of `oracle`'s three-active-channel case
picked the first channel with a value seen exactly once as "the odd one
out" without first checking that the *other two* channels agreed with each
other. On `active = [false, true, true, true]`,
`words = [_, 0, 1, 2]` (three active channels, all three different), it
misclassified the case as `Majority` instead of `OutsideHypothesis`. The
exhaustive test failed against `step` (which was already correct) and
caught it immediately; fixed by requiring a value with multiplicity 2 among
the three before treating the remaining one as the odd channel. Recorded
here because it is the one place this project's own test infrastructure had
a bug worth knowing about, not because it says anything about `step` or
about Charon/Aeneas.

## Freshness (`scripts/check-extraction.sh`)

Running `charon cargo --preset=aeneas` twice in a row on an unmodified
`rust/src/lib.rs` does **not** produce byte-identical LLBC files. Two
things vary between runs, confirmed by diffing the parsed JSON of two
back-to-back runs:

1. `translated.options.dest_file` — literally the `--dest-file` path the
   caller passed; expected to differ since `scripts/check-extraction.sh`
   writes the fresh copy to a scratch path, not over the committed one.
2. The list order of `translated.short_names`, `translated.item_names`, and
   `translated.assoc_item_names` — Charon's human-readable debug naming
   tables. These are association lists (key/value pairs), and their order
   is not stable across separate `charon cargo` invocations of the same
   crate.

Everything else — `fun_decls`, `type_decls`, `global_decls`, `trait_decls`,
`trait_impls`, `ordered_decls`, `files`, and the rest of `options` — was
byte-identical across the two runs, and Aeneas produced a byte-identical
`lean/QuadVoterProof.lean` from both LLBCs. `scripts/check-extraction.sh`
therefore compares the LLBC with those two fields normalized out
(`scripts/normalize-llbc-diff.py`: drop `dest_file`, sort the three naming
tables before comparing) and compares `lean/QuadVoterProof.lean` with a
plain byte diff, which needs no such normalization.
