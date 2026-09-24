# quad-voter-proof

Machine-checked proof of a step of a four-channel command-word comparison
scheme, consistent with the open-source description of "Biser-4" (NIIAP):
four machines running the same program, synchronously, with an output
comparison scheme that blocks a channel that has failed, rated for two
failures (degradation 4 → 3 → 2). Not a claim about how "Biser-4" itself
identifies a failed channel — buran.ru (`su4bcvk.htm`), the source for the
comparison scheme, says only "blocks"; see `reports/PROOF.md` and the
source/ours labels below and in `rust/src/lib.rs`.

Not the `cose-parse-nopanic` product tree — this crate follows its layout
and pins as a template only. Work and name: Dmitrii Zatona.
License: Apache-2.0.

**Proved (`reports/PROOF.md` has the exact statements):**

- **T1 (no-panic):** for every active set and every four command words,
  `step` returns `ok` — never a panic.
- **T2 (masking, one step, arbitrary `A`):** with `|A| ≥ 3` and at most one
  active channel disagreeing with a claimed value `v`, `step` outputs `v`
  and disables exactly that one disagreeing channel (or nothing, if all
  agree).
- **T3a (reachable traces, no order assumption):** on any trace from four
  active channels, with `|F| ≤ 2` and — every step — the active channels
  not in `F` agreeing on a value, a channel not in `F` is never disabled.
  **False for an arbitrary starting state** (counterexample: one
  correct channel outvoted by two agreeing faulty ones); stated here only
  for traces starting at four active channels.
- **T3b (reachable traces, with "faults reveal one at a time"):**
  additionally assuming at most one *faulty* active channel disagrees with
  the correct value per step, the command is always that correct value,
  and the "outside the failure hypothesis" result never occurs.
- **T4 (pair):** with exactly two channels active and disagreeing, the
  result is an explicit `Undetermined` — no command, active set unchanged.

All five are proved over the code Aeneas extracted from `rust/src/lib.rs`
(`lean/QuadVoterProof.lean`, unedited Aeneas output), not over a
hand-written model. Axioms of every theorem (T1, T2, T3a and its two
corollaries, T3b, T4): `propext`, `Classical.choice`, `Quot.sound` only
(checked by `lake env lean` `#print axioms`, and in CI). No `sorry`, no
`axiom`, in any of the project's Lean files (`lean/*.lean`, including
`lakefile.lean`) — checked by `scripts/check-no-sorry.sh`, comment-aware,
also in CI.

**Not proved (the full list, with the artifact-specific
reading, is in `reports/PROOF.md`):** specification errors; input
congruence / a Byzantine command source; synchronization, timing, the
clock generator; the comparison-scheme hardware and the compiler (no
DO-178C-qualified Rust toolchain exists); a common flight-software bug
(all four channels agreeing on a wrong command — the proved voter outputs
it, by T2/T3b's own conclusion); upsets with recovery (this model's
disabled channels never return — a deliberate divergence from the "Biser"
family, where "Biser-2" restored a grain by RAM copy after a transient
upset); survival past the third failure; behaviour outside the failure
hypothesis (`OutsideHypothesis` is the proved *result*, not a proved
*command* — T3a's boundary, below); what a real implementation should do
about an undetermined pair; correspondence with the actual "Buran"
implementation (theirs was hardware plus assembly PPN, this is a
from-scratch Rust model of the open-source *description*); trust in the
Lean kernel, Charon, and Aeneas as tools (none is DO-178C TQL-qualified).

**T3a boundary (required statement):** T3a proves a correct channel is
never disabled; it does **not** prove a command is issued when two
channels disagree simultaneously by value (a 2–2 split at four active
channels gives `OutsideHypothesis`, no command). "Survives two failures"
here is only the T3b statement, and only with T3b's own assumption.

## The model: source vs. ours

Two open sources, not one, describe "Biser-4", and they say different
things. buran.ru (`su4bcvk.htm`) says: four channels, synchronous, same
programs, an output
comparison scheme monitoring all four channels' commands, blocking a
failed channel's output, 4 → 3 → 2, rated for two failures in any path.
Parondzhanov's testimony corroborates "synchronous,
same programs" and adds that synchronization was hardware, not software.
Vikhorev–Glazkov (NPCAP, 2007 conference proceedings) — a different,
independent primary source, the manufacturer's own — say only that
Biser-4 used **fourfold redundancy** *for* the two-failure-in-any-path
requirement; they do not describe synchronous
operation, identical programs, the comparison scheme, or blocking at all
for Biser-4 — for those, buran.ru and Parondzhanov are the only sources.
Neither source says how the comparison scheme picks the failed channel,
what it does with a disagreeing pair, how inputs are distributed to the
channels, or whether sync/service words are wider than the command
payload. Every rule in this model beyond what these sources state is
marked below and in `rust/src/lib.rs`'s doc comments.

| Rule | Source / ours |
|---|---|
| Four channels, synchronous, same programs, output comparison, blocks a failed one, 4 → 3 → 2, two-failure requirement | Source: buran.ru (`su4bcvk.htm`) for all of this; Parondzhanov's testimony corroborates "synchronous, same programs" and hardware sync; Vikhorev–Glazkov (NPCAP 2007) separately confirm only that fourfold redundancy was *for* the two-failure requirement, not the comparison-scheme mechanism. |
| A blocked channel never returns | **Ours.** "Biser-2" (a predecessor in the same family) restored a grain after a transient upset by copying RAM across the inter-channel link (NB); this model represents permanent failures, not transient upsets with recovery, and says so directly. |
| Command word type `u64` | **Ours.** Source command words to peripherals ("kodogrammy") are described as 36 bits; no built-in Rust type is exactly 36 bits, and `u64` is the smallest one that represents every 36-bit value without truncation. The model compares words only for whole-word equality, never a numeric range, so the extra width changes nothing proved here. |
| Comparison is whole-word, not bitwise | **Ours.** "Biser-2"'s majority element was bitwise (NB); at four channels, bitwise majority voting produces bit-level 2–2 ties, so whole-word comparison was chosen as the simpler, more directly verifiable model — stated as a modelling choice, not a claim about "Biser-4". |
| Exactly one disagreeing channel among an agreeing majority → majority wins, disagreeing channel disabled | **Ours.** buran.ru says only "blocks"; a secondary, unverified source (Habr) says "differs from the other three"; the predecessor "Biser-2" had a bitwise majority element flagging a grain's anomaly (NB). Majority-of-the-whole-word is this project's reconstruction of "blocks", not a documented mechanism. |
| Two active channels, disagreeing → `Undetermined` | **Ours.** The source does not describe pair behaviour at all. |
| Any other disagreement pattern (2–2, 2–1–1, all different at three active) → `OutsideHypothesis`, no command chosen | **Ours.** Not a behaviour attributed to "Biser-4". |
| One active channel → `Agreed`, that channel's own word as the command, unchanged | **Ours.** A degenerate case of "all active channels agree" (agreement holds vacuously for one channel); no source describes running with a single channel at all. `step` accepts this input (T1), but no trace reachable from four active channels ever reaches it (T3a's invariant keeps `\|A\| ≥ 2`), and no theorem beyond T1 says anything about it. |
| Zero active channels → `NoActiveChannels`, no command | **Ours.** Kept as its own variant, distinct from `Agreed`, purely so `step` is total (T1) — not a claim about "Biser-4", which never runs with zero channels. Same reachability caveat as the one-channel row: never reached from four active, not covered by any theorem beyond T1. |

## Reproduce

Pin Charon `909ff09a` / Aeneas `c2015b86` / Lean 4.31.0 — install notes in
[`reports/TOOLCHAIN.md`](reports/TOOLCHAIN.md) (same pins and machine as
`cose-parse-nopanic`). `lean/lakefile.lean` loads Aeneas from
`$HOME/aeneas/backends/lean` (`AENEAS_LEAN` overrides). Then:

```sh
cd rust && cargo test
cd ..
export PATH="$HOME/charon/bin:$PATH"
scripts/check-extraction.sh   # re-extracts and diffs against the committed llbc/Lean
scripts/check-no-sorry.sh     # self-tests, then greps every lean/*.lean file
cd lean && lake build
lake env lean --stdin <<'EOF'
import VoterStatements
open VoterStatements
#print axioms VoterStatements.T1
#print axioms VoterStatements.T2
#print axioms VoterStatements.T3a
#print axioms VoterStatements.T3b
#print axioms VoterStatements.T4
EOF
```

## What CI does and does not run

[`.github/workflows/ci.yml`](.github/workflows/ci.yml) has two jobs.

The **Rust job** runs `sha256sum -c reports/PROOF.sha256` (binding the
committed LLBC and generated Lean to the Rust source, `Cargo.toml`,
`Cargo.lock`, `lakefile.lean`, and the handwritten proof/statements files),
then `cargo test`.

The **Lean job** checks out Aeneas at `c2015b86`, installs Lean 4.31.0,
builds Aeneas's own Lean library, runs `lake build` on this project
(`QuadVoterProof`, `VoterProof`, `VoterStatements`), checks the axiom sets
of `T1`, `T2`, `T3a` (and its corollaries `T3a_correct_never_disabled`,
`T3a_nonempty`), `T3b`, and `T4` against `{propext, Classical.choice,
Quot.sound}` (the primary sorry/axiom gate — `sorryAx`, what `sorry`
compiles to, would show up here), and runs `scripts/check-no-sorry.sh` —
a secondary, textual gate
over every `lean/*.lean` file that strips Lean comments before
matching `sorry`/`admit`/`axiom`, so a `sorry -- TODO` or a `private
axiom` cannot hide from it the way a plain `grep -v ':.*--'` could; its
own `--self-test` (run first) proves that against eleven fixture cases.

**Neither job runs Charon, and neither re-extracts LLBC or generated
Lean.** Installing and running Charon in a few CI minutes is not
practical (see `reports/TOOLCHAIN.md`); freshness of the committed
`llbc/quad_voter_proof.llbc` and `lean/QuadVoterProof.lean` against the
Rust source is checked locally, by a human or an agent running
[`scripts/check-extraction.sh`](scripts/check-extraction.sh) before every
commit that touches `rust/src/lib.rs` — exactly the same honest gap
`cose-parse-nopanic` states in its own README.

## Layout

- `rust/` — the crate: `#![no_std]`, no `unsafe`, no allocation, no loop,
  no recursion. `step` and its helpers (`quad_step`, `triple_step`,
  `pair_step`, `disable`) are the code Aeneas extracts.
- `llbc/quad_voter_proof.llbc` — Charon's LLBC, committed.
- `lean/QuadVoterProof.lean` — Aeneas's generated Lean, committed,
  unedited.
- `lean/VoterProof.lean` — handwritten: equational characterizations of
  the extracted code (`step_unfold`, `quad_step_eq`, `triple*_eq`,
  `pair_step_unfold`, index/update bridging lemmas).
- `lean/VoterStatements.lean` — handwritten: the theorem statements file
  (T1, T2, T3a, T3b, T4, proved), plus the trace machinery (`activeSeq`)
  and the invariant-preservation lemmas T3a/T3b build on.
- `scripts/check-extraction.sh` / `scripts/normalize-llbc-diff.py` — the
  extraction-freshness gate (see `reports/EXTRACT.md` for why LLBC needs a
  normalized, not byte-for-byte, comparison).
- `scripts/check-no-sorry.sh` / `scripts/check-no-sorry.py` — the
  secondary, textual `sorry`/`admit`/`axiom` gate, comment-aware (so
  `sorry -- TODO` cannot hide) and not anchored at column 0 (so `private
  axiom` / `@[simp] axiom` cannot hide either); self-tests itself against
  eleven fixture cases before checking the real files.
- `reports/PROOF.md`, `reports/TOOLCHAIN.md`, `reports/EXTRACT.md`,
  `reports/PROOF.sha256` — the proof artifacts.

[`cose-parse-nopanic`](https://github.com/dzatona/cose-parse-nopanic) is
the same Charon/Aeneas/Lean pipeline, on a different piece of code (a
no-panic proof of a CBOR/COSE envelope parse); this repository follows its
layout and reporting conventions.
