# PROOF — T1, T2, T3a, T3b, T4 over the extracted comparison-scheme step

Current proof. Theorems are proved in `lean/VoterStatements.lean`, built on
the equational characterizations of the extracted `step` (and its helpers
`quad_step`, `triple_step`, `pair_step`, `disable`) proved in
`lean/VoterProof.lean`. `lean/QuadVoterProof.lean` is Aeneas's unedited
output from `llbc/quad_voter_proof.llbc` (see `EXTRACT.md`).

Notation:

- `A active` — the set of active channels ("A"), a `Finset (Fin 4)`.
- `out words i` — channel `i`'s command word this step ("out[i]").
- `F : Finset (Fin 4)`, `F.card ≤ 2` — the faulty channels, fixed along a
  trace.
- `h` — the per-step value all active correct (∉ `F`) channels agree on.
  The premise says nothing about `h` being the right command: under a
  shared flight-code bug the correct channels agree on a wrong `h`, and
  the theorems deliver that wrong `h` just the same. T3a and T3b both
  carry this agreement premise as an explicit hypothesis, once per step
  (`hAgree`).

## T1 — no-panic

> For any active set and any command words, `step` returns `ok`.

```
theorem T1 (active : Array Bool 4#usize) (words : Array U64 4#usize) :
    ∃ r, step active words = ok r
```

`ok` includes every `StepResult` variant, including `Undetermined` and
`OutsideHypothesis` — this is "no panic", not "no undetermined result".

## T2 — masking, one step, arbitrary `A`

> Let `|A| ≥ 3`, `v` a value, `D = {i ∈ A | out[i] ≠ v}`, `|D| ≤ 1`. If
> `D = ∅`, the output is `v` and `A` is unchanged. If `D = {d}`, the output
> is `v`, the new `A` is `A \ {d}`, and no other channel is disabled.

```
theorem T2 (active : Array Bool 4#usize) (words : Array U64 4#usize) (v : U64)
    (hA3 : 3 ≤ (A active).card)
    (hD1 : ((A active).filter (fun i => out words i ≠ v)).card ≤ 1) :
    (((A active).filter (fun i => out words i ≠ v)) = ∅ →
      step active words = ok (StepResult.Agreed v active)) ∧
    (∀ d, ((A active).filter (fun i => out words i ≠ v)) = {d} →
      ∃ r, step active words = ok r ∧ resultCommand r = some v ∧
        resultDisabledIs r d ∧ A (resultActive r) = A active \ {d} ∧
        ∀ j : Fin 4, j ≠ d → chanGet (resultActive r) j = chanGet active j)
```

`resultCommand`, `resultDisabledIs`, `resultActive` read the three public
fields back out of a `StepResult` uniformly across its five variants (see
`VoterStatements.lean`); `resultDisabledIs r d` compares `.val : Nat`
between the extracted `U8` and `d : Fin 4` — it never constructs a `U8`
from an arbitrary `Fin 4`, so `disable`'s `else`-branch fallback for a
`U8` outside `0..=3` (see `rust/src/lib.rs`) is never part of this claim.
Proved by a full case split on the sixteen active patterns (discarding the
eleven with `|A| < 3` via `A_card_eq`), then, within each of the five
surviving patterns, a full case split on the word-equality pattern that
`quad_step`/`triple_step`'s extracted `if`-tree already encodes.

`hD1` is carried as a hypothesis in the theorem's statement but is not
needed by this proof's own case split (both conclusions are already
conditioned on `D`'s exact shape); the linter flags it unused, which is
expected and does not weaken the theorem.

## T3a — reachable traces, no assumption about failure order

> On any finite trace from `A = {0,1,2,3}`, the invariant "A \ F is
> nonempty and every disabled channel ∈ F" is preserved by the step, then
> by induction on the trace. Hence a correct channel is never disabled.
> **For an arbitrary initial state the theorem is false**
> (counterexample: `A` = one correct channel plus two faulty channels, the
> faulty channels agree on `w`, the correct channel is disabled) — T3a is
> stated only for traces from four active channels.

`T3a` itself proves the "every disabled channel ∈ F" half of the
invariant, as `univ \ A ⊆ F`: every channel outside the current active
set `A` (i.e., every channel disabled so far, since the trace starts at
`A = univ` and disabled channels never return) is in `F`. The "`A \ F`
nonempty" half is `T3a_nonempty`, a proved corollary, not folded into
`T3a`'s own statement: it follows from `T3a_correct_never_disabled`
(every channel not in `F` is active) plus `F.card ≤ 2 < 4` (so some
channel outside `F` exists at all, hence is active and in `A \ F`).

```
def allActive : Array Bool 4#usize  -- {0, 1, 2, 3}

def activeSeq (wordsSeq : Nat → Array U64 4#usize) : Nat → Array Bool 4#usize
  | 0 => allActive
  | n + 1 => stepActive (activeSeq wordsSeq n) (wordsSeq n)  -- fold over `step`

theorem T3a (wordsSeq : Nat → Array U64 4#usize) (F : Finset (Fin 4)) (hF : F.card ≤ 2)
    (hAgree : ∀ n : Nat, ∃ h : U64,
      ∀ i : Fin 4, i ∈ A (activeSeq wordsSeq n) → i ∉ F → out (wordsSeq n) i = h) :
    ∀ n : Nat, Finset.univ \ A (activeSeq wordsSeq n) ⊆ F

theorem T3a_correct_never_disabled (wordsSeq : Nat → Array U64 4#usize)
    (F : Finset (Fin 4)) (hF : F.card ≤ 2)
    (hAgree : ∀ n : Nat, ∃ h : U64,
      ∀ i : Fin 4, i ∈ A (activeSeq wordsSeq n) → i ∉ F → out (wordsSeq n) i = h) :
    ∀ (n : Nat) (i : Fin 4), i ∉ F → i ∈ A (activeSeq wordsSeq n)

theorem T3a_nonempty (wordsSeq : Nat → Array U64 4#usize)
    (F : Finset (Fin 4)) (hF : F.card ≤ 2)
    (hAgree : ∀ n : Nat, ∃ h : U64,
      ∀ i : Fin 4, i ∈ A (activeSeq wordsSeq n) → i ∉ F → out (wordsSeq n) i = h) :
    ∀ n : Nat, (A (activeSeq wordsSeq n) \ F).Nonempty
```

`activeSeq` is the fold over the extracted `step`, indexed by the trace
step `n`, used here in place of a Rust loop; `stepActive` is `step`'s result unwrapped
using T1 (the `match ... | _ => active` fallback arm is dead code, proved
unreachable by `T1`, not part of any theorem's claim).

**Why `hAgree` is required, not derivable.** T3a's invariant is false
without a per-step agreement premise, even starting from four active
channels: if the words at some step make three channels agree on a value
and the fourth (a channel not in the adversarially-chosen `F`) disagree by
coincidence, `step` disables that fourth channel — nothing in `step`
consults `F`. The invariant only survives because, when it already held
before the step, there are `4 - |F| ≥ 2` correct active channels, so a
disabled channel `d ∉ F` would force a *second* correct channel's word to
equal the disabled channel's own disagreeing value, contradicting the
per-step agreement premise (`VoterStatements.quad_disable_in_F`,
`triple_disable_in_F`). This is the same fact already implicit in the
definition of `h` above (the per-step agreement premise); T3a's Lean
statement just makes the per-step existential explicit instead of leaving
it implicit in the shared notation.

**T3a boundary:** T3a proves that a
correct channel is never disabled; it does **not** prove that a command is
issued when two channels disagree simultaneously by value (a 2–2 split at
four active channels gives `OutsideHypothesis`, no command). "Survives two
failures" in this project is only the T3b statement, with its own
assumption.

**Scope restricted to reachable states.** `|A (activeSeq wordsSeq n)|` is
always 2, 3, or 4 along a trace from four active channels (T3a's own
invariant, combined with `F.card ≤ 2`); `|A| = 1` and `|A| = 0` are inputs
`step` accepts (see T1) but never arise on such a trace, and neither T3a
nor T3b states anything about them.

## T3b — reachable traces, with the "faults reveal one at a time" assumption

> Additionally, on every step, `|{i ∈ A ∩ F | out[i] ≠ h}| ≤ 1`. Then: (b)
> while `|A| ≥ 3`, the output is `h`; (c) `OutsideHypothesis` never occurs;
> (d) when `|A| = 2`, both active channels are correct (T3a) and the output
> is `h`.

```
theorem T3b (wordsSeq : Nat → Array U64 4#usize) (F : Finset (Fin 4)) (hF : F.card ≤ 2)
    (hAgree : ∀ n : Nat, ∃ h : U64,
      (∀ i : Fin 4, i ∈ A (activeSeq wordsSeq n) → i ∉ F → out (wordsSeq n) i = h) ∧
      ((A (activeSeq wordsSeq n) ∩ F).filter (fun i => out (wordsSeq n) i ≠ h)).card ≤ 1) :
    ∀ (n : Nat) (h : U64),
      (∀ i : Fin 4, i ∈ A (activeSeq wordsSeq n) → i ∉ F → out (wordsSeq n) i = h) →
      ((A (activeSeq wordsSeq n) ∩ F).filter (fun i => out (wordsSeq n) i ≠ h)).card ≤ 1 →
      ∃ r : StepResult,
        step (activeSeq wordsSeq n) (wordsSeq n) = ok r ∧
        resultCommand r = some h ∧
        r ≠ StepResult.OutsideHypothesis (activeSeq wordsSeq n)
```

The conclusion is `∀ h`, with the two per-step premises (correct channels
agree on `h`; at most one active faulty channel disagrees with `h`)
repeated as hypotheses of the conclusion itself, not a fresh `∃ h` —an
existential conclusion would only witness "step outputs *some* value",
satisfiable by reading `h` back as whatever `step` happened to output, and
would not tie the output to the healthy value (b)/(d) above require.
Both premises pin down at most one `h` per step in practice (any two
active correct channels agree with each other, since each agrees with
`h`), so `∀ h, premises → ...` is not a weaker statement than an
existential one for this fact — it is what makes "the output equals `h`"
a real claim instead of a tautology. The outer `hAgree` hypothesis is
still required beyond the per-step premises repeated in the conclusion:
`T3a`, invoked internally for the invariant "every channel not in `F` is
active", needs the correct-agreement premise at *every* step of the
trace, not just the one step the conclusion is instantiated at.

The "faults reveal one at a time" assumption is in the *same* existential
as `h`, by design: T3b's statement above binds it in the same clause as
`h` itself, not as a separate later hypothesis. (b) and (d) are proved together as one
`resultCommand r = some h` fact (`|A|` is always 2, 3, or 4 by T3a, and
both cases give command `h`: `|A| ≥ 3` via `T2` instantiated at `v = h`
after showing `D` (T2's disagreement set) coincides with the faulty
disagreement set the hypothesis bounds; `|A| = 2` via `step_pair_agree`,
since both active channels are correct by T3a and therefore both equal
`h`). (c) needs no case split: `resultCommand (OutsideHypothesis _) = none
≠ some h`, so the same `resultCommand r = some h` fact already rules it
out (`resultCommand_outside_ne`).

Breaks without the assumption: a 2–2 or 2–1–1 split among four active
channels (both possible with two active faulty channels disagreeing with
`h` and, in the 2–2 case, with each other) gives `OutsideHypothesis`, no
command — exactly the pattern the assumption is designed to exclude by
bounding disagreeing faulty channels to at most one.

## T4 — pair

> At `|A| = 2` with a disagreement, the result is `Undetermined`: no
> command is produced, `A` is unchanged.

```
theorem T4 (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (i j : Fin 4) (hij : i ≠ j) (hA : A active = {i, j})
    (hdisagree : out words i ≠ out words j) :
    step active words = ok (StepResult.Undetermined active)
```

## Not proved

Out of scope for this artifact:

- **Specification errors** (Ariane 501-class): the theorems are properties
  of `step` relative to its own Rust definition, not a claim that the
  definition is the right one.
- **Input congruence and a Byzantine command source** (STS-124-class):
  `words` is an arbitrary function of the step index in T3a/T3b, with no
  constraint tying it to what any physical channel could actually receive.
- **Synchronization, timing, the shared clock generator**: not modelled at
  all; `step` is a pure function of one cycle's inputs.
- **The comparison-scheme hardware and the compiler**: no qualified
  DO-178C Rust toolchain exists (Ferrocene is ISO 26262 / IEC 61508 / IEC
  62304, not DO-178C — RS). This crate's proof says nothing about the
  compiled artifact, only the extracted MIR/LLBC Aeneas translated.
- **A common flight-software bug**: if all four channels agree on a wrong
  command, the proved voter outputs it — T2/T3b's own conclusion, not a
  gap in the proof.
- **Upsets with recovery**: the "Biser" family had inter-channel RAM
  copying after a transient upset (NB); this model's `disable`d channels
  never return (`OURS`, `rust/src/lib.rs`), so recovery is outside every
  theorem here.
- **Survival past the third failure**: Parondzhanov's PPN reportedly kept
  Buran flying through a third BCVM failure; this model stops resolving
  anything once `|A| = 2` (T4/T3b(d)) and has no third-failure behaviour to
  prove.
- **Behaviour outside the failure hypothesis** (simultaneous disagreement,
  2–2 splits): `OutsideHypothesis` is the proved *result*, not a proved
  *command* — see the T3a boundary sentence above.
- **Pair behaviour beyond "Undetermined"**: T4 proves the result is
  `Undetermined`; what a real implementation should do about it is exactly
  what the source does not say (`rust/src/lib.rs`, `README.md`).
- **Correspondence with the actual Buran implementation**: theirs was a
  hardware comparison scheme plus PPN assembly; this is a from-scratch
  Rust model of the open-source *description*, not a port of any Buran
  source.
- **Trust in the Lean kernel, Charon, and Aeneas**: none of the three is a
  DO-178C TQL-qualified tool (RS §3); this proof is only as trustworthy as
  they are.

## Live run

Crate `quad_voter_proof` **0.1.0**. Pins: Charon `909ff09a` v0.1.220,
Aeneas `c2015b86`, Lean 4.31.0.

### `cargo test`

```
$ cargo test
running 12 tests
test result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out

running 1 test
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
```

### `scripts/check-extraction.sh`

```
== diff: llbc/quad_voter_proof.llbc (semantic: ignores dest_file path and debug name-table order)
fresh (matches committed)
== diff: lean/QuadVoterProof.lean
fresh (matches committed)
```

### `lake build`

Full project (`QuadVoterProof`, `VoterProof`, `VoterStatements`) builds
with exit 0. The only warnings are three pre-existing `sorry`s inside
Aeneas's own stdlib (`Aeneas/Std/Slice.lean`, `Aeneas/Std/StringIter.lean`,
in unused `get_unchecked` / `StringIter` models — same situation as
`cose-parse-nopanic`), plus harmless local style warnings (one unused
hypothesis name, three `<;>`-vs-`;` linter suggestions) — none in a
theorem statement or proof step that matters to the result.

### Axiom audit

```
$ lake env lean --stdin <<'EOF'
import VoterStatements
open VoterStatements
#print axioms VoterStatements.T1
#print axioms VoterStatements.T2
#print axioms VoterStatements.T3a
#print axioms VoterStatements.T3a_correct_never_disabled
#print axioms VoterStatements.T3a_nonempty
#print axioms VoterStatements.T3b
#print axioms VoterStatements.T4
EOF
'VoterStatements.T1' depends on axioms: [propext, Classical.choice, Quot.sound]
'VoterStatements.T2' depends on axioms: [propext, Classical.choice, Quot.sound]
'VoterStatements.T3a' depends on axioms: [propext, Classical.choice, Quot.sound]
'VoterStatements.T3a_correct_never_disabled' depends on axioms: [propext, Classical.choice, Quot.sound]
'VoterStatements.T3a_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'VoterStatements.T3b' depends on axioms: [propext, Classical.choice, Quot.sound]
'VoterStatements.T4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` — the axiom audit above is the primary gate for that: it
already fails if `T1`, `T2`, `T3a`, `T3a`'s two corollaries
(`T3a_correct_never_disabled`, `T3a_nonempty`), `T3b`, or `T4` depend on
`sorryAx` (what `sorry` compiles to) or on any axiom outside `{propext,
Classical.choice, Quot.sound}`, wherever in their dependency graph it
occurs. The secondary, textual gate is `scripts/check-no-sorry.sh`
(`scripts/check-no-sorry.py` underneath): it strips Lean line (`--`) and
nested block (`/- ... -/`) comments before searching, so `sorry -- TODO`
cannot hide a hit, and matches `axiom` anywhere on a line rather than
anchoring at column 0, so `private axiom` / `@[simp] axiom` cannot hide
one either (a plain `grep -v ':.*--'` can be fooled by both). Its own
`--self-test` runs eleven fixture cases — five that must be flagged, six
that must not — proving this before trusting it against the real files;
run it locally before any commit touching a `.lean` file, and CI runs it
on every push/PR.

**Scope of the textual gate: every `.lean` file in `lean/`, nothing
else.** Checked clean: `lean/lakefile.lean`, `lean/QuadVoterProof.lean`
(Aeneas output, not hand-edited), `lean/VoterProof.lean`,
`lean/VoterStatements.lean` — not `rust/src/lib.rs` (Rust has no
`axiom`/`sorry` syntax; an unknown item there is a `cargo build` error,
not something this gate needs to catch) and not Aeneas's own stdlib
(pre-existing `sorry`s in unused models, outside this project — see
above; not in any of these seven theorems' axiom sets either, confirmed
by the audit above, not by this grep).

### Reproduce

```sh
sha256sum -c reports/PROOF.sha256
cd rust && cargo test
cd .. && scripts/check-extraction.sh
scripts/check-no-sorry.sh
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

`reports/PROOF.sha256` hashes the files the spec requires (Rust source,
`Cargo.toml`, `Cargo.lock`, `lakefile.lean`, LLBC, generated Lean, the
handwritten proof and statements files) plus the four verification
scripts (`scripts/check-extraction.sh`, `scripts/normalize-llbc-diff.py`,
`scripts/check-no-sorry.py`, `scripts/check-no-sorry.sh`): those scripts
are as much a part of the trust story as the theorems they check, and an
unnoticed edit to one of them (say, a `check-no-sorry.py` that always
reports "clean") would silently defeat its gate.

See `TOOLCHAIN.md` for pins, `EXTRACT.md` for what changed to make
extraction work and the freshness-check methodology.
