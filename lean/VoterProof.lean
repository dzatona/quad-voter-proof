-- Handwritten proof engine over the code Aeneas extracted into
-- `QuadVoterProof.lean` (`import QuadVoterProof`; that file is not edited by
-- hand). This file proves *equational characterizations* of `step` and its
-- helpers (`step_unfold`, `quad_step_eq`, `triple{012,013,023,123}_eq`,
-- `pair_step_unfold`, `disable_{0,1,2,3}_eq`) that `VoterStatements.lean`
-- builds T1/T2/T3a/T3b/T4 from.
--
-- Panic model (same as the Aeneas/Binder convention): every extracted
-- function lives in the `Result` monad `ok v | fail e | div`. A panic
-- (overflow, out-of-bounds index, unwrap, division by zero, ...) is exactly
-- `fail`/`div`. No-panic is `∀ inputs, ∃ v, f inputs = ok v`.
--
-- `step`/`quad_step`/`triple_step`/`pair_step`/`disable` have no loop: they
-- are nested `if`/`then`/`else` over `Array.index_usize` (always `ok` for a
-- literal in-bounds index on a length-4 array) and `==` comparisons. Every
-- lemma below is proved by unfolding the extracted definition, rewriting
-- every `Array.index_usize`/`Array.update` call to a plain value via the
-- bridge lemmas in the first section, and (for `step`, `quad_step`,
-- `triple_step`) splitting the resulting `if`s.

import QuadVoterProof

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open quad_voter_proof

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace VoterProof

/-! # Bridging `Array.index_usize` / `Array.update` (monadic) to plain values

Every call in the extracted code indexes or updates a length-4 array at a
literal `Usize` in `{0, 1, 2, 3}`, so both always succeed. `chanGet` is the
total, proof-free-at-use-site accessor this project's channel index type
(`Fin 4`, matching the notation `i` used in `VoterStatements.lean`) reads
through; `VoterStatements.lean`'s `A`/`out` are stated in terms of it. -/

/-- Reads channel `i`'s slot of a length-4 `Array` (`active[i]` / `out[i]`
    in `VoterStatements.lean`'s notation). Total: `i : Fin 4` is always in range. -/
def chanGet {α : Type} (v : Array α 4#usize) (i : Fin 4) : α :=
  v.val[i.val]'(by
    have h := v.property
    have h4 : (4#usize : Usize).val = 4 := by decide
    omega)

theorem index_eq {α : Type} (v : Array α 4#usize) (i : Usize) (h : i.val < 4) :
    Array.index_usize v i = ok (v.val[i.val]'(by
      have h4 : (4#usize : Usize).val = 4 := by decide
      simp only [Array.length_eq]; omega)) := by
  have hb : i.val < v.length := by
    have h4 : (4#usize : Usize).val = 4 := by decide
    simp only [Array.length_eq, h4]; omega
  have hs := Array.index_usize_spec v i hb
  cases hu : Array.index_usize v i with
  | ok r => simp [hu, spec, theta] at hs; rw [hs]
  | fail _ => simp [hu, spec, theta] at hs
  | div => simp [hu, spec, theta] at hs

theorem index0_eq {α : Type} (v : Array α 4#usize) :
    Array.index_usize v 0#usize = ok (chanGet v 0) := by
  rw [index_eq v 0#usize (by decide)]; rfl
theorem index1_eq {α : Type} (v : Array α 4#usize) :
    Array.index_usize v 1#usize = ok (chanGet v 1) := by
  rw [index_eq v 1#usize (by decide)]; rfl
theorem index2_eq {α : Type} (v : Array α 4#usize) :
    Array.index_usize v 2#usize = ok (chanGet v 2) := by
  rw [index_eq v 2#usize (by decide)]; rfl
theorem index3_eq {α : Type} (v : Array α 4#usize) :
    Array.index_usize v 3#usize = ok (chanGet v 3) := by
  rw [index_eq v 3#usize (by decide)]; rfl

theorem update_eq (active : Array Bool 4#usize) (i : Usize) (x : Bool) (h : i.val < 4) :
    active.update i x = ok (active.set i x) := by
  have hb : i.val < active.length := by
    have h4 : (4#usize : Usize).val = 4 := by decide
    simp only [Array.length_eq, h4]; omega
  have hs := Array.update_spec active i x hb
  cases hu : active.update i x with
  | ok v => simp [hu, spec, theta] at hs; rw [hs]
  | fail _ => simp [hu, spec, theta] at hs
  | div => simp [hu, spec, theta] at hs

theorem disable_0_eq (active : Array Bool 4#usize) :
    disable active 0#u8 = ok (active.set 0#usize false) := by
  unfold disable; simp; exact update_eq active 0#usize false (by decide)
theorem disable_1_eq (active : Array Bool 4#usize) :
    disable active 1#u8 = ok (active.set 1#usize false) := by
  unfold disable; simp; exact update_eq active 1#usize false (by decide)
theorem disable_2_eq (active : Array Bool 4#usize) :
    disable active 2#u8 = ok (active.set 2#usize false) := by
  unfold disable; simp; exact update_eq active 2#usize false (by decide)
theorem disable_3_eq (active : Array Bool 4#usize) :
    disable active 3#u8 = ok (active.set 3#usize false) := by
  unfold disable; simp; exact update_eq active 3#usize false (by decide)

/-! # `pair_step` / `triple_step` / `quad_step`: fully resolved -/

theorem pair_step_unfold (wa wb : U64) (active : Array Bool 4#usize) :
    pair_step wa wb active =
      if wa = wb then ok (StepResult.Agreed wa active) else ok (StepResult.Undetermined active) := by
  unfold pair_step
  rfl

theorem triple_step_unfold (ia : U8) (wa : U64) (ib : U8) (wb : U64) (ic : U8) (wc : U64)
    (active : Array Bool 4#usize) :
    triple_step ia wa ib wb ic wc active =
      (if wa = wb then
        if wa = wc then
          if wb = wc then ok (StepResult.Agreed wa active)
          else ok (StepResult.OutsideHypothesis active)
        else
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else disable active ic >>= fun a => ok (StepResult.Majority wa ic a)
      else
        if wa = wc then
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else disable active ib >>= fun a => ok (StepResult.Majority wa ib a)
        else
          if wb = wc then disable active ia >>= fun a => ok (StepResult.Majority wb ia a)
          else ok (StepResult.OutsideHypothesis active)) := by
  unfold triple_step
  rfl

/-- `triple_step` with the `{0, 1, 2}` call-site indices (`step`'s `a0 ∧ a1
    ∧ a2 ∧ ¬a3` branch), disable calls resolved to `Array.set`. -/
theorem triple012_eq (wa wb wc : U64) (active : Array Bool 4#usize) :
    triple_step 0#u8 wa 1#u8 wb 2#u8 wc active =
      (if wa = wb then
        if wa = wc then
          if wb = wc then ok (StepResult.Agreed wa active)
          else ok (StepResult.OutsideHypothesis active)
        else
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else ok (StepResult.Majority wa 2#u8 (active.set 2#usize false))
      else
        if wa = wc then
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else ok (StepResult.Majority wa 1#u8 (active.set 1#usize false))
        else
          if wb = wc then ok (StepResult.Majority wb 0#u8 (active.set 0#usize false))
          else ok (StepResult.OutsideHypothesis active)) := by
  rw [triple_step_unfold]
  simp only [disable_0_eq, disable_1_eq, disable_2_eq, disable_3_eq, bind_tc_ok]

/-- `triple_step` with the `{0, 1, 3}` call-site indices. -/
theorem triple013_eq (wa wb wc : U64) (active : Array Bool 4#usize) :
    triple_step 0#u8 wa 1#u8 wb 3#u8 wc active =
      (if wa = wb then
        if wa = wc then
          if wb = wc then ok (StepResult.Agreed wa active)
          else ok (StepResult.OutsideHypothesis active)
        else
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else ok (StepResult.Majority wa 3#u8 (active.set 3#usize false))
      else
        if wa = wc then
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else ok (StepResult.Majority wa 1#u8 (active.set 1#usize false))
        else
          if wb = wc then ok (StepResult.Majority wb 0#u8 (active.set 0#usize false))
          else ok (StepResult.OutsideHypothesis active)) := by
  rw [triple_step_unfold]
  simp only [disable_0_eq, disable_1_eq, disable_2_eq, disable_3_eq, bind_tc_ok]

/-- `triple_step` with the `{0, 2, 3}` call-site indices. -/
theorem triple023_eq (wa wb wc : U64) (active : Array Bool 4#usize) :
    triple_step 0#u8 wa 2#u8 wb 3#u8 wc active =
      (if wa = wb then
        if wa = wc then
          if wb = wc then ok (StepResult.Agreed wa active)
          else ok (StepResult.OutsideHypothesis active)
        else
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else ok (StepResult.Majority wa 3#u8 (active.set 3#usize false))
      else
        if wa = wc then
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else ok (StepResult.Majority wa 2#u8 (active.set 2#usize false))
        else
          if wb = wc then ok (StepResult.Majority wb 0#u8 (active.set 0#usize false))
          else ok (StepResult.OutsideHypothesis active)) := by
  rw [triple_step_unfold]
  simp only [disable_0_eq, disable_1_eq, disable_2_eq, disable_3_eq, bind_tc_ok]

/-- `triple_step` with the `{1, 2, 3}` call-site indices. -/
theorem triple123_eq (wa wb wc : U64) (active : Array Bool 4#usize) :
    triple_step 1#u8 wa 2#u8 wb 3#u8 wc active =
      (if wa = wb then
        if wa = wc then
          if wb = wc then ok (StepResult.Agreed wa active)
          else ok (StepResult.OutsideHypothesis active)
        else
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else ok (StepResult.Majority wa 3#u8 (active.set 3#usize false))
      else
        if wa = wc then
          if wb = wc then ok (StepResult.OutsideHypothesis active)
          else ok (StepResult.Majority wa 2#u8 (active.set 2#usize false))
        else
          if wb = wc then ok (StepResult.Majority wb 1#u8 (active.set 1#usize false))
          else ok (StepResult.OutsideHypothesis active)) := by
  rw [triple_step_unfold]
  simp only [disable_0_eq, disable_1_eq, disable_2_eq, disable_3_eq, bind_tc_ok]

theorem quad_step_unfold (words : Array U64 4#usize) (active : Array Bool 4#usize) :
    quad_step words active =
      (let w0 := chanGet words 0
       let w1 := chanGet words 1
       let w2 := chanGet words 2
       let w3 := chanGet words 3
       if w0 = w1 then
        if w0 = w2 then
          if w0 = w3 then ok (StepResult.Agreed w0 active)
          else disable active 3#u8 >>= fun a => ok (StepResult.Majority w0 3#u8 a)
        else
          if w0 = w3 then disable active 2#u8 >>= fun a => ok (StepResult.Majority w0 2#u8 a)
          else ok (StepResult.OutsideHypothesis active)
       else
        if w0 = w2 then
          if w0 = w3 then disable active 1#u8 >>= fun a => ok (StepResult.Majority w0 1#u8 a)
          else ok (StepResult.OutsideHypothesis active)
        else
          if w0 = w3 then ok (StepResult.OutsideHypothesis active)
          else
            if w1 = w2 then
              if w1 = w3 then
                if w2 = w3 then disable active 0#u8 >>= fun a => ok (StepResult.Majority w1 0#u8 a)
                else ok (StepResult.OutsideHypothesis active)
              else ok (StepResult.OutsideHypothesis active)
            else ok (StepResult.OutsideHypothesis active)) := by
  unfold quad_step
  simp only [index0_eq, index1_eq, index2_eq, index3_eq, bind_tc_ok]

/-- `quad_step`, fully resolved: no more `Array.index_usize` / `disable`
    calls, everything reduced to comparisons of `chanGet words k` and
    terminal `ok (StepResult...)` values. -/
theorem quad_step_eq (words : Array U64 4#usize) (active : Array Bool 4#usize) :
    quad_step words active =
      (let w0 := chanGet words 0
       let w1 := chanGet words 1
       let w2 := chanGet words 2
       let w3 := chanGet words 3
       if w0 = w1 then
        if w0 = w2 then
          if w0 = w3 then ok (StepResult.Agreed w0 active)
          else ok (StepResult.Majority w0 3#u8 (active.set 3#usize false))
        else
          if w0 = w3 then ok (StepResult.Majority w0 2#u8 (active.set 2#usize false))
          else ok (StepResult.OutsideHypothesis active)
       else
        if w0 = w2 then
          if w0 = w3 then ok (StepResult.Majority w0 1#u8 (active.set 1#usize false))
          else ok (StepResult.OutsideHypothesis active)
        else
          if w0 = w3 then ok (StepResult.OutsideHypothesis active)
          else
            if w1 = w2 then
              if w1 = w3 then
                if w2 = w3 then ok (StepResult.Majority w1 0#u8 (active.set 0#usize false))
                else ok (StepResult.OutsideHypothesis active)
              else ok (StepResult.OutsideHypothesis active)
            else ok (StepResult.OutsideHypothesis active)) := by
  rw [quad_step_unfold]
  simp only [disable_0_eq, disable_1_eq, disable_2_eq, disable_3_eq, bind_tc_ok]

/-! # `step`: dispatch, fully resolved -/

theorem step_unfold (active : Array Bool 4#usize) (words : Array U64 4#usize) :
    step active words =
      (if chanGet active 0 then
        if chanGet active 1 then
          if chanGet active 2 then
            if chanGet active 3 then quad_step words active
            else triple_step 0#u8 (chanGet words 0) 1#u8 (chanGet words 1) 2#u8 (chanGet words 2) active
          else
            if chanGet active 3 then
              triple_step 0#u8 (chanGet words 0) 1#u8 (chanGet words 1) 3#u8 (chanGet words 3) active
            else pair_step (chanGet words 0) (chanGet words 1) active
        else
          if chanGet active 2 then
            if chanGet active 3 then
              triple_step 0#u8 (chanGet words 0) 2#u8 (chanGet words 2) 3#u8 (chanGet words 3) active
            else pair_step (chanGet words 0) (chanGet words 2) active
          else
            if chanGet active 3 then pair_step (chanGet words 0) (chanGet words 3) active
            else ok (StepResult.Agreed (chanGet words 0) active)
      else
        if chanGet active 1 then
          if chanGet active 2 then
            if chanGet active 3 then
              triple_step 1#u8 (chanGet words 1) 2#u8 (chanGet words 2) 3#u8 (chanGet words 3) active
            else pair_step (chanGet words 1) (chanGet words 2) active
          else
            if chanGet active 3 then pair_step (chanGet words 1) (chanGet words 3) active
            else ok (StepResult.Agreed (chanGet words 1) active)
        else
          if chanGet active 2 then
            if chanGet active 3 then pair_step (chanGet words 2) (chanGet words 3) active
            else ok (StepResult.Agreed (chanGet words 2) active)
          else
            if chanGet active 3 then ok (StepResult.Agreed (chanGet words 3) active)
            else ok (StepResult.NoActiveChannels active)) := by
  unfold step
  simp only [index0_eq, index1_eq, index2_eq, index3_eq, bind_tc_ok]

/-- Finishes one `step`-dispatch branch: rewrites whichever of `quad_step_eq`
    / `triple{012,013,023,123}_eq` / `pair_step_unfold` applies to a fully
    resolved `ok (StepResult...)` case tree, or leaves the goal as-is if the
    branch is already a bare `ok (StepResult.Agreed ..)` /
    `ok (StepResult.NoActiveChannels ..)` (`step_unfold` itself, no helper
    call). `dsimp only` clears the `let`s `quad_step_eq` introduces before
    `split_ifs`, which otherwise cannot see through them. -/
macro "resolve_step_branch" : tactic =>
  `(tactic|
    first
      | rw [quad_step_eq]
      | rw [triple012_eq]
      | rw [triple013_eq]
      | rw [triple023_eq]
      | rw [triple123_eq]
      | rw [pair_step_unfold]
      | skip)

/-! # Reading channel `k` back out of `active.set k' false`

Used by `VoterStatements.lean` to show the new active set after a `Majority`
step is exactly the old one minus the disabled channel. -/

theorem chanGet_set0_self (active : Array Bool 4#usize) :
    chanGet (active.set 0#usize false) (0 : Fin 4) = false := by
  simp only [chanGet, Array.set_val_eq]; rw [List.getElem_set]; simp

theorem chanGet_set0_ne (active : Array Bool 4#usize) (k : Fin 4) (hk : k.val ≠ 0) :
    chanGet (active.set 0#usize false) k = chanGet active k := by
  simp only [chanGet, Array.set_val_eq]; rw [List.getElem_set]; simp [hk]

theorem chanGet_set1_self (active : Array Bool 4#usize) :
    chanGet (active.set 1#usize false) (1 : Fin 4) = false := by
  simp only [chanGet, Array.set_val_eq]; rw [List.getElem_set]; simp

theorem chanGet_set1_ne (active : Array Bool 4#usize) (k : Fin 4) (hk : k.val ≠ 1) :
    chanGet (active.set 1#usize false) k = chanGet active k := by
  simp only [chanGet, Array.set_val_eq]; rw [List.getElem_set]; simp [hk]

theorem chanGet_set2_self (active : Array Bool 4#usize) :
    chanGet (active.set 2#usize false) (2 : Fin 4) = false := by
  simp only [chanGet, Array.set_val_eq]; rw [List.getElem_set]; simp

theorem chanGet_set2_ne (active : Array Bool 4#usize) (k : Fin 4) (hk : k.val ≠ 2) :
    chanGet (active.set 2#usize false) k = chanGet active k := by
  simp only [chanGet, Array.set_val_eq]; rw [List.getElem_set]; simp [hk]

theorem chanGet_set3_self (active : Array Bool 4#usize) :
    chanGet (active.set 3#usize false) (3 : Fin 4) = false := by
  simp only [chanGet, Array.set_val_eq]; rw [List.getElem_set]; simp

theorem chanGet_set3_ne (active : Array Bool 4#usize) (k : Fin 4) (hk : k.val ≠ 3) :
    chanGet (active.set 3#usize false) k = chanGet active k := by
  simp only [chanGet, Array.set_val_eq]; rw [List.getElem_set]; simp [hk]

end VoterProof
