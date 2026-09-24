-- Formal statements of T1, T2, T3a, T3b, T4, over the code
-- extracted into `QuadVoterProof.lean`. Every theorem is proved here (or in
-- `VoterProof.lean`, which this file builds on); no `sorry`, no `axiom`.
--
-- Notation:
-- - `A active`        -- the set of active channels ("A").
-- - `out words i`      -- channel `i`'s command word this step ("out[i]").
-- - a fixed `F : Finset (Fin 4)`, `F.card ≤ 2`         -- the faulty channels.
-- - `h`                -- the per-step value all active correct (∉ F)
--   channels agree on; introduced where used (T3a, T3b) as an explicit
--   hypothesis. The premise says nothing about `h` being the right
--   command: under a shared flight-code bug the correct channels agree
--   on a wrong `h`, and the theorems deliver that wrong `h` just the
--   same. T2
--   does not use `F`/`h` at all: it is the single-step masking property for
--   an arbitrary claimed value `v` and an arbitrary small disagreement set,
--   independent of any fault model.
--
-- `resultActive`/`resultCommand`/`resultDisabledIs` read the three public
-- fields back out of a `StepResult` uniformly across its five variants, so
-- theorem statements do not have to match on the variant themselves.

import VoterProof

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open quad_voter_proof
open VoterProof

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace VoterStatements

/-- The set of active channels ("A"). -/
def A (active : Array Bool 4#usize) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => chanGet active i = true)

/-- Channel `i`'s command word this step ("out[i]"). -/
def out (words : Array U64 4#usize) (i : Fin 4) : U64 := chanGet words i

/-- The active set every `StepResult` variant carries. -/
def resultActive (r : StepResult) : Array Bool 4#usize :=
  match r with
  | .Agreed _ a => a
  | .Majority _ _ a => a
  | .Undetermined a => a
  | .OutsideHypothesis a => a
  | .NoActiveChannels a => a

/-- The command a `StepResult` carries, if any (`Agreed`/`Majority` only). -/
def resultCommand (r : StepResult) : Option U64 :=
  match r with
  | .Agreed c _ => some c
  | .Majority c _ _ => some c
  | _ => none

/-- Whether a `StepResult` disables exactly channel `d` (`Majority` only).
    Compares `.val : Nat`, never constructs a `U8` from `d`, so this is
    never a claim about `disable`'s `else`-branch fallback for a `U8`
    outside `0..=3` (that fallback is not reachable from `step`, and no
    theorem here quantifies over it — see `reports/PROOF.md`). -/
def resultDisabledIs (r : StepResult) (d : Fin 4) : Prop :=
  match r with
  | .Majority _ dis _ => dis.val = d.val
  | _ => False

theorem A_card_eq (active : Array Bool 4#usize) :
    (A active).card =
      (if chanGet active 0 then 1 else 0) + (if chanGet active 1 then 1 else 0) +
      (if chanGet active 2 then 1 else 0) + (if chanGet active 3 then 1 else 0) := by
  simp only [A]
  rw [show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide]
  simp [Finset.filter_insert, Finset.filter_singleton]
  split_ifs <;> decide

/-! # The new active set after disabling channel `K` -/

theorem A_set0_eq (active : Array Bool 4#usize) :
    A (active.set 0#usize false) = A active \ {(0:Fin 4)} := by
  ext k; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_singleton]
  by_cases hk : k = 0
  · subst hk; rw [chanGet_set0_self]; simp
  · rw [chanGet_set0_ne active k (fun h => hk (Fin.ext h))]; simp [hk]

theorem forall0_ne (active : Array Bool 4#usize) :
    ∀ j : Fin 4, j ≠ 0 → chanGet (active.set 0#usize false) j = chanGet active j := by
  intro j hj; exact chanGet_set0_ne active j (by intro h; apply hj; ext; omega)

theorem A_set1_eq (active : Array Bool 4#usize) :
    A (active.set 1#usize false) = A active \ {(1:Fin 4)} := by
  ext k; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_singleton]
  by_cases hk : k = 1
  · subst hk; rw [chanGet_set1_self]; simp
  · rw [chanGet_set1_ne active k (fun h => hk (Fin.ext h))]; simp [hk]

theorem forall1_ne (active : Array Bool 4#usize) :
    ∀ j : Fin 4, j ≠ 1 → chanGet (active.set 1#usize false) j = chanGet active j := by
  intro j hj; exact chanGet_set1_ne active j (by intro h; apply hj; ext; omega)

theorem A_set2_eq (active : Array Bool 4#usize) :
    A (active.set 2#usize false) = A active \ {(2:Fin 4)} := by
  ext k; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_singleton]
  by_cases hk : k = 2
  · subst hk; rw [chanGet_set2_self]; simp
  · rw [chanGet_set2_ne active k (fun h => hk (Fin.ext h))]; simp [hk]

theorem forall2_ne (active : Array Bool 4#usize) :
    ∀ j : Fin 4, j ≠ 2 → chanGet (active.set 2#usize false) j = chanGet active j := by
  intro j hj; exact chanGet_set2_ne active j (by intro h; apply hj; ext; omega)

theorem A_set3_eq (active : Array Bool 4#usize) :
    A (active.set 3#usize false) = A active \ {(3:Fin 4)} := by
  ext k; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_singleton]
  by_cases hk : k = 3
  · subst hk; rw [chanGet_set3_self]; simp
  · rw [chanGet_set3_ne active k (fun h => hk (Fin.ext h))]; simp [hk]

theorem forall3_ne (active : Array Bool 4#usize) :
    ∀ j : Fin 4, j ≠ 3 → chanGet (active.set 3#usize false) j = chanGet active j := by
  intro j hj; exact chanGet_set3_ne active j (by intro h; apply hj; ext; omega)

theorem T2_case_all (active : Array Bool 4#usize) (words : Array U64 4#usize) (v : U64)
    (ha0 : chanGet active 0 = true) (ha1 : chanGet active 1 = true)
    (ha2 : chanGet active 2 = true) (ha3 : chanGet active 3 = true) :
    (((A active).filter (fun i => out words i ≠ v)) = ∅ →
      step active words = ok (StepResult.Agreed v active)) ∧
    (∀ d, ((A active).filter (fun i => out words i ≠ v)) = {d} →
      ∃ r, step active words = ok r ∧ resultCommand r = some v ∧
        resultDisabledIs r d ∧ A (resultActive r) = A active \ {d} ∧
        ∀ j : Fin 4, j ≠ d → chanGet (resultActive r) j = chanGet active j) := by
  have hAmem : ∀ i : Fin 4, i ∈ A active := by
    intro i; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i <;> simp_all
  constructor
  · intro hD
    have hall : ∀ i : Fin 4, out words i = v := by
      intro i
      by_contra hne
      have : i ∈ (A active).filter (fun i => out words i ≠ v) := by
        simp only [Finset.mem_filter]; exact ⟨hAmem i, hne⟩
      rw [hD] at this; simp at this
    have hw0 := hall 0; have hw1 := hall 1; have hw2 := hall 2; have hw3 := hall 3
    simp only [out] at hw0 hw1 hw2 hw3
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true]
    rw [quad_step_eq]; dsimp only; rw [hw0, hw1, hw2, hw3]; simp
  · intro d hD
    have hmem : ∀ i : Fin 4, out words i ≠ v ↔ i = d := by
      intro i
      have hiff := Finset.ext_iff.mp hD i
      simp only [Finset.mem_filter, hAmem i, true_and, Finset.mem_singleton] at hiff
      exact hiff
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true]
    rw [quad_step_eq]; dsimp only
    fin_cases d
    · simp only [Fin.mk.injEq] at hmem
      have h0 := hmem 0; have h1 := hmem 1; have h2 := hmem 2; have h3 := hmem 3
      simp only [out] at h0 h1 h2 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set0_eq active, forall0_ne active⟩
    · simp only [Fin.mk.injEq] at hmem
      have h0 := hmem 0; have h1 := hmem 1; have h2 := hmem 2; have h3 := hmem 3
      simp only [out] at h0 h1 h2 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set1_eq active, forall1_ne active⟩
    · simp only [Fin.mk.injEq] at hmem
      have h0 := hmem 0; have h1 := hmem 1; have h2 := hmem 2; have h3 := hmem 3
      simp only [out] at h0 h1 h2 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set2_eq active, forall2_ne active⟩
    · simp only [Fin.mk.injEq] at hmem
      have h0 := hmem 0; have h1 := hmem 1; have h2 := hmem 2; have h3 := hmem 3
      simp only [out] at h0 h1 h2 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set3_eq active, forall3_ne active⟩


theorem T2_case_012 (active : Array Bool 4#usize) (words : Array U64 4#usize) (v : U64)
    (ha0 : chanGet active 0 = true) (ha1 : chanGet active 1 = true)
    (ha2 : chanGet active 2 = true) (ha3 : chanGet active 3 = false) :
    (((A active).filter (fun i => out words i ≠ v)) = ∅ →
      step active words = ok (StepResult.Agreed v active)) ∧
    (∀ d, ((A active).filter (fun i => out words i ≠ v)) = {d} →
      ∃ r, step active words = ok r ∧ resultCommand r = some v ∧
        resultDisabledIs r d ∧ A (resultActive r) = A active \ {d} ∧
        ∀ j : Fin 4, j ≠ d → chanGet (resultActive r) j = chanGet active j) := by
  have hAmem : ∀ i : Fin 4, i ∈ A active ↔ i.val ≠ 3 := by
    intro i; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i <;> simp_all
  constructor
  · intro hD
    have hall : ∀ i : Fin 4, i.val ≠ 3 → out words i = v := by
      intro i hi3
      by_contra hne
      have : i ∈ (A active).filter (fun i => out words i ≠ v) := by
        simp only [Finset.mem_filter]; exact ⟨(hAmem i).mpr hi3, hne⟩
      rw [hD] at this; simp at this
    have hw0 := hall 0 (by decide); have hw1 := hall 1 (by decide); have hw2 := hall 2 (by decide)
    simp only [out] at hw0 hw1 hw2
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true, if_false]
    rw [triple012_eq]; rw [hw0, hw1, hw2]; simp
  · intro d hD
    have hmem : ∀ i : Fin 4, i.val ≠ 3 → (out words i ≠ v ↔ i = d) := by
      intro i hi3
      have hiff := Finset.ext_iff.mp hD i
      simp only [Finset.mem_filter, (hAmem i).mpr hi3, true_and, Finset.mem_singleton] at hiff
      exact hiff
    have hd3 : d.val ≠ 3 := by
      intro hcontra
      have : d ∈ (A active).filter (fun i => out words i ≠ v) := by rw [hD]; simp
      simp only [Finset.mem_filter] at this
      exact absurd ((hAmem d).mp this.1) (by simp [hcontra])
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true, if_false]
    rw [triple012_eq]
    fin_cases d
    · have h0 := hmem 0 (by decide); have h1 := hmem 1 (by decide); have h2 := hmem 2 (by decide)
      simp only [out, Fin.mk.injEq] at h0 h1 h2
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set0_eq active, forall0_ne active⟩
    · have h0 := hmem 0 (by decide); have h1 := hmem 1 (by decide); have h2 := hmem 2 (by decide)
      simp only [out, Fin.mk.injEq] at h0 h1 h2
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set1_eq active, forall1_ne active⟩
    · have h0 := hmem 0 (by decide); have h1 := hmem 1 (by decide); have h2 := hmem 2 (by decide)
      simp only [out, Fin.mk.injEq] at h0 h1 h2
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set2_eq active, forall2_ne active⟩
    · exact absurd rfl hd3


-- active = {0,1,3}, a2 = false
theorem T2_case_013 (active : Array Bool 4#usize) (words : Array U64 4#usize) (v : U64)
    (ha0 : chanGet active 0 = true) (ha1 : chanGet active 1 = true)
    (ha2 : chanGet active 2 = false) (ha3 : chanGet active 3 = true) :
    (((A active).filter (fun i => out words i ≠ v)) = ∅ →
      step active words = ok (StepResult.Agreed v active)) ∧
    (∀ d, ((A active).filter (fun i => out words i ≠ v)) = {d} →
      ∃ r, step active words = ok r ∧ resultCommand r = some v ∧
        resultDisabledIs r d ∧ A (resultActive r) = A active \ {d} ∧
        ∀ j : Fin 4, j ≠ d → chanGet (resultActive r) j = chanGet active j) := by
  have hAmem : ∀ i : Fin 4, i ∈ A active ↔ i.val ≠ 2 := by
    intro i; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i <;> simp_all
  constructor
  · intro hD
    have hall : ∀ i : Fin 4, i.val ≠ 2 → out words i = v := by
      intro i hi2
      by_contra hne
      have : i ∈ (A active).filter (fun i => out words i ≠ v) := by
        simp only [Finset.mem_filter]; exact ⟨(hAmem i).mpr hi2, hne⟩
      rw [hD] at this; simp at this
    have hw0 := hall 0 (by decide); have hw1 := hall 1 (by decide); have hw3 := hall 3 (by decide)
    simp only [out] at hw0 hw1 hw3
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true, if_false]
    rw [triple013_eq]; rw [hw0, hw1, hw3]; simp
  · intro d hD
    have hmem : ∀ i : Fin 4, i.val ≠ 2 → (out words i ≠ v ↔ i = d) := by
      intro i hi2
      have hiff := Finset.ext_iff.mp hD i
      simp only [Finset.mem_filter, (hAmem i).mpr hi2, true_and, Finset.mem_singleton] at hiff
      exact hiff
    have hd2 : d.val ≠ 2 := by
      intro hcontra
      have : d ∈ (A active).filter (fun i => out words i ≠ v) := by rw [hD]; simp
      simp only [Finset.mem_filter] at this
      exact absurd ((hAmem d).mp this.1) (by simp [hcontra])
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true, if_false]
    rw [triple013_eq]
    fin_cases d
    · have h0 := hmem 0 (by decide); have h1 := hmem 1 (by decide); have h3 := hmem 3 (by decide)
      simp only [out, Fin.mk.injEq] at h0 h1 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set0_eq active, forall0_ne active⟩
    · have h0 := hmem 0 (by decide); have h1 := hmem 1 (by decide); have h3 := hmem 3 (by decide)
      simp only [out, Fin.mk.injEq] at h0 h1 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set1_eq active, forall1_ne active⟩
    · exact absurd rfl hd2
    · have h0 := hmem 0 (by decide); have h1 := hmem 1 (by decide); have h3 := hmem 3 (by decide)
      simp only [out, Fin.mk.injEq] at h0 h1 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set3_eq active, forall3_ne active⟩

-- active = {0,2,3}, a1 = false
theorem T2_case_023 (active : Array Bool 4#usize) (words : Array U64 4#usize) (v : U64)
    (ha0 : chanGet active 0 = true) (ha1 : chanGet active 1 = false)
    (ha2 : chanGet active 2 = true) (ha3 : chanGet active 3 = true) :
    (((A active).filter (fun i => out words i ≠ v)) = ∅ →
      step active words = ok (StepResult.Agreed v active)) ∧
    (∀ d, ((A active).filter (fun i => out words i ≠ v)) = {d} →
      ∃ r, step active words = ok r ∧ resultCommand r = some v ∧
        resultDisabledIs r d ∧ A (resultActive r) = A active \ {d} ∧
        ∀ j : Fin 4, j ≠ d → chanGet (resultActive r) j = chanGet active j) := by
  have hAmem : ∀ i : Fin 4, i ∈ A active ↔ i.val ≠ 1 := by
    intro i; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i <;> simp_all
  constructor
  · intro hD
    have hall : ∀ i : Fin 4, i.val ≠ 1 → out words i = v := by
      intro i hi1
      by_contra hne
      have : i ∈ (A active).filter (fun i => out words i ≠ v) := by
        simp only [Finset.mem_filter]; exact ⟨(hAmem i).mpr hi1, hne⟩
      rw [hD] at this; simp at this
    have hw0 := hall 0 (by decide); have hw2 := hall 2 (by decide); have hw3 := hall 3 (by decide)
    simp only [out] at hw0 hw2 hw3
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true, if_false]
    rw [triple023_eq]; rw [hw0, hw2, hw3]; simp
  · intro d hD
    have hmem : ∀ i : Fin 4, i.val ≠ 1 → (out words i ≠ v ↔ i = d) := by
      intro i hi1
      have hiff := Finset.ext_iff.mp hD i
      simp only [Finset.mem_filter, (hAmem i).mpr hi1, true_and, Finset.mem_singleton] at hiff
      exact hiff
    have hd1 : d.val ≠ 1 := by
      intro hcontra
      have : d ∈ (A active).filter (fun i => out words i ≠ v) := by rw [hD]; simp
      simp only [Finset.mem_filter] at this
      exact absurd ((hAmem d).mp this.1) (by simp [hcontra])
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true, if_false]
    rw [triple023_eq]
    fin_cases d
    · have h0 := hmem 0 (by decide); have h2 := hmem 2 (by decide); have h3 := hmem 3 (by decide)
      simp only [out, Fin.mk.injEq] at h0 h2 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set0_eq active, forall0_ne active⟩
    · exact absurd rfl hd1
    · have h0 := hmem 0 (by decide); have h2 := hmem 2 (by decide); have h3 := hmem 3 (by decide)
      simp only [out, Fin.mk.injEq] at h0 h2 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set2_eq active, forall2_ne active⟩
    · have h0 := hmem 0 (by decide); have h2 := hmem 2 (by decide); have h3 := hmem 3 (by decide)
      simp only [out, Fin.mk.injEq] at h0 h2 h3
      by_cases hw0 : chanGet words 0 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set3_eq active, forall3_ne active⟩

-- active = {1,2,3}, a0 = false
theorem T2_case_123 (active : Array Bool 4#usize) (words : Array U64 4#usize) (v : U64)
    (ha0 : chanGet active 0 = false) (ha1 : chanGet active 1 = true)
    (ha2 : chanGet active 2 = true) (ha3 : chanGet active 3 = true) :
    (((A active).filter (fun i => out words i ≠ v)) = ∅ →
      step active words = ok (StepResult.Agreed v active)) ∧
    (∀ d, ((A active).filter (fun i => out words i ≠ v)) = {d} →
      ∃ r, step active words = ok r ∧ resultCommand r = some v ∧
        resultDisabledIs r d ∧ A (resultActive r) = A active \ {d} ∧
        ∀ j : Fin 4, j ≠ d → chanGet (resultActive r) j = chanGet active j) := by
  have hAmem : ∀ i : Fin 4, i ∈ A active ↔ i.val ≠ 0 := by
    intro i; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i <;> simp_all
  constructor
  · intro hD
    have hall : ∀ i : Fin 4, i.val ≠ 0 → out words i = v := by
      intro i hi0
      by_contra hne
      have : i ∈ (A active).filter (fun i => out words i ≠ v) := by
        simp only [Finset.mem_filter]; exact ⟨(hAmem i).mpr hi0, hne⟩
      rw [hD] at this; simp at this
    have hw1 := hall 1 (by decide); have hw2 := hall 2 (by decide); have hw3 := hall 3 (by decide)
    simp only [out] at hw1 hw2 hw3
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true, if_false]
    rw [triple123_eq]; rw [hw1, hw2, hw3]; simp
  · intro d hD
    have hmem : ∀ i : Fin 4, i.val ≠ 0 → (out words i ≠ v ↔ i = d) := by
      intro i hi0
      have hiff := Finset.ext_iff.mp hD i
      simp only [Finset.mem_filter, (hAmem i).mpr hi0, true_and, Finset.mem_singleton] at hiff
      exact hiff
    have hd0 : d.val ≠ 0 := by
      intro hcontra
      have : d ∈ (A active).filter (fun i => out words i ≠ v) := by rw [hD]; simp
      simp only [Finset.mem_filter] at this
      exact absurd ((hAmem d).mp this.1) (by simp [hcontra])
    rw [step_unfold]; simp only [ha0, ha1, ha2, ha3, if_true, if_false]
    rw [triple123_eq]
    fin_cases d
    · exact absurd rfl hd0
    · have h1 := hmem 1 (by decide); have h2 := hmem 2 (by decide); have h3 := hmem 3 (by decide)
      simp only [out, Fin.mk.injEq] at h1 h2 h3
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set1_eq active, forall1_ne active⟩
    · have h1 := hmem 1 (by decide); have h2 := hmem 2 (by decide); have h3 := hmem 3 (by decide)
      simp only [out, Fin.mk.injEq] at h1 h2 h3
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set2_eq active, forall2_ne active⟩
    · have h1 := hmem 1 (by decide); have h2 := hmem 2 (by decide); have h3 := hmem 3 (by decide)
      simp only [out, Fin.mk.injEq] at h1 h2 h3
      by_cases hw1 : chanGet words 1 = v <;>
      by_cases hw2 : chanGet words 2 = v <;>
      by_cases hw3 : chanGet words 3 = v <;>
      simp_all
      exact ⟨rfl, rfl, A_set3_eq active, forall3_ne active⟩


/-- **T1 (no-panic).** For any active set and any command words, `step`
    returns `ok`. -/
theorem T1 (active : Array Bool 4#usize) (words : Array U64 4#usize) :
    ∃ r, step active words = ok r := by
  rw [step_unfold]
  split_ifs <;>
    first
      | (rw [quad_step_eq] <;> dsimp only <;> split_ifs <;> exact ⟨_, rfl⟩)
      | (rw [triple012_eq] <;> split_ifs <;> exact ⟨_, rfl⟩)
      | (rw [triple013_eq] <;> split_ifs <;> exact ⟨_, rfl⟩)
      | (rw [triple023_eq] <;> split_ifs <;> exact ⟨_, rfl⟩)
      | (rw [triple123_eq] <;> split_ifs <;> exact ⟨_, rfl⟩)
      | (rw [pair_step_unfold] <;> split_ifs <;> exact ⟨_, rfl⟩)
      | exact ⟨_, rfl⟩

/-- **T2 (masking, one step, arbitrary A).** Let `|A| ≥ 3`, `v` a value,
    `D = {i ∈ A | out[i] ≠ v}`, `|D| ≤ 1`. If `D = ∅`, the output is `v` and
    `A` is unchanged. If `D = {d}`, the output is `v`, the new `A` is
    `A \ {d}`, and no other channel is disabled. -/
theorem T2 (active : Array Bool 4#usize) (words : Array U64 4#usize) (v : U64)
    (hA3 : 3 ≤ (A active).card)
    (hD1 : ((A active).filter (fun i => out words i ≠ v)).card ≤ 1) :
    (((A active).filter (fun i => out words i ≠ v)) = ∅ →
      step active words = ok (StepResult.Agreed v active)) ∧
    (∀ d, ((A active).filter (fun i => out words i ≠ v)) = {d} →
      ∃ r, step active words = ok r ∧ resultCommand r = some v ∧
        resultDisabledIs r d ∧ A (resultActive r) = A active \ {d} ∧
        ∀ j : Fin 4, j ≠ d → chanGet (resultActive r) j = chanGet active j) := by
  clear hD1
  rw [A_card_eq] at hA3
  cases ha0 : chanGet active 0 <;>
  cases ha1 : chanGet active 1 <;>
  cases ha2 : chanGet active 2 <;>
  cases ha3 : chanGet active 3 <;>
  simp only [ha0, ha1, ha2, ha3, if_true, if_false, reduceIte] at hA3 <;>
  first
    | exact absurd hA3 (by decide)
    | exact T2_case_all active words v ha0 ha1 ha2 ha3
    | exact T2_case_012 active words v ha0 ha1 ha2 ha3
    | exact T2_case_013 active words v ha0 ha1 ha2 ha3
    | exact T2_case_023 active words v ha0 ha1 ha2 ha3
    | exact T2_case_123 active words v ha0 ha1 ha2 ha3

/-- **T4 (pair).** At `|A| = 2` with a disagreement, the result is
    `Undetermined`: no command is produced, `A` is unchanged. -/
theorem T4 (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (i j : Fin 4) (hij : i ≠ j) (hA : A active = {i, j})
    (hdisagree : out words i ≠ out words j) :
    step active words = ok (StepResult.Undetermined active) := by
  have hmem : ∀ k : Fin 4, chanGet active k = true ↔ (k = i ∨ k = j) := by
    intro k
    have := Finset.ext_iff.mp hA k
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at this
    exact this
  have h0 := hmem 0
  have h1 := hmem 1
  have h2 := hmem 2
  have h3 := hmem 3
  unfold out at hdisagree
  rw [step_unfold]
  fin_cases i <;> fin_cases j <;> simp_all <;>
    rw [pair_step_unfold] <;> simp [hdisagree]

theorem majority_source2_012 (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (ha0 : chanGet active 0 = true) (ha1 : chanGet active 1 = true)
    (ha2 : chanGet active 2 = true) (ha3 : chanGet active 3 = false)
    (c : U64) (dis : U8) (active' : Array Bool 4#usize)
    (hr : step active words = ok (StepResult.Majority c dis active')) :
    (dis = 0#u8 ∧ chanGet words 1 = c ∧ chanGet words 2 = c ∧ chanGet words 0 ≠ c ∧
      active' = active.set 0#usize false) ∨
    (dis = 1#u8 ∧ chanGet words 0 = c ∧ chanGet words 2 = c ∧ chanGet words 1 ≠ c ∧
      active' = active.set 1#usize false) ∨
    (dis = 2#u8 ∧ chanGet words 0 = c ∧ chanGet words 1 = c ∧ chanGet words 2 ≠ c ∧
      active' = active.set 2#usize false) := by
  rw [step_unfold] at hr
  simp only [ha0, ha1, ha2, ha3] at hr
  rw [triple012_eq] at hr
  split_ifs at hr <;> simp_all <;> tauto


theorem majority_source2_013 (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (ha0 : chanGet active 0 = true) (ha1 : chanGet active 1 = true)
    (ha2 : chanGet active 2 = false) (ha3 : chanGet active 3 = true)
    (c : U64) (dis : U8) (active' : Array Bool 4#usize)
    (hr : step active words = ok (StepResult.Majority c dis active')) :
    (dis = 0#u8 ∧ chanGet words 1 = c ∧ chanGet words 3 = c ∧ chanGet words 0 ≠ c ∧
      active' = active.set 0#usize false) ∨
    (dis = 1#u8 ∧ chanGet words 0 = c ∧ chanGet words 3 = c ∧ chanGet words 1 ≠ c ∧
      active' = active.set 1#usize false) ∨
    (dis = 3#u8 ∧ chanGet words 0 = c ∧ chanGet words 1 = c ∧ chanGet words 3 ≠ c ∧
      active' = active.set 3#usize false) := by
  rw [step_unfold] at hr
  simp only [ha0, ha1, ha2, ha3] at hr
  rw [triple013_eq] at hr
  split_ifs at hr <;> simp_all <;> tauto

theorem majority_source2_023 (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (ha0 : chanGet active 0 = true) (ha1 : chanGet active 1 = false)
    (ha2 : chanGet active 2 = true) (ha3 : chanGet active 3 = true)
    (c : U64) (dis : U8) (active' : Array Bool 4#usize)
    (hr : step active words = ok (StepResult.Majority c dis active')) :
    (dis = 0#u8 ∧ chanGet words 2 = c ∧ chanGet words 3 = c ∧ chanGet words 0 ≠ c ∧
      active' = active.set 0#usize false) ∨
    (dis = 2#u8 ∧ chanGet words 0 = c ∧ chanGet words 3 = c ∧ chanGet words 2 ≠ c ∧
      active' = active.set 2#usize false) ∨
    (dis = 3#u8 ∧ chanGet words 0 = c ∧ chanGet words 2 = c ∧ chanGet words 3 ≠ c ∧
      active' = active.set 3#usize false) := by
  rw [step_unfold] at hr
  simp only [ha0, ha1, ha2, ha3] at hr
  rw [triple023_eq] at hr
  split_ifs at hr <;> simp_all <;> tauto

theorem majority_source2_123 (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (ha0 : chanGet active 0 = false) (ha1 : chanGet active 1 = true)
    (ha2 : chanGet active 2 = true) (ha3 : chanGet active 3 = true)
    (c : U64) (dis : U8) (active' : Array Bool 4#usize)
    (hr : step active words = ok (StepResult.Majority c dis active')) :
    (dis = 1#u8 ∧ chanGet words 2 = c ∧ chanGet words 3 = c ∧ chanGet words 1 ≠ c ∧
      active' = active.set 1#usize false) ∨
    (dis = 2#u8 ∧ chanGet words 1 = c ∧ chanGet words 3 = c ∧ chanGet words 2 ≠ c ∧
      active' = active.set 2#usize false) ∨
    (dis = 3#u8 ∧ chanGet words 1 = c ∧ chanGet words 2 = c ∧ chanGet words 3 ≠ c ∧
      active' = active.set 3#usize false) := by
  rw [step_unfold] at hr
  simp only [ha0, ha1, ha2, ha3] at hr
  rw [triple123_eq] at hr
  split_ifs at hr <;> simp_all <;> tauto

theorem majority_source2_all (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (ha0 : chanGet active 0 = true) (ha1 : chanGet active 1 = true)
    (ha2 : chanGet active 2 = true) (ha3 : chanGet active 3 = true)
    (c : U64) (dis : U8) (active' : Array Bool 4#usize)
    (hr : step active words = ok (StepResult.Majority c dis active')) :
    (dis = 0#u8 ∧ chanGet words 1 = c ∧ chanGet words 2 = c ∧ chanGet words 3 = c ∧
      chanGet words 0 ≠ c ∧ active' = active.set 0#usize false) ∨
    (dis = 1#u8 ∧ chanGet words 0 = c ∧ chanGet words 2 = c ∧ chanGet words 3 = c ∧
      chanGet words 1 ≠ c ∧ active' = active.set 1#usize false) ∨
    (dis = 2#u8 ∧ chanGet words 0 = c ∧ chanGet words 1 = c ∧ chanGet words 3 = c ∧
      chanGet words 2 ≠ c ∧ active' = active.set 2#usize false) ∨
    (dis = 3#u8 ∧ chanGet words 0 = c ∧ chanGet words 1 = c ∧ chanGet words 2 = c ∧
      chanGet words 3 ≠ c ∧ active' = active.set 3#usize false) := by
  rw [step_unfold] at hr
  simp only [ha0, ha1, ha2, ha3] at hr
  rw [quad_step_eq] at hr
  dsimp only at hr
  split_ifs at hr <;> simp_all <;> tauto


/-- Whenever `step` succeeds, either the result is `Majority`, or the
    active set the result carries is exactly the input `active` (`Agreed`,
    `Undetermined`, `OutsideHypothesis`, `NoActiveChannels` all pass the
    input active set through unchanged). -/
theorem step_majority_or_unchanged (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (r : StepResult) (hr : step active words = ok r) :
    (∃ c dis a, r = StepResult.Majority c dis a) ∨ resultActive r = active := by
  rw [step_unfold] at hr
  cases ha0 : chanGet active 0 <;> cases ha1 : chanGet active 1 <;>
  cases ha2 : chanGet active 2 <;> cases ha3 : chanGet active 3 <;>
  simp only [ha0, ha1, ha2, ha3, Bool.false_eq_true, if_true, if_false] at hr <;>
  first
    | (rw [quad_step_eq] at hr; dsimp only at hr; split_ifs at hr <;>
       (try simp only [ok.injEq] at hr) <;> (try subst hr) <;>
       first | (left; exact ⟨_, _, _, rfl⟩) | (right; rfl))
    | (rw [triple012_eq] at hr; split_ifs at hr <;>
       (try simp only [ok.injEq] at hr) <;> (try subst hr) <;>
       first | (left; exact ⟨_, _, _, rfl⟩) | (right; rfl))
    | (rw [triple013_eq] at hr; split_ifs at hr <;>
       (try simp only [ok.injEq] at hr) <;> (try subst hr) <;>
       first | (left; exact ⟨_, _, _, rfl⟩) | (right; rfl))
    | (rw [triple023_eq] at hr; split_ifs at hr <;>
       (try simp only [ok.injEq] at hr) <;> (try subst hr) <;>
       first | (left; exact ⟨_, _, _, rfl⟩) | (right; rfl))
    | (rw [triple123_eq] at hr; split_ifs at hr <;>
       (try simp only [ok.injEq] at hr) <;> (try subst hr) <;>
       first | (left; exact ⟨_, _, _, rfl⟩) | (right; rfl))
    | (rw [pair_step_unfold] at hr; split_ifs at hr <;>
       (try simp only [ok.injEq] at hr) <;> (try subst hr) <;> right <;> rfl)
    | ((try simp only [ok.injEq] at hr) <;> (try subst hr) <;> right <;> rfl)

/-- Total, panic-free version of `step`: the new active set, given `step`
    always succeeds (`T1`). -/
def stepActive (active : Array Bool 4#usize) (words : Array U64 4#usize) : Array Bool 4#usize :=
  match step active words with
  | Result.ok r => resultActive r
  | _ => active

theorem stepActive_eq (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (r : StepResult) (hr : step active words = ok r) :
    stepActive active words = resultActive r := by
  unfold stepActive; rw [hr]

/-- If the correct (∉ `F`) channels all active in a 4-element set agree on
    `h`, and a majority disables channel `K` in favor of value `c ≠ out K`,
    with the other three channels agreeing on `c`, then `K ∈ F` — otherwise
    a second correct channel would force `c = h = out K`, contradiction. -/
theorem quad_disable_in_F {out : Fin 4 → U64} (F : Finset (Fin 4)) (hF : F.card ≤ 2)
    (h c : U64) (hAgree : ∀ i : Fin 4, i ∉ F → out i = h)
    (K : Fin 4) (hKc : out K ≠ c)
    (hOthers : ∀ j : Fin 4, j ≠ K → out j = c) :
    K ∈ F := by
  by_contra hKF
  have hsub : ¬ (Finset.univ.erase K ⊆ F) := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ K), Finset.card_univ] at hcard
    simp at hcard
    omega
  rw [Finset.not_subset] at hsub
  obtain ⟨e, he, heF⟩ := hsub
  have heK : e ≠ K := (Finset.mem_erase.mp he).1
  have h1 : out e = h := hAgree e heF
  have h2 : out e = c := hOthers e heK
  have h3 : out K = h := hAgree K hKF
  exact hKc (h3.trans (h1.symm.trans h2))

/-- Same as `quad_disable_in_F`, but for a step with only three of the four
    channels active (`M` is the fourth, known to be in `F` since the
    invariant already accounts for it). -/
theorem triple_disable_in_F {out : Fin 4 → U64} (F : Finset (Fin 4)) (hF : F.card ≤ 2)
    (M : Fin 4) (hM : M ∈ F) (h c : U64)
    (hAgree : ∀ i : Fin 4, i ≠ M → i ∉ F → out i = h)
    (K : Fin 4) (hKM : K ≠ M) (hKc : out K ≠ c)
    (hOthers : ∀ j : Fin 4, j ≠ K → j ≠ M → out j = c) :
    K ∈ F := by
  by_contra hKF
  have hKmem : K ∈ Finset.univ.erase M := Finset.mem_erase.mpr ⟨hKM, Finset.mem_univ K⟩
  have hsub : ¬ ((Finset.univ.erase M).erase K ⊆ F) := by
    intro hsub
    have hbig : insert M ((Finset.univ.erase M).erase K) ⊆ F := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hxM | hxrest
      · rw [hxM]; exact hM
      · exact hsub hxrest
    have hcard := Finset.card_le_card hbig
    have hMnotin : M ∉ (Finset.univ.erase M).erase K := by simp
    rw [Finset.card_insert_of_notMem hMnotin, Finset.card_erase_of_mem hKmem,
      Finset.card_erase_of_mem (Finset.mem_univ M), Finset.card_univ] at hcard
    simp at hcard
    omega
  rw [Finset.not_subset] at hsub
  obtain ⟨e, he, heF⟩ := hsub
  have he' := Finset.mem_erase.mp he
  have heK : e ≠ K := he'.1
  have he'' := Finset.mem_erase.mp he'.2
  have heM : e ≠ M := he''.1
  have h1 : out e = h := hAgree e heM heF
  have h2 : out e = c := hOthers e heK heM
  have h3 : out K = h := hAgree K hKM hKF
  exact hKc (h3.trans (h1.symm.trans h2))

theorem sdiff_erase_subset {A_active : Finset (Fin 4)} {F : Finset (Fin 4)} {K : Fin 4}
    (hKF : K ∈ F) (hInv : Finset.univ \ A_active ⊆ F) :
    Finset.univ \ (A_active \ {K}) ⊆ F := by
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton, not_and,
    not_not] at hx
  by_cases hxA : x ∈ A_active
  · have := hx hxA
    rw [this]; exact hKF
  · exact hInv (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxA⟩)

/-- **Invariant step.** If every channel not in `F` is currently active
    (`hInv`), `F.card ≤ 2`, and the active correct channels agree on `h`,
    then every channel not in `F` is still active after one more step. This
    is the induction step of T3a. -/
theorem step_preserves_correct (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (F : Finset (Fin 4)) (hF : F.card ≤ 2) (hInv : (Finset.univ \ A active) ⊆ F)
    (h : U64) (hAgree : ∀ i : Fin 4, i ∈ A active → i ∉ F → out words i = h) :
    (Finset.univ \ A (stepActive active words)) ⊆ F := by
  obtain ⟨r, hr⟩ := T1 active words
  rw [stepActive_eq active words r hr]
  rcases step_majority_or_unchanged active words r hr with ⟨c, dis, a, hrm⟩ | hunc
  · subst hrm
    simp only [resultActive]
    cases ha0 : chanGet active 0 <;> cases ha1 : chanGet active 1 <;>
    cases ha2 : chanGet active 2 <;> cases ha3 : chanGet active 3 <;>
    first
      | (have hM := majority_source2_all active words ha0 ha1 ha2 ha3 c dis a hr
         have hAactive : A active = Finset.univ := by
           ext k; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
           fin_cases k <;> simp_all
         rcases hM with ⟨hd, hw1, hw2, hw3, hwd, hact⟩ | ⟨hd, hw1, hw2, hw3, hwd, hact⟩ |
           ⟨hd, hw1, hw2, hw3, hwd, hact⟩ | ⟨hd, hw1, hw2, hw3, hwd, hact⟩ <;>
         subst hd <;> subst hact <;>
         first
           | (rw [A_set0_eq]
              apply sdiff_erase_subset
                (quad_disable_in_F F hF h c
                  (fun i hiF => hAgree i (hAactive ▸ Finset.mem_univ i) hiF)
                  0 (by simpa only [out] using hwd)
                  (fun j hj0 => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set1_eq]
              apply sdiff_erase_subset
                (quad_disable_in_F F hF h c
                  (fun i hiF => hAgree i (hAactive ▸ Finset.mem_univ i) hiF)
                  1 (by simpa only [out] using hwd)
                  (fun j hj1 => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set2_eq]
              apply sdiff_erase_subset
                (quad_disable_in_F F hF h c
                  (fun i hiF => hAgree i (hAactive ▸ Finset.mem_univ i) hiF)
                  2 (by simpa only [out] using hwd)
                  (fun j hj2 => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set3_eq]
              apply sdiff_erase_subset
                (quad_disable_in_F F hF h c
                  (fun i hiF => hAgree i (hAactive ▸ Finset.mem_univ i) hiF)
                  3 (by simpa only [out] using hwd)
                  (fun j hj3 => by
                    fin_cases j <;> simp_all [out]))
                hInv))
      | (have hM' := majority_source2_012 active words ha0 ha1 ha2 ha3 c dis a hr
         have hM : (3 : Fin 4) ∈ F := by
           apply hInv
           simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, A, Finset.mem_filter]
           simp_all
         have hAactiveM : ∀ i : Fin 4, i.val ≠ 3 → i ∈ A active := by
           intro i hiM
           simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
           fin_cases i <;> simp_all
         have hAgree' : ∀ i : Fin 4, i ≠ 3 → i ∉ F → out words i = h := by
           intro i hiM hiF
           exact hAgree i (hAactiveM i (fun hh => hiM (Fin.ext hh))) hiF
         rcases hM' with ⟨hd, hw1, hw2, hwd, hact⟩ | ⟨hd, hw1, hw2, hwd, hact⟩ | ⟨hd, hw1, hw2, hwd, hact⟩ <;>
         subst hd <;> subst hact <;>
         first
           | (rw [A_set0_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 3 hM h c hAgree'
                  0 (by decide) (by simpa only [out] using hwd)
                  (fun j hj0 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set1_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 3 hM h c hAgree'
                  1 (by decide) (by simpa only [out] using hwd)
                  (fun j hj1 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set2_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 3 hM h c hAgree'
                  2 (by decide) (by simpa only [out] using hwd)
                  (fun j hj2 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
         )
      | (have hM' := majority_source2_023 active words ha0 ha1 ha2 ha3 c dis a hr
         have hM : (1 : Fin 4) ∈ F := by
           apply hInv
           simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, A, Finset.mem_filter]
           simp_all
         have hAactiveM : ∀ i : Fin 4, i.val ≠ 1 → i ∈ A active := by
           intro i hiM
           simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
           fin_cases i <;> simp_all
         have hAgree' : ∀ i : Fin 4, i ≠ 1 → i ∉ F → out words i = h := by
           intro i hiM hiF
           exact hAgree i (hAactiveM i (fun hh => hiM (Fin.ext hh))) hiF
         rcases hM' with ⟨hd, hw1, hw2, hwd, hact⟩ | ⟨hd, hw1, hw2, hwd, hact⟩ | ⟨hd, hw1, hw2, hwd, hact⟩ <;>
         subst hd <;> subst hact <;>
         first
           | (rw [A_set0_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 1 hM h c hAgree'
                  0 (by decide) (by simpa only [out] using hwd)
                  (fun j hj0 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set2_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 1 hM h c hAgree'
                  2 (by decide) (by simpa only [out] using hwd)
                  (fun j hj2 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set3_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 1 hM h c hAgree'
                  3 (by decide) (by simpa only [out] using hwd)
                  (fun j hj3 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
         )
      | (have hM' := majority_source2_013 active words ha0 ha1 ha2 ha3 c dis a hr
         have hM : (2 : Fin 4) ∈ F := by
           apply hInv
           simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, A, Finset.mem_filter]
           simp_all
         have hAactiveM : ∀ i : Fin 4, i.val ≠ 2 → i ∈ A active := by
           intro i hiM
           simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
           fin_cases i <;> simp_all
         have hAgree' : ∀ i : Fin 4, i ≠ 2 → i ∉ F → out words i = h := by
           intro i hiM hiF
           exact hAgree i (hAactiveM i (fun hh => hiM (Fin.ext hh))) hiF
         rcases hM' with ⟨hd, hw1, hw2, hwd, hact⟩ | ⟨hd, hw1, hw2, hwd, hact⟩ | ⟨hd, hw1, hw2, hwd, hact⟩ <;>
         subst hd <;> subst hact <;>
         first
           | (rw [A_set0_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 2 hM h c hAgree'
                  0 (by decide) (by simpa only [out] using hwd)
                  (fun j hj0 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set1_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 2 hM h c hAgree'
                  1 (by decide) (by simpa only [out] using hwd)
                  (fun j hj1 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set3_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 2 hM h c hAgree'
                  3 (by decide) (by simpa only [out] using hwd)
                  (fun j hj3 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
         )
      | (have hM' := majority_source2_123 active words ha0 ha1 ha2 ha3 c dis a hr
         have hM : (0 : Fin 4) ∈ F := by
           apply hInv
           simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, A, Finset.mem_filter]
           simp_all
         have hAactiveM : ∀ i : Fin 4, i.val ≠ 0 → i ∈ A active := by
           intro i hiM
           simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
           fin_cases i <;> simp_all
         have hAgree' : ∀ i : Fin 4, i ≠ 0 → i ∉ F → out words i = h := by
           intro i hiM hiF
           exact hAgree i (hAactiveM i (fun hh => hiM (Fin.ext hh))) hiF
         rcases hM' with ⟨hd, hw1, hw2, hwd, hact⟩ | ⟨hd, hw1, hw2, hwd, hact⟩ | ⟨hd, hw1, hw2, hwd, hact⟩ <;>
         subst hd <;> subst hact <;>
         first
           | (rw [A_set1_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 0 hM h c hAgree'
                  1 (by decide) (by simpa only [out] using hwd)
                  (fun j hj1 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set2_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 0 hM h c hAgree'
                  2 (by decide) (by simpa only [out] using hwd)
                  (fun j hj2 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
           | (rw [A_set3_eq]
              apply sdiff_erase_subset
                (triple_disable_in_F F hF 0 hM h c hAgree'
                  3 (by decide) (by simpa only [out] using hwd)
                  (fun j hj3 hjM => by
                    fin_cases j <;> simp_all [out]))
                hInv)
         )
      | (-- Pair / single / empty active pattern: `Majority` cannot arise
         -- there, so `hr` is contradictory.
         exfalso
         rw [step_unfold] at hr
         simp only [ha0, ha1, ha2, ha3, Bool.false_eq_true, if_true, if_false] at hr
         first
           | (rw [pair_step_unfold] at hr; split_ifs at hr <;>
              simp only [ok.injEq] at hr <;> exact StepResult.noConfusion hr)
           | (simp only [ok.injEq] at hr; exact StepResult.noConfusion hr))
  · rw [hunc]; exact hInv


/-- The trace's fixed starting state: all four channels active
    (`A = {0,1,2,3}`). -/
def allActive : Array Bool 4#usize := Array.repeat 4#usize true

theorem A_allActive : A allActive = Finset.univ := by
  ext k
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, chanGet, allActive]
  fin_cases k <;> rfl

/-- The active-set trace: `activeSeq wordsSeq 0 = allActive`, each further
    step is the extracted `step` applied to the previous active set and
    that step's command words. Not a Rust loop — a fold, in Lean, over the
    extracted `step`. -/
def activeSeq (wordsSeq : Nat → Array U64 4#usize) : Nat → Array Bool 4#usize
  | 0 => allActive
  | n + 1 => stepActive (activeSeq wordsSeq n) (wordsSeq n)

/-- **T3a (reachable traces, no assumption about failure order).** On any
    finite trace from `A = {0,1,2,3}`, the invariant "every channel not in
    `F` is active" is preserved by each step, hence proved by induction on
    the trace. In particular, a correct (∉ `F`) channel is never disabled.

    Needs, at every step, the per-step premise bundled into `h`'s own
    definition: the correct active channels agree on a common value `h`.
    The premise says nothing about `h` being the right command: under a
    shared flight-code bug the correct channels agree on a wrong `h`, and
    the invariant proved here holds regardless — it is about which channel
    gets disabled, not about what value is output.
    `F` is fixed along the trace with `|F| ≤ 2`.
    T3a is stated only for traces starting at four active channels — for an
    arbitrary starting state it is false (counterexample: `A` = one
    correct channel plus two faulty channels, all three active; the two
    faulty channels coincidentally agree on a value `w`, the correct
    channel is the lone dissenter, and `step` disables it; see
    `reports/PROOF.md`). -/
theorem T3a (wordsSeq : Nat → Array U64 4#usize) (F : Finset (Fin 4)) (hF : F.card ≤ 2)
    (hAgree : ∀ n : Nat, ∃ h : U64,
      ∀ i : Fin 4, i ∈ A (activeSeq wordsSeq n) → i ∉ F → out (wordsSeq n) i = h) :
    ∀ n : Nat, Finset.univ \ A (activeSeq wordsSeq n) ⊆ F := by
  intro n
  induction n with
  | zero =>
    show Finset.univ \ A allActive ⊆ F
    rw [A_allActive]
    simp
  | succ n ih =>
    show Finset.univ \ A (stepActive (activeSeq wordsSeq n) (wordsSeq n)) ⊆ F
    obtain ⟨h, hAgreeN⟩ := hAgree n
    exact step_preserves_correct (activeSeq wordsSeq n) (wordsSeq n) F hF ih h hAgreeN

/-- T3a's headline corollary: a correct (∉ `F`) channel is never disabled
    along any trace from four active channels. -/
theorem T3a_correct_never_disabled (wordsSeq : Nat → Array U64 4#usize)
    (F : Finset (Fin 4)) (hF : F.card ≤ 2)
    (hAgree : ∀ n : Nat, ∃ h : U64,
      ∀ i : Fin 4, i ∈ A (activeSeq wordsSeq n) → i ∉ F → out (wordsSeq n) i = h) :
    ∀ (n : Nat) (i : Fin 4), i ∉ F → i ∈ A (activeSeq wordsSeq n) := by
  intro n i hiF
  have hInv := T3a wordsSeq F hF hAgree n
  by_contra hni
  exact hiF (hInv (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hni⟩))

/-- T3a's invariant also gives "`A \ F` nonempty": since every channel not
    in `F` is active (`T3a_correct_never_disabled`) and `F.card ≤ 2 < 4`,
    some channel outside `F` exists and is active. -/
theorem T3a_nonempty (wordsSeq : Nat → Array U64 4#usize)
    (F : Finset (Fin 4)) (hF : F.card ≤ 2)
    (hAgree : ∀ n : Nat, ∃ h : U64,
      ∀ i : Fin 4, i ∈ A (activeSeq wordsSeq n) → i ∉ F → out (wordsSeq n) i = h) :
    ∀ n : Nat, (A (activeSeq wordsSeq n) \ F).Nonempty := by
  intro n
  have hcorrect := T3a_correct_never_disabled wordsSeq F hF hAgree n
  have hUnivF : (Finset.univ \ F).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ F)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨i, hi⟩ := hUnivF
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
  exact ⟨i, Finset.mem_sdiff.mpr ⟨hcorrect i hi, hi⟩⟩

theorem resultCommand_outside_ne (active : Array Bool 4#usize) (r : StepResult) (v : U64)
    (hc : resultCommand r = some v) : r ≠ StepResult.OutsideHypothesis active := by
  intro h; rw [h] at hc; simp [resultCommand] at hc

/-- When exactly two channels `i ≠ j` are active and both agree on `v`,
    `step` returns `Agreed v` (converse of T4's disagreement case). -/
theorem step_pair_agree (active : Array Bool 4#usize) (words : Array U64 4#usize)
    (i j : Fin 4) (hij : i ≠ j) (hA : A active = {i, j}) (v : U64)
    (hi : out words i = v) (hj : out words j = v) :
    step active words = ok (StepResult.Agreed v active) := by
  have hmem : ∀ k : Fin 4, chanGet active k = true ↔ (k = i ∨ k = j) := by
    intro k
    have := Finset.ext_iff.mp hA k
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at this
    exact this
  have h0 := hmem 0
  have h1 := hmem 1
  have h2 := hmem 2
  have h3 := hmem 3
  unfold out at hi hj
  rw [step_unfold]
  fin_cases i <;> fin_cases j <;> simp_all <;>
    rw [pair_step_unfold] <;> simp_all

/-- **T3b (reachable traces, with the "faults reveal one at a time"
    assumption).** Same hypotheses as T3a, plus: at every step, at most one
    *faulty* active channel disagrees with the per-step correct value `h`
    (the added premise for T3b, stated in the same existential as `h` —
    bound in the same clause as `h` itself, not as a separate later
    hypothesis). Then, at every step: (b) while `|A| ≥ 3` the
    output is `h`; (c) the result is never `OutsideHypothesis`; (d) when
    `|A| = 2` (both channels active there are correct, by T3a) the output
    is `h`.

    The conclusion is stated for `∀ h`, with the two per-step premises
    (correct channels agree on `h`; at most one active faulty channel
    disagrees with `h`) repeated as hypotheses of the conclusion itself —
    not as a fresh `∃ h`, which would only witness "step outputs *some*
    value" and let `h` be read back as whatever `step` happened to output,
    proving nothing about it being the healthy value. Both premises hold
    of at most one `h` per step in practice (any two active correct
    channels agree with each other, since each agrees with `h`), so this
    is not a weaker statement than an existential one; it is what ties the
    output to *the* value the correct channels emit, per (b)/(d) above.
    (b) and (d) are proved together as one `resultCommand = some h` fact
    — `|A|` is always 2, 3, or 4 along such a trace (T3a), and both cases
    give command `h` — plus the separate `OutsideHypothesis`-exclusion (c),
    which needs no case split at all (`resultCommand (OutsideHypothesis _)
    = none ≠ some h`). The outer `hAgree` hypothesis is still required: T3a
    (invoked internally, for the invariant "every channel not in `F` is
    active") needs the per-step correct-agreement premise at *every* step
    of the trace, not just at the one step the conclusion is instantiated
    at. -/
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
        r ≠ StepResult.OutsideHypothesis (activeSeq wordsSeq n) := by
  intro n h hAgreeCorrect hAgreeFaulty
  set active := activeSeq wordsSeq n with hactive_def
  set words := wordsSeq n with hwords_def
  have hInv := T3a wordsSeq F hF (fun m => (hAgree m).imp (fun h' hh' => hh'.1)) n
  rw [← hactive_def] at hInv
  have hD_eq : (A active).filter (fun i => out words i ≠ h) =
      (A active ∩ F).filter (fun i => out words i ≠ h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hiA, hine⟩
      refine ⟨⟨hiA, ?_⟩, hine⟩
      by_contra hiF
      exact hine (hAgreeCorrect i hiA hiF)
    · rintro ⟨⟨hiA, _⟩, hine⟩
      exact ⟨hiA, hine⟩
  have hD1 : ((A active).filter (fun i => out words i ≠ h)).card ≤ 1 := by
    rw [hD_eq]; exact hAgreeFaulty
  have hAcard2 : 2 ≤ (A active).card := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A active))
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have hle : (Finset.univ \ A active).card ≤ F.card := Finset.card_le_card hInv
    omega
  by_cases hAcard3 : 3 ≤ (A active).card
  · obtain ⟨hEmpty, hSingle⟩ := T2 active words h hAcard3 hD1
    by_cases hD0 : (A active).filter (fun i => out words i ≠ h) = ∅
    · exact ⟨StepResult.Agreed h active, hEmpty hD0, rfl,
        resultCommand_outside_ne active _ h rfl⟩
    · obtain ⟨d, hd⟩ := Finset.card_eq_one.mp
        (le_antisymm hD1 (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hD0)))
      obtain ⟨r, hr, hc, _, _, _⟩ := hSingle d hd
      exact ⟨r, hr, hc, resultCommand_outside_ne active r h hc⟩
  · have hAcard2' : (A active).card = 2 := by omega
    obtain ⟨i, j, hij, hAij⟩ := Finset.card_eq_two.mp hAcard2'
    have hiA : i ∈ A active := by rw [hAij]; simp
    have hjA : j ∈ A active := by rw [hAij]; simp
    have hFeq : Finset.univ \ A active = F := by
      apply Finset.eq_of_subset_of_card_le hInv
      have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A active))
      rw [Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hiF : i ∉ F := by rw [← hFeq]; simp [hiA]
    have hjF : j ∉ F := by rw [← hFeq]; simp [hjA]
    have hi_eq : out words i = h := hAgreeCorrect i hiA hiF
    have hj_eq : out words j = h := hAgreeCorrect j hjA hjF
    have hstep := step_pair_agree active words i j hij hAij h hi_eq hj_eq
    exact ⟨StepResult.Agreed h active, hstep, rfl,
      resultCommand_outside_ne active _ h rfl⟩


end VoterStatements
