import Mathlib

/-!
# Capacities of the §3 extraction

The §3 extraction (de Saxcé, Prop. 5) accumulates orthonormal directions along the flag; the
*number* of directions available at stage `s` is the supply count `c s`, and the family built after
`R` stages has the size of the *running maximum* of the supply counts.  This module records that
elementary arithmetic.

Module `Submission.Work.Extraction.Capacity`, namespace `Submission.Capacity`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace Submission.Capacity

/-- The running maximum of a sequence (shifted so that `cap c (s+1)` uses `c s`). -/
def cap (c : ℕ → ℕ) : ℕ → ℕ := fun s => Nat.rec 0 (fun s ih => max ih (c s)) s

lemma cap_zero (c : ℕ → ℕ) : cap c 0 = 0 := rfl

lemma cap_succ (c : ℕ → ℕ) (s : ℕ) : cap c (s + 1) = max (cap c s) (c s) := rfl

lemma cap_mono (c : ℕ → ℕ) : Monotone (cap c) := by
  intro s t hst
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih =>
      rw [cap_succ]
      exact le_trans ih (le_max_left _ _)

lemma cap_le_cap (c : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) : cap c s ≤ cap c t := cap_mono c hst

/-- Every supply count up to stage `s` is at most the capacity at `s`. -/
lemma le_cap (c : ℕ → ℕ) {i s : ℕ} (his : i ≤ s) : c i ≤ cap c (i + 1) ∧ cap c (i + 1) ≤ cap c (s + 1) := by
  refine ⟨?_, cap_le_cap c (by omega)⟩
  rw [cap_succ]
  exact le_max_right _ _

lemma c_le_cap (c : ℕ → ℕ) {i s : ℕ} (his : i ≤ s) : c i ≤ cap c (s + 1) :=
  le_trans (le_cap c his).1 (le_cap c his).2

/-- The capacity at the last stage dominates the total number of directions. -/
lemma cap_le_of_le_cap {c : ℕ → ℕ} {s R : ℕ} (hs : s ≤ R) : cap c s ≤ cap c R := cap_le_cap c hs

/-- The **capped capacity** used by the accounting: the running maximum, capped at `ℓ`. -/
def capC (c : ℕ → ℕ) (ℓ s : ℕ) : ℕ := min ℓ (cap c s)

lemma capC_zero (c : ℕ → ℕ) (ℓ : ℕ) : capC c ℓ 0 = 0 := by simp [capC, cap_zero]

lemma capC_mono (c : ℕ → ℕ) (ℓ : ℕ) : Monotone (capC c ℓ) := by
  intro s t hst
  exact min_le_min_left _ (cap_le_cap c hst)

lemma capC_le (c : ℕ → ℕ) (ℓ s : ℕ) : capC c ℓ s ≤ ℓ := min_le_left _ _

/-- The increments of the capped capacity are at most the increments of the capacity. -/
lemma capC_sub_le (c : ℕ → ℕ) (ℓ s : ℕ) :
    capC c ℓ (s + 1) - capC c ℓ s ≤ cap c (s + 1) - cap c s := by
  have hAB : cap c s ≤ cap c (s + 1) := cap_mono c (Nat.le_succ s)
  by_cases hA : cap c s ≤ ℓ
  · have h1 : capC c ℓ s = cap c s := by simp [capC, min_eq_right hA]
    rw [h1]
    exact Nat.sub_le_sub_right (min_le_right _ _) _
  · have hℓA : ℓ < cap c s := lt_of_not_ge hA
    have hℓB : ℓ < cap c (s + 1) := lt_of_lt_of_le hℓA hAB
    have h1 : capC c ℓ s = ℓ := by simp [capC, min_eq_left hℓA.le]
    have h2 : capC c ℓ (s + 1) = ℓ := by simp [capC, min_eq_left hℓB.le]
    rw [h1, h2, Nat.sub_self]
    exact Nat.zero_le _

end Submission.Capacity

end
