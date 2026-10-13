/-
  Work.WilE2 — Sard's theorem for `f : ℝⁿ → ℝ` (the target is one-dimensional, and the
  smoothness equals the dimension: the *sharp* borderline case of the Morse–Sard theorem).

  This module: VOCABULARY.

  For a function `f : ℝⁿ → ℝ` and `k : ℕ`, `flatSet f k` is the set of points at which all
  iterated (Fréchet) derivatives of `f` of orders `1, …, k` vanish.  These are the sets that
  appear in the stratification of the critical set in the proof of Sard's theorem
  (`Cr^k` in Sard, *The measure of the critical values of differentiable maps*, 1942):

  * `flatSet f 1` is exactly the critical set `{x | fderiv ℝ f x = 0}` (for the one-dimensional
    target);
  * on `flatSet f k` the function `f` is "flat of order `k+1`", which via a Rolle/mean-value
    argument (see `Submission.Work.WilE2.SardRolle`) gives the sharp estimate
    `‖f y - f x‖ ≤ ω ‖y - x‖ ^ (k+1)` used in the counting argument.
-/
import Mathlib

open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace Work.WilE2

/-- The set of points at which all iterated derivatives of `f` of orders `1, …, k` vanish. -/
def flatSet {n : ℕ} (f : (Fin n → ℝ) → ℝ) (k : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0}

@[simp] theorem mem_flatSet {n : ℕ} {f : (Fin n → ℝ) → ℝ} {k : ℕ} {x : Fin n → ℝ} :
    x ∈ flatSet f k ↔ ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0 := Iff.rfl

/-- A one-dimensional `ContinuousMultilinearMap` vanishes iff it vanishes on its single slot. -/
theorem iteratedFDeriv_one_eq_zero_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} :
    iteratedFDeriv ℝ 1 f x = 0 ↔ fderiv ℝ f x = 0 := by
  constructor
  · intro h
    ext v
    have h0 : (iteratedFDeriv ℝ 1 f x) (fun _ : Fin 1 => v) = 0 := by rw [h]; rfl
    rw [iteratedFDeriv_one_apply] at h0
    exact h0
  · intro h
    ext m
    rw [iteratedFDeriv_one_apply]
    simp [h]

/-- `flatSet f k` is antitone in `k`. -/
theorem flatSet_antitone {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Antitone (flatSet f) := by
  intro k l hkl x hx j hj1 hjk
  exact hx j hj1 (le_trans hjk hkl)

/-- The critical set of a real-valued function is the first flat set. -/
theorem flatSet_one_eq_critical {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    flatSet f 1 = {x | fderiv ℝ f x = 0} := by
  ext x
  simp only [mem_flatSet, Set.mem_setOf_eq]
  constructor
  · intro h
    have h1 : iteratedFDeriv ℝ 1 f x = 0 := h 1 le_rfl le_rfl
    rwa [iteratedFDeriv_one_eq_zero_iff] at h1
  · intro h j hj1 hjk
    have : j = 1 := le_antisymm hjk hj1
    subst this
    rwa [iteratedFDeriv_one_eq_zero_iff]

/-- The flat sets exhaust the critical set: every critical point belongs to some `flatSet f j`,
`j ≥ 1`. -/
theorem critical_subset_iUnion_flatSet {n : ℕ} (f : (Fin n → ℝ) → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    flatSet f 1 ⊆ (⋃ j ∈ Set.Icc 1 m, flatSet f j) := by
  intro x hx
  exact Set.mem_iUnion₂.mpr ⟨1, Set.mem_Icc.mpr ⟨le_rfl, hm⟩, hx⟩

end Work.WilE2
