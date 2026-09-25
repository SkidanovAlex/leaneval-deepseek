import Mathlib
import Submission.Work.BourgainPlan.Maximal.hlMaxTwoGrid
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

/-!
# The `ℓ²`-valued half-shifted dyadic maximal function: definitions

For a finite family `f : Fin n → ℝ → ℝ` put

`ell2MaxShift f x = Σ_t (dyMaxShift (1/2) (‖f t ·‖ₑ) x)²`,

the square of the `ℓ²`-valued maximal function built from the **half-shifted** (non-laminar)
dyadic grid `dyCellShift (1/2) n k = [(k+1/2)2^n, (k+3/2)2^n)` of `hlMaxTwoGrid.lean`.

This file only records the definition and its measurability (which holds for an *arbitrary* family
`f`, because the supremum defining `dyMaxShift` runs over the countable index set `ℤ × ℤ` of cells
and the cell integrals are constants).  The analysis lives in
`Submission/Work/BourgainPlan/Maximal/ell2MaxShiftStrongTwo.lean` (subadditivity and the
strong-`(2,2)` bound, uniform in the number of components) and
`Submission/Work/BourgainPlan/Maximal/ell2MaxShiftLpLtTwo.lean` (the Marcinkiewicz interpolation
between the weak-`(1,1)` bound `ell2MaxShiftWeakOne` and that strong-`(2,2)` bound, i.e. the
`1 < p < 2` half of the vector-valued maximal inequality for the shifted grid).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- **The half-shifted dyadic maximal function is measurable in `x`**, for an arbitrary (not
necessarily measurable) `φ`: the cells containing `x` give a countable family of indicator
functions of `x` times the (constant) cell integral. -/
theorem dyMaxShift_measurable (α : ℝ) (φ : ℝ → ℝ≥0∞) : Measurable (dyMaxShift α φ) := by
  have h : dyMaxShift α φ = fun x => ⨆ (p : ℤ × ℤ), (dyCellShift α p.1 p.2).indicator
      (fun _ => ENNReal.ofReal (((2 : ℝ) ^ p.1)⁻¹) * ∫⁻ y in dyCellShift α p.1 p.2, φ y) x := by
    funext x
    refine le_antisymm ?_ ?_
    · unfold dyMaxShift
      refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
      refine le_iSup_of_le (n, k) ?_
      rw [Set.indicator_of_mem hx]
    · refine iSup_le fun p => ?_
      by_cases hp : x ∈ dyCellShift α p.1 p.2
      · rw [Set.indicator_of_mem hp]
        unfold dyMaxShift
        exact le_iSup_of_le p.1 (le_iSup_of_le p.2 (le_iSup_of_le hp le_rfl))
      · rw [Set.indicator_of_notMem hp]; exact bot_le
  rw [h]
  exact Measurable.iSup fun p =>
    Measurable.indicator measurable_const (dyCellShift_measurable α p.1 p.2)

/-- `Σ_t (dyMaxShift (1/2) (‖f t ·‖ₑ) x)²`: the square of the `ℓ²`-norm of the componentwise
half-shifted dyadic maximal function of the family `f`. -/
noncomputable def ell2MaxShift {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)

lemma ell2MaxShift_measurable {n : ℕ} (f : Fin n → ℝ → ℝ) : Measurable (ell2MaxShift f) := by
  unfold ell2MaxShift
  refine Finset.measurable_sum _ fun t _ => ?_
  exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp
    (dyMaxShift_measurable (1 / 2) (fun y => ‖f t y‖ₑ))

end Work.BourgainPlan.Maximal
