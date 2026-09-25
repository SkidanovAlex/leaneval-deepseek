import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2MaxShiftDefs
import Submission.Work.BourgainPlan.Maximal.ell2Max_rpow_half_add_le

/-!
# Subadditivity of the `ℓ²`-valued half-shifted dyadic maximal function

For a finite family `f : Fin n → ℝ → ℝ` we have defined

`ell2MaxShift f x = Σ_t (dyMaxShift (1/2) (‖f t ·‖ₑ) x)²`

in `Submission/Work/BourgainPlan/Maximal/ell2MaxShiftDefs.lean`. The present file proves that its
square root is *subadditive*:

`(ell2MaxShift (f + g) x) ^ (1/2) ≤ (ell2MaxShift f x) ^ (1/2) + (ell2MaxShift g x) ^ (1/2)`.

This is the exact analogue, for the **half-shifted** (non-laminar) dyadic grid `dyCellShift (1/2)`,
of `ell2Max_rpow_half_add_le`. Nothing in the argument uses laminarity, so the same two ingredients
suffice:

* **Subadditivity of the shifted scalar dyadic maximal function**, `dyMaxShift_add_le`:
  `dyMaxShift α (φ + ψ) x ≤ dyMaxShift α φ x + dyMaxShift α ψ x`, immediate from additivity of the
  Lebesgue integral on the shifted cells and `sup (a_i + b_i) ≤ sup a_i + sup b_i`;
* **Minkowski's inequality in `ℝ≥0∞` for finite sums**, `ENNReal_sum_sq_rpow_half_add_le`
  (imported from `ell2Max_rpow_half_add_le`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- **Monotonicity of the shifted dyadic maximal function** in the input. -/
lemma dyMaxShift_mono (α : ℝ) {φ ψ : ℝ → ℝ≥0∞} (h : φ ≤ ψ) (x : ℝ) :
    dyMaxShift α φ x ≤ dyMaxShift α ψ x := by
  unfold dyMaxShift
  refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
  refine le_trans (mul_le_mul_right ?_ _)
    (le_iSup_of_le n (le_iSup_of_le k (le_iSup_of_le hx le_rfl)))
  exact lintegral_mono h

/-- **Subadditivity of the shifted scalar dyadic maximal function.**
`dyMaxShift α (φ + ψ) ≤ dyMaxShift α φ + dyMaxShift α ψ` pointwise. Only measurability of `φ` is
needed: when both are measurable this is additivity of the integral, and otherwise one can always
turn the integral of a sum into a sum of integrals using *one* measurable summand. -/
lemma dyMaxShift_add_le (α : ℝ) {φ ψ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (_hψ : Measurable ψ)
    (x : ℝ) : dyMaxShift α (φ + ψ) x ≤ dyMaxShift α φ x + dyMaxShift α ψ x := by
  unfold dyMaxShift
  refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
  have hInt : ∫⁻ y in dyCellShift α n k, (φ + ψ) y
      = (∫⁻ y in dyCellShift α n k, φ y) + ∫⁻ y in dyCellShift α n k, ψ y := by
    simp only [Pi.add_apply]
    rw [lintegral_add_left hφ]
  rw [hInt, mul_add]
  exact add_le_add (le_iSup_of_le n (le_iSup_of_le k (le_iSup_of_le hx le_rfl)))
    (le_iSup_of_le n (le_iSup_of_le k (le_iSup_of_le hx le_rfl)))

/-- Subadditivity of the `ℓ²`-valued half-shifted dyadic maximal function: the square root of
`ell2MaxShift` is subadditive over finite families (the `ℓ²` triangle inequality in `ℝ≥0∞`,
together with subadditivity of the shifted scalar dyadic maximal function). -/
theorem ell2MaxShift_rpow_half_add_le {n : ℕ} (f g : Fin n → ℝ → ℝ)
    (hf : ∀ t, Measurable (f t)) (hg : ∀ t, Measurable (g t)) (x : ℝ) :
    (Work.BourgainPlan.Maximal.ell2MaxShift (f + g) x) ^ ((1 : ℝ) / 2)
      ≤ (Work.BourgainPlan.Maximal.ell2MaxShift f x) ^ ((1 : ℝ) / 2)
        + (Work.BourgainPlan.Maximal.ell2MaxShift g x) ^ ((1 : ℝ) / 2) := by
  -- Pointwise (in the component `t`) subadditivity of `dyMaxShift`, using
  -- `‖f t y + g t y‖ₑ ≤ ‖f t y‖ₑ + ‖g t y‖ₑ`.
  have hcomp : ∀ t : Fin n,
      dyMaxShift (1 / 2) (fun y => ‖(f + g) t y‖ₑ) x
        ≤ dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x
          + dyMaxShift (1 / 2) (fun y => ‖g t y‖ₑ) x := by
    intro t
    refine le_trans (dyMaxShift_mono (1 / 2) ?_ x)
      (dyMaxShift_add_le (1 / 2) ((hf t).enorm) ((hg t).enorm) x)
    intro y
    simp only [Pi.add_apply]
    exact enorm_add_le _ _
  -- Square both sides and sum over the components.
  have hstep : ell2MaxShift (f + g) x
      ≤ ∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x
          + dyMaxShift (1 / 2) (fun y => ‖g t y‖ₑ) x) ^ (2:ℝ) := by
    unfold ell2MaxShift
    exact Finset.sum_le_sum fun t _ => ENNReal.rpow_le_rpow (hcomp t) (by norm_num)
  -- Take square roots and apply Minkowski.
  refine le_trans (ENNReal.rpow_le_rpow hstep (by norm_num)) ?_
  simpa only [ell2MaxShift] using
    ENNReal_sum_sq_rpow_half_add_le
      (fun t : Fin n => dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x)
      (fun t : Fin n => dyMaxShift (1 / 2) (fun y => ‖g t y‖ₑ) x)

end Work.BourgainPlan.Maximal
