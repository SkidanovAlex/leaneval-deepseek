import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.bt_integral_weight_id

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- **The bound for the `f`-part of the bad term.**

For `f ∈ ℋ⁴` which vanishes on the two angular boundaries `θ = 0`, `θ = π/2`, the
`D_z³`-derivative of `f` at a point `(z,θ)` of the domain is controlled by the full
weighted `L²`-norm of `D_z³ D_θ f`:

`(D_z³ f z θ)² (w z)² ≤ 100/(γ-1) ∫_{Iθ} (D_z³ D_θ f z s · W(z,s))² ds`.

This is the one-dimensional angular Hardy inequality `HardyTheta` applied to the
function `θ ↦ D_z³ f z θ`, multiplied by the radial weight `(w z)²`: the two vanish at
`θ = 0` because `f` does, the Cauchy–Schwarz step produces the singular angular weight
`sin(2θ)^{2-γ}`, and the identity `bt_mixed_weight_id` converts
`(∂_θ D_z³ f)² (w z)² sin(2θ)^{2-γ}` back into the squared weighted mixed derivative
`(D_z³ D_θ f · W)²`. -/
theorem bt_f_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) (hvt : Work.Spaces.VanishTheta f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DzIter 3 f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 100 / (Work.Spaces.gam α - 1)
            * MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
                (fun s => (Work.Spaces.mixed 3 1 f z s * Work.Spaces.Wt α z s) ^ 2) := by
  intro z hz θ hθ
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  by_cases hz0 : z = 0
  · -- At `z = 0` the radial weight `w` vanishes (totalised division), so both sides are `≥ 0`.
    subst hz0
    have hzero : (Work.Spaces.DzIter 3 f 0 θ) ^ 2 * (Work.Spaces.w 0) ^ 2 = 0 := by
      simp [Work.Spaces.w]
    rw [hzero]
    exact mul_nonneg (le_of_lt (div_pos (by norm_num) hγ))
      (MeasureTheory.integral_nonneg fun s => sq_nonneg _)
  · -- At `z > 0` the radial weight is nonzero and the angular Hardy inequality applies.
    have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hwne : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hzpos))
    -- The squared weighted mixed derivative is integrable on `Iθ`, being an `H⁴`-summand.
    have hG : MeasureTheory.Integrable
        (fun s => (Work.Spaces.mixed 3 1 f z s * Work.Spaces.Wt α z s) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.mixed_sq_integrableOn hsm hmem 1 3 (by norm_num) (by norm_num) hz
    -- Hence `(∂_θ D_z³ f)² sin(2θ)^{2-γ}` is integrable, as required by `HardyTheta`.
    have hF : MeasureTheory.IntegrableOn
        (fun s => (Work.Spaces.pth (Work.Spaces.DzIter 3 f) z s) ^ 2
          * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      have h1 : MeasureTheory.Integrable
          (fun s => (Work.Spaces.w z ^ 2)⁻¹
            * (Work.Spaces.mixed 3 1 f z s * Work.Spaces.Wt α z s) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hG.const_mul _
      refine h1.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with s hs
      have h := Work.Spaces.bt_mixed_weight_id hsm α z s hα hα1 hz hs
      rw [← h]
      rw [show (Work.Spaces.pth (Work.Spaces.DzIter 3 f) z s) ^ 2 * Work.Spaces.w z ^ 2
            * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α)
          = Work.Spaces.w z ^ 2
            * ((Work.Spaces.pth (Work.Spaces.DzIter 3 f) z s) ^ 2
              * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α)) from by ring]
      rw [inv_mul_cancel_left₀ (pow_ne_zero 2 hwne)]
    -- The angular Hardy inequality for `θ ↦ D_z³ f z θ`, which vanishes at `θ = 0`.
    have hHardy := Work.Spaces.HardyTheta α hα hα1 (Work.Spaces.DzIter 3 f) z
      (Work.Spaces.SmoothNbhd.DzIter hsm 3) hz
      ((Work.Spaces.bt_DzIter_vanish hvt 3).1 z) hF θ hθ
    have step : (Work.Spaces.DzIter 3 f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (100 / (Work.Spaces.gam α - 1)
            * ∫ s in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter 3 f) z s) ^ 2
                * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right hHardy (sq_nonneg _)
    refine le_trans step (le_of_eq ?_)
    rw [mul_assoc, Work.Spaces.bt_integral_weight_id α hα hα1 f hsm hz]

end Work.Spaces
