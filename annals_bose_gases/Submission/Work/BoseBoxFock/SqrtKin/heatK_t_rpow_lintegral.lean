import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SqrtKin.heatK_rpow_integrableOn
import Submission.Work.BoseBoxFock.SqrtKin.heatK_rpow_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.heatK_t_rpow_lintegral`

The Lebesgue (`lintegral`) form of the radial `t`-integral of the heat kernel of `ℝ³`
against `t^{-3/2}`, with an extra nonnegative constant `c`:

`∫⁻_{t>0} t^{-3/2}·(heatK t z·c) = (2/π^{3/2})·‖z‖^{-4}·c`   (`z ≠ 0`, `c ≥ 0`).

This is the `ENNReal`-valued companion of the Bochner-integral evaluation
`heatK_rpow_integral` (in the sibling file `heatK_rpow_integral`), which gives

`∫_{t>0} t^{-3/2}·heatK t z = 2/(π^{3/2}‖z‖⁴)`   (`z ≠ 0`).

**Proof.** The integrand is pointwise nonnegative on `(0,∞)` (`c ≥ 0`, `heatK ≥ 0` there) and
integrable there (`heatK_rpow_integrableOn`, times the constant `c`), so
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` converts the `lintegral` of the
`ENNReal.ofReal` into `ENNReal.ofReal` of the Bochner integral. The latter is
`c · ∫_{t>0} t^{-3/2}·heatK t z` by `integral_const_mul`, and `heatK_rpow_integral` evaluates
it; the arithmetic `c·(2/(π^{3/2}‖z‖⁴)) = (2/π^{3/2})·(‖z‖^{-4}·c)`, using
`‖z‖^{-4} = (‖z‖⁴)^{-1}`, closes the identity.
-/

namespace Work.BoseBoxFock.SqrtKin

open MeasureTheory

theorem heatK_t_rpow_lintegral {z : EuclideanSpace ℝ (Fin 3)} (hz : z ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * (heatK t z * c)))
      = ENNReal.ofReal ((2 / Real.pi ^ ((3 : ℝ) / 2)) * (‖z‖ ^ (-(4 : ℝ)) * c)) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set f : ℝ → ℝ := fun t => t ^ (-(3 : ℝ) / 2) * (heatK t z * c) with hf
  -- integrability of the integrand on `(0, ∞)`
  have hfint : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    rw [hf]
    show Integrable (fun t : ℝ => t ^ (-(3 : ℝ) / 2) * (heatK t z * c))
      (volume.restrict (Set.Ioi (0 : ℝ)))
    simpa only [mul_assoc] using (heatK_rpow_integrableOn hz).mul_const c
  -- pointwise nonnegativity on `(0, ∞)`
  have hfnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f := by
    rw [hf]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (mul_nonneg (heatK_nonneg ht.le z) hc)
  -- evaluation of the Bochner integral
  have hval : ∫ t in Set.Ioi (0 : ℝ), f t
      = (2 / Real.pi ^ ((3 : ℝ) / 2)) * (‖z‖ ^ (-(4 : ℝ)) * c) := by
    rw [hf]
    have h1 : (fun t : ℝ => t ^ (-(3 : ℝ) / 2) * (heatK t z * c))
        = fun t : ℝ => c * (t ^ (-(3 : ℝ) / 2) * heatK t z) := by
      funext t; ring
    rw [h1, integral_const_mul, heatK_rpow_integral hz]
    have hneg : ‖z‖ ^ (-(4 : ℝ)) = (‖z‖ ^ 4)⁻¹ := by
      rw [show (-(4 : ℝ)) = -((4 : ℝ)) by ring, Real.rpow_neg hzpos.le]
      norm_num
    rw [hneg]
    field_simp
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfint hfnn, hval]

end Work.BoseBoxFock.SqrtKin
