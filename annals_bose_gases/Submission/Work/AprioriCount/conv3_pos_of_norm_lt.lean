import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.KernelFibreBound
import Submission.LocPotential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Positivity of the cubic self-convolution `χ ⋆ χ` on the unit ball

`χ = chiBase / √chiNormSq` where `chiBase = chiBump` is the cubic `ContDiffBump`
supported in the closed ball of radius `1/2` (`chiBump.rOut = 1/2`).  Hence
`χ > 0` on the open ball of radius `1/2` and `χ = 0` outside the closed ball.

For `‖w‖ < 1` the two balls `B(0,1/2)` and `B(w,1/2)` overlap: the midpoint
`w/2` lies strictly inside both.  So the integrand
`y ↦ χ y · χ (w − y)` of `conv3 χ χ w = ∫ y, χ y · χ (w − y)` is continuous,
compactly supported, nonnegative, and strictly positive at `y = w/2`; by
`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` the integral is
strictly positive.
-/

namespace Work.AprioriCount

open MeasureTheory

/-- The cubic localisation function `χ` is strictly positive strictly inside
the open ball of radius `1/2` (the support radius `chiBump.rOut` of the
underlying `ContDiffBump`). -/
lemma chi_pos_of_norm_lt {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < 1 / 2) :
    0 < Submission.BoseGases.chi x := by
  have hmem : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3))
      Submission.BoseGases.chiBump.rOut := by
    rw [Metric.mem_ball]
    simpa [Submission.BoseGases.chiBump, dist_eq_norm] using hx
  have hnum : 0 < Submission.BoseGases.chiBase x :=
    Submission.BoseGases.chiBump.pos_of_mem_ball hmem
  have hden : 0 < Real.sqrt Submission.BoseGases.chiNormSq :=
    Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos
  simpa [Submission.BoseGases.chi] using div_pos hnum hden

theorem conv3_pos_of_norm_lt {w : EuclideanSpace ℝ (Fin 3)} (hw : ‖w‖ < 1) :
    0 < Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi w := by
  -- the integrand of the self-convolution, as a function of the integration variable
  let f : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun y => Submission.BoseGases.chi y * Submission.BoseGases.chi (w - y)
  have hcont : Continuous f := by
    have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chi (w - y)) :=
      Submission.BoseGases.chi_continuous.comp (continuous_const.sub continuous_id)
    exact Submission.BoseGases.chi_continuous.mul h1
  have hcs : HasCompactSupport f := Submission.BoseGases.chi_hasCompactSupport.mul_right
  have hnn : 0 ≤ f := fun y =>
    mul_nonneg (Submission.BoseGases.chi_nonneg y) (Submission.BoseGases.chi_nonneg _)
  -- the midpoint `w/2` lies strictly inside both balls `B(0,1/2)` and `B(w,1/2)`
  have hnorm : ‖(2 : ℝ)⁻¹ • w‖ < 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
    linarith
  have hw2 : w - (2 : ℝ)⁻¹ • w = (2 : ℝ)⁻¹ • w := by
    nth_rewrite 1 [← one_smul ℝ w]
    rw [← sub_smul]
    norm_num
  have hx : f ((2 : ℝ)⁻¹ • w) ≠ 0 := by
    have hp1 : 0 < Submission.BoseGases.chi ((2 : ℝ)⁻¹ • w) := chi_pos_of_norm_lt hnorm
    have hp2 : 0 < Submission.BoseGases.chi (w - (2 : ℝ)⁻¹ • w) := by
      rw [hw2]; exact chi_pos_of_norm_lt hnorm
    exact mul_ne_zero (ne_of_gt hp1) (ne_of_gt hp2)
  have hthis : 0 < ∫ y : EuclideanSpace ℝ (Fin 3), f y ∂volume :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn hx
  simpa [Submission.BoseGases.conv3, f] using hthis

end Work.AprioriCount
