import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-! ## The two elementary weight facts

`w` is the radial weight `(1+z)²/z²`; for `z > 0` it is `≥ 1` (indeed `w z = (1 + 1/z)²`),
so its square is `≥ 1` as well.  `thEta θ = sin(2θ)^{-η}` is `≥ 1` on the open angular
interval, because `sin(2θ) ∈ (0,1]` there and the exponent `-η` is negative. -/

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

theorem one_le_w_sq_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  nlinarith [one_le_w_of_pos hz]

theorem one_le_thEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos (z := -(Work.Spaces.eta)) hsin
    (Real.sin_le_one (2 * θ)) (by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- **The `D_z`-slice of a `SliceHonestOpen` datum is integrable on `Iθ`.**

`SliceHonestOpen G` gives, at every `z > 0`, the integrability of the weighted square
`(D_zG z θ)² (w z)² sin(2θ)^{-η}` on `Iθ`.  On the open interval both factors of the extra
weight are `≥ 1` (`w z ≥ 1` for `z > 0`, `sin(2θ)^{-η} ≥ 1` for `0 < θ < π/2`), so the
weighted square dominates the square `(D_zG z θ)²` there; and `|t| ≤ t² + 1`, so the slice
itself is dominated by `(D_zG z θ)² + 1 ≤ (D_zG z θ)² (w z)² sin(2θ)^{-η} + (w z)²
sin(2θ)^{-η}`, a sum of two integrable functions (the first is the hypothesis, the second is
a constant multiple of `thEta`, integrable on `Iθ`).  The endpoints `θ = 0, π/2` are null,
which is why the estimates are stated on `Ioo 0 (π/2)` and transported with
`volume.restrict Iθ = volume.restrict (Ioo 0 (π/2))`. -/
theorem dzSliceHonest (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    (hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) :
    ∀ w : ℝ, 0 < w → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.Dz G w θ)
      Work.Spaces.Iθ := by
  intro w hw
  have hIθrestrict : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  have hw2 : 1 ≤ (Work.Spaces.w w) ^ 2 := one_le_w_sq_of_pos hw
  have hIntF : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hhon.2.2 w hw
  have hIntG : MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta θ + (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hIθrestrict]
    exact hIntF.add (Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul _)
  show MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.Dz G w θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [hIθrestrict]
  refine MeasureTheory.Integrable.mono' hIntG ?_ ?_
  · have hcont : ContinuousOn (fun θ : ℝ => w * Work.Spaces.pz G w θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      continuousOn_const.mul ((hsm.pz.curry_θ hw).continuousOn)
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hσ1 : 1 ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta_of_mem_Ioo hθ
    have hMσ : 1 ≤ (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      nlinarith [hw2, hσ1]
    rw [Real.norm_eq_abs]
    have habs : |Work.Spaces.Dz G w θ| ≤ (Work.Spaces.Dz G w θ) ^ 2 + 1 := by
      have h := sq_nonneg (|Work.Spaces.Dz G w θ| - 1)
      have h2 : (|Work.Spaces.Dz G w θ|) ^ 2 = (Work.Spaces.Dz G w θ) ^ 2 := sq_abs _
      nlinarith [h, abs_nonneg (Work.Spaces.Dz G w θ), h2]
    have hquad : (Work.Spaces.Dz G w θ) ^ 2 ≤ (Work.Spaces.Dz G w θ) ^ 2
        * (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      have h1 := le_mul_of_one_le_right (sq_nonneg (Work.Spaces.Dz G w θ)) hw2
      have h1' : 0 ≤ (Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2 :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have h2' := le_mul_of_one_le_right h1' hσ1
      linarith
    linarith

end Work.FTS.EllSol.EllPkgAux.MollDom
