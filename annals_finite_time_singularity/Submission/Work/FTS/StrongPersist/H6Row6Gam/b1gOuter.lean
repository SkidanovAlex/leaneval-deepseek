import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gInner
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
/-! ## Radial integrability of the slice integral -/

theorem b1gOuter : ∀ (α : ℝ) (A f : ℝ → ℝ → ℝ) (M : ℝ), α ∈ Set.Ioc 0 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.FTS.Nonlin.Xn α f ≤ M →
    MeasureTheory.Integrable
      (fun z => ∫ θ, |b1gF α A f (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  intro α A f M hα hA hf h6A h6f hXnM
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXnM
  have hMXint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply] using
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe α A hα0 hα1 hA h6A).1
  have hQint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply] using
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe α f hα0 hα1 hf h6f).1
  have hMajAbs_int : MeasureTheory.Integrable (fun z => Real.sqrt 3 * M
      * (((Work.Spaces.w z) ^ 2 * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2
            * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hMXint.add hQint).div_const 2).const_mul _
  have hcontF : ContinuousOn (fun p : ℝ × ℝ => b1gF α A f p) Work.FTS.EllipticEst.Q0 := by
    simp only [b1gF_apply]
    exact (((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.contOn_leafGam α).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
        (hA.mixed 5 0))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hf.mixed 1 1))).mul
      (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hf.mixed 5 1))
  have hIaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |b1gF α A f p|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontF.abs
  refine MeasureTheory.Integrable.mono' hMajAbs_int hIaesm.integral_prod_right' ?_
  filter_upwards [b1gInner α A f M hα hA hf h6A h6f hXnM] with z hz
  have hA_nn : 0 ≤ ∫ θ, |b1gF α A f (z, θ)|
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integral_nonneg (fun θ => abs_nonneg _)
  rw [Real.norm_of_nonneg hA_nn]
  refine le_trans hz ?_
  have hAMall : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z))
      * (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))
      ≤ ((Work.Spaces.w z) ^ 2 * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2
            * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z) / 2 := by
    have hMXnn : 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
      rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX_apply]
      refine add_nonneg (mul_nonneg (by positivity)
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
        (mul_nonneg (div_nonneg (by norm_num) (by
            rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.hgam_const]; linarith))
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc
            (fun θ hθ => mul_nonneg
              (Real.rpow_nonneg
                (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _)
              (sq_nonneg _))))
    have hQznn : 0 ≤ Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z := by
      rw [Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz_apply]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg
          (Real.rpow_nonneg
            (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.sin_two_nonneg_of_Iθ' hθ) _)
          (sq_nonneg _))
    have ha : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)) ^ 2
        = (Work.Spaces.w z) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z := by
      rw [mul_pow, Real.sq_sqrt hMXnn]
    have hb : (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z)) ^ 2
        = (Work.Spaces.w z) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z := by
      rw [mul_pow, Real.sq_sqrt hQznn]
    nlinarith [sq_nonneg (Work.Spaces.w z
        * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveMX α A z)
      - Work.Spaces.w z * Real.sqrt (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.b1fiveQz α f z))]
  exact mul_le_mul_of_nonneg_left hAMall (mul_nonneg (Real.sqrt_nonneg 3) hMnn)
end

end Work.FTS.StrongPersist.H6Row6
