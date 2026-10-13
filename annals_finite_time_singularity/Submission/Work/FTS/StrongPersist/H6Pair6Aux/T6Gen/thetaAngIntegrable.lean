import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.STDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

open scoped Real Topology
open MeasureTheory Set Filter

theorem thetaAngIntegrable (α : ℝ) (hα : α ∈ Set.Ioc 0 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f)
    (j : ℕ) (hj : j ≤ 5) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter j f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hαpos : 0 < α := hα.1
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- (1) the weighted mixed slot `(D_z^j D_θ f · W)²` is integrable on `Iθ`
  have hmix : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_mixedSummand α 6 hsm hmem 1 j le_rfl
      (by omega) hzI
  -- (2) divide by `(w z)² ≠ 0`; the weight identity is valid on all of `Iθ`
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  have hB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.mixed j 1 f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    (hmix.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr
      (MeasureTheory.ae_restrict_of_forall_mem hIθ (fun θ hθ => by
        beta_reduce
        have hsq := (Work.FTS.H2.Whz_Wm_sq α hαpos z θ hθ).2
        rw [Work.FTS.H2.Wm_eq] at hsq
        rw [mul_pow, hsq]
        rw [show (((Work.Spaces.w z) ^ 2)⁻¹) * ((Work.Spaces.mixed j 1 f z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
            = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
                * ((Work.Spaces.mixed j 1 f z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) from by ring,
          inv_mul_cancel₀ hw2, one_mul]))
  -- (3) on the interior, `sin(2θ) · ∂_θ(D_z^j f) = D_z^j D_θ f`
  refine hB.congr ?_
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  beta_reduce
  have hcomm := Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hsm j 1 hz hθ
  have hsin : Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.mixed j 1 f z θ := by
    have h := hcomm
    rw [show Work.Spaces.DthIter 1 (Work.Spaces.DzIter j f)
        = Work.Spaces.Dth (Work.Spaces.DzIter j f) from rfl] at h
    simpa only [Work.Spaces.Dth] using h
  rw [hsin]

end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
