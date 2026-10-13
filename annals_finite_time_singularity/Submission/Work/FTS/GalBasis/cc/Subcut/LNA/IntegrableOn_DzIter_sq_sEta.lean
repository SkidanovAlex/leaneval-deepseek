import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut.LNA

theorem IntegrableOn_DzIter_sq_sEta {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) (hb4 : b ≤ 4)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  -- The `D_z`-summand of `HkIntegrand` is integrable on the angular slice
  -- (`Work.FTS.EllipticEst.integrableOn_zSummand`), and it differs from the target
  -- integrand by the *constant* factor `w z ^ 2 ≠ 0`.
  have hs := Work.FTS.EllipticEst.integrableOn_zSummand α 4 hsm hmem b hb4
    (Set.mem_Ici.mpr hz.le)
  have hwz : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  refine MeasureTheory.IntegrableOn.congr_fun (hs.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
  · -- the two integrands agree *everywhere* on `Iθ`
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    show (Work.Spaces.w z ^ 2)⁻¹ * (Work.Spaces.DzIter b f z θ *
        (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = Work.Spaces.DzIter b f z θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
    rw [show (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
        = Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) by
      rw [div_eq_mul_inv, ← Real.rpow_neg hs0]]
    have hsq : (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hs0]
      congr 1
      ring
    rw [mul_pow, mul_pow, hsq]
    rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
          ((Work.Spaces.DzIter b f z θ) ^ 2 *
            ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))))
        = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2) *
          ((Work.Spaces.DzIter b f z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) by ring,
      inv_mul_cancel₀ (pow_ne_zero 2 hwz), one_mul]
  · rw [Work.Spaces.Iθ]; exact measurableSet_Icc

end Work.FTS.GalBasis.cc.Subcut.LNA
