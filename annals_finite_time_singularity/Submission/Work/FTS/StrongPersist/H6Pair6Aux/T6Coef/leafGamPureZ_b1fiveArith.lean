/-
# `T6Coef/leafGamPureZ_b1fiveArith` — the numerical bookkeeping of the `b₁ = 5` crux case

Bound on the `z`-side functional of the crux case: from the two supplied integral bounds
`∫ w² MX ≤ 2002 α^{-3} K6²` and `∫ w² Qz ≤ HkNorm α 6 f ²` (the children `xProdIntLe`,
`zProdIntLe`) we conclude
`√2 · M · √(∫ w²MX) · √(∫ w²Qz) ≤ C α^{-3} [(1+K0+K4)(1+HkSq α 6 f) + (K4+K6)(1+M)(1+HkNorm α 6 f)]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000 in
/-- The numerical bound of the crux case. -/
theorem b1fiveArith : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 K6 M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Real.sqrt 2 * M
          * (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
            * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveQz α f z))
        ≤ C * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  refine ⟨100, by norm_num, ?_⟩
  intro α hα A f K0 K4 K6 M hCoef hDat
  obtain ⟨hα0, hα1⟩ := hα
  have hgam1 : Work.Spaces.gam α - 1 = α / 10 := hgam_const
  have hgam_pos : 0 < Work.Spaces.gam α - 1 := by rw [hgam1]; linarith
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hCoef.n6
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hCoef.n4
  have hK0nn : 0 ≤ K0 := by
    have h := hCoef.val 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    exact le_trans (abs_nonneg _) h
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hDat.bdd
  have hN6f_nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hSq6A : Work.Spaces.HkSq α 6 A = (Work.Spaces.HkNorm α 6 A) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 A)]
  have hSq6f : Work.Spaces.HkSq α 6 f = (Work.Spaces.HkNorm α 6 f) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
  have hK6sq : Work.Spaces.HkSq α 6 A ≤ K6 ^ 2 := by
    rw [hSq6A]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 A) hCoef.n6 2
  have hAval : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
      ≤ 2002 * α ^ (-(3 : ℝ)) * K6 ^ 2 := by
    have h0 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 6 A := by
      simpa only [b1fiveMX] using (xProdIntLe α A hα0 hα1 hCoef.sm hCoef.h6).2
    have hcoef : 4 / Real.pi + 200 / (Work.Spaces.gam α - 1) ≤ 2002 * α ^ (-(3 : ℝ)) := by
      have hgam : 200 / (Work.Spaces.gam α - 1) = 2000 / α := by rw [hgam1]; ring
      have h6 : 4 / Real.pi ≤ 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi)]
        have := Real.pi_gt_three
        linarith
      have h3 : 1 ≤ α ^ (-(3 : ℝ)) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(3 : ℝ) ≤ 0 by norm_num)
        rwa [Real.rpow_zero] at h
      have h3' : α⁻¹ ≤ α ^ (-(3 : ℝ)) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(3 : ℝ) ≤ -(1 : ℝ) by norm_num)
        rwa [Real.rpow_neg hα0.le, Real.rpow_one] at h
      have h4 : 2000 / α ≤ 2000 * α ^ (-(3 : ℝ)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left h3' (by norm_num)
      have h5 : (2 : ℝ) ≤ 2 * α ^ (-(3 : ℝ)) := by linarith
      rw [hgam]
      linarith
    calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 6 A := h0
      _ ≤ (2002 * α ^ (-(3 : ℝ))) * K6 ^ 2 :=
          mul_le_mul hcoef hK6sq (Work.Spaces.HkSq_nonneg α 6 A) (by positivity)
      _ = 2002 * α ^ (-(3 : ℝ)) * K6 ^ 2 := by ring
  have hBval : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveQz α f z)
      ≤ (Work.Spaces.HkNorm α 6 f) ^ 2 := by
    simpa only [b1fiveQz, hSq6f] using (zProdIntLe α f hα0 hα1 hDat.sm hDat.h6).2
  have h1 : Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
      ≤ 45 * α ^ (-(3 : ℝ)) * K6 := by
    have hsq : Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
        ≤ Real.sqrt (2002 * α ^ (-(3 : ℝ)) * K6 ^ 2) := Real.sqrt_le_sqrt hAval
    have h2002 : Real.sqrt 2002 ≤ 45 := by
      rw [Real.sqrt_le_iff]; constructor <;> norm_num
    have hα' : Real.sqrt (α ^ (-(3 : ℝ))) ≤ α ^ (-(3 : ℝ)) := by
      rw [Real.sqrt_le_iff]
      refine ⟨Real.rpow_nonneg hα0.le _, ?_⟩
      have h3 : 1 ≤ α ^ (-(3 : ℝ)) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(3 : ℝ) ≤ 0 by norm_num)
        rwa [Real.rpow_zero] at h
      nlinarith [Real.rpow_nonneg hα0.le (-(3 : ℝ)), h3]
    calc Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
        ≤ Real.sqrt 2002 * Real.sqrt (α ^ (-(3 : ℝ))) * K6 := by
          refine le_trans hsq ?_
          rw [show 2002 * α ^ (-(3 : ℝ)) * K6 ^ 2 = 2002 * (α ^ (-(3 : ℝ)) * K6 ^ 2) by ring]
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2002)]
          rw [Real.sqrt_mul (Real.rpow_nonneg hα0.le _)]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hK6nn, mul_assoc]
      _ ≤ 45 * α ^ (-(3 : ℝ)) * K6 :=
          mul_le_mul_of_nonneg_right (mul_le_mul h2002 hα' (Real.sqrt_nonneg _) (by norm_num)) hK6nn
  have h2 : Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveQz α f z)
      ≤ Work.Spaces.HkNorm α 6 f := by
    calc Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveQz α f z)
        ≤ Real.sqrt ((Work.Spaces.HkNorm α 6 f) ^ 2) := Real.sqrt_le_sqrt hBval
      _ = Work.Spaces.HkNorm α 6 f := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hN6f_nn]
  have hsq2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hMKH : M * (K6 * Work.Spaces.HkNorm α 6 f)
      ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
    have h1 : M ≤ 1 + M := by linarith
    have h2 : K6 ≤ K4 + K6 := by linarith
    have h3 : Work.Spaces.HkNorm α 6 f ≤ 1 + Work.Spaces.HkNorm α 6 f := by linarith
    calc M * (K6 * Work.Spaces.HkNorm α 6 f)
        ≤ M * ((K4 + K6) * (1 + Work.Spaces.HkNorm α 6 f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 hN6f_nn (by linarith)) hMnn
      _ ≤ (1 + M) * ((K4 + K6) * (1 + Work.Spaces.HkNorm α 6 f)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by ring
  have hbr2 : (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)
      ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
    have h1 : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_nonneg (by linarith) (by linarith [Work.Spaces.HkSq_nonneg α 6 f])
    linarith
  calc Real.sqrt 2 * M
        * (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
          * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveQz α f z))
      ≤ Real.sqrt 2 * M * ((45 * α ^ (-(3 : ℝ)) * K6) * Work.Spaces.HkNorm α 6 f) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.sqrt_nonneg 2) hMnn)
        exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = (Real.sqrt 2 * (45 * α ^ (-(3 : ℝ)))) * (M * (K6 * Work.Spaces.HkNorm α 6 f)) := by ring
    _ ≤ (2 * (45 * α ^ (-(3 : ℝ)))) * ((K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
        refine mul_le_mul ?_ hMKH (mul_nonneg hMnn (mul_nonneg hK6nn hN6f_nn))
          (by positivity)
        exact mul_le_mul_of_nonneg_right hsq2 (by positivity)
    _ = 90 * α ^ (-(3 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by ring
    _ ≤ 100 * α ^ (-(3 : ℝ)) * ((K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
        mul_le_mul_of_nonneg_right (by
          have h3 := Real.rpow_nonneg hα0.le (-(3 : ℝ))
          linarith : 90 * α ^ (-(3 : ℝ)) ≤ 100 * α ^ (-(3 : ℝ)))
          (by positivity)
    _ ≤ 100 * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
          + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
        mul_le_mul_of_nonneg_left hbr2 (by positivity)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
