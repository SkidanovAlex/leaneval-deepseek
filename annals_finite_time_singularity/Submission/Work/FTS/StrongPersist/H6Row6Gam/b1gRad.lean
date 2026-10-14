import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveArith =====
section

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
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000 in
/-- Slice integrability of the crux integrand `|F|` in the angular variable. -/
theorem b1fiveSliceInt : ∀ (α : ℝ) (A f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f →
    ∀ z : ℝ, 0 < z →
      MeasureTheory.Integrable (fun θ => |b1fiveF α A f (z, θ)|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro α A f hα0 hα1 hA hf h6A h6f z hz
  have hVint := integrableOn_gamMixed_slice (b := 0) (a := 1) hα0 hf h6f
    le_rfl (by norm_num) hz
  have hZint := integrableOn_gamMixed_slice (b := 5) (a := 1) hα0 hf h6f
    le_rfl (by norm_num) hz
  have hg : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
      * Real.sqrt (b1fiveMX α A z)
      * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 0 1 f z θ) ^ 2
          + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((hVint.add hZint)).div_const 2).const_mul _
  refine MeasureTheory.Integrable.mono' hg ?_ ?_
  · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => |b1fiveF α A f p|) ?_ hz
    simp only [b1fiveF_apply]
    exact ((((contOn_leafGam α).mul (smoothOpen_continuousOn (hA.mixed 5 0))).mul
      (smoothOpen_continuousOn (hf.mixed 0 1))).mul
      (smoothOpen_continuousOn (hf.mixed 5 1))).abs
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _
    have hcoefnn : ∀ z : ℝ, 0 ≤ b1fiveMX α A z := by
      intro z
      rw [b1fiveMX_apply]
      refine add_nonneg (mul_nonneg (by positivity)
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
        (mul_nonneg (div_nonneg (by norm_num) (by
            rw [hgam_const]; linarith))
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc
            (fun θ hθ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _)
              (sq_nonneg _))))
    have hX2 : |Work.Spaces.DzIter 5 A z θ| ≤ Real.sqrt (b1fiveMX α A z) := by
      rw [← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt ?_
      rw [b1fiveMX_apply]
      exact xSliceAgmon5 α A hα0 hα1 hA h6A z θ hz hθ0 hθ1
    have habsF : |b1fiveF α A f (z, θ)| = (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) := by
      simp only [b1fiveF_apply, Work.FTS.TransportS.leafGam, Work.Spaces.mixed_zero_right]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
      ring
    rw [Real.norm_of_nonneg (abs_nonneg _), habsF]
    have hAM : |Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|
        ≤ ((Work.Spaces.mixed 0 1 f z θ) ^ 2 + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|Work.Spaces.mixed 0 1 f z θ| - |Work.Spaces.mixed 5 1 f z θ|),
        sq_abs (Work.Spaces.mixed 0 1 f z θ), sq_abs (Work.Spaces.mixed 5 1 f z θ)]
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.DzIter 5 A z θ|
            * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Real.sqrt (b1fiveMX α A z)
            * (((Work.Spaces.mixed 0 1 f z θ) ^ 2 + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) hσnn)
            exact mul_le_mul hX2 hAM (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (Real.sqrt_nonneg _)
      _ = (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z)
          * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 0 1 f z θ) ^ 2
            + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2) := by
            ring

set_option maxHeartbeats 1600000 in
/-- The pointwise-in-`z` bound on the angular integral of the crux integrand. -/
theorem b1fiveInner : ∀ (α : ℝ) (A f : ℝ → ℝ → ℝ) (M : ℝ), α ∈ Set.Ioc 0 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.FTS.Nonlin.Xn α f ≤ M →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, |b1fiveF α A f (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ Real.sqrt 2 * M * ((Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
            * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))) := by
  intro α A f M hα hA hf h6A h6f hXnM
  obtain ⟨hα0, hα1⟩ := hα
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXnM
  have h4f : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf 4 (by norm_num) h6f
  have hgam1 : Work.Spaces.gam α - 1 = α / 10 := hgam_const
  have hgam_pos : 0 < Work.Spaces.gam α - 1 := by rw [hgam1]; linarith
  have hMXnn : ∀ z : ℝ, 0 ≤ b1fiveMX α A z := by
    intro z
    rw [b1fiveMX_apply]
    refine add_nonneg (mul_nonneg (by positivity)
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
      (mul_nonneg (div_nonneg (by norm_num) hgam_pos.le)
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))))
  have hQznn : ∀ z : ℝ, 0 ≤ b1fiveQz α f z := by
    intro z
    rw [b1fiveQz_apply]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))
  have hXpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter 5 A z θ) ^ 2 ≤ b1fiveMX α A z := by
    intro z θ hz hθ0 hθ1
    rw [b1fiveMX_apply]
    exact xSliceAgmon5 α A hα0 hα1 hA h6A z θ hz hθ0 hθ1
  have hPz_le : ∀ z : ℝ, 0 < z → b1fivePz α f z ≤ 2 * M ^ 2 := by
    intro z hz
    have h1 : b1fivePz α f z ≤ 2 * Work.Spaces.HkSq α 4 f := by
      rw [b1fivePz_apply]
      exact vSliceSupLe α f hα0 hα1 hf h4f z hz
    have h2 : Work.Spaces.HkSq α 4 f = (Work.Spaces.HkNorm α 4 f) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    have h3 : (Work.Spaces.HkNorm α 4 f) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 f) hXnM 2
    linarith [h1, h2.le, h2.ge, h3]
  have hCSθ : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|))
        ≤ Real.sqrt (b1fivePz α f z) * Real.sqrt (b1fiveQz α f z) := by
    intro z hz
    have h := gamSliceCS α f hα0 hα1 hf h6f z hz
    simpa only [mul_assoc, b1fivePz_apply, b1fiveQz_apply] using h
  have hAMall : ∀ z : ℝ,
      (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))
      ≤ ((Work.Spaces.w z) ^ 2 * b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2 * b1fiveQz α f z) / 2 := by
    intro z
    have ha : (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2
        = (Work.Spaces.w z) ^ 2 * b1fiveMX α A z := by
      rw [mul_pow, Real.sq_sqrt (hMXnn z)]
    have hb : (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2
        = (Work.Spaces.w z) ^ 2 * b1fiveQz α f z := by
      rw [mul_pow, Real.sq_sqrt (hQznn z)]
    nlinarith [sq_nonneg (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)
      - Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))]
  have hIz : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hIz]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |b1fiveF α A f (z, θ)| ≤ (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)) := by
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _
    have hX2 : |Work.Spaces.DzIter 5 A z θ| ≤ Real.sqrt (b1fiveMX α A z) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hXpt z θ hz hθ0 hθ1)
    have habsF : |b1fiveF α A f (z, θ)| = (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) := by
      simp only [b1fiveF_apply, Work.FTS.TransportS.leafGam, Work.Spaces.mixed_zero_right]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
      ring
    rw [habsF]
    have h1 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter 5 A z θ|
          * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * Real.sqrt (b1fiveMX α A z)
          * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) := by
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      exact mul_le_mul_of_nonneg_left hX2 (mul_nonneg (sq_nonneg _) hσnn)
    refine h1.trans_eq ?_
    ring
  have hInt_eq : (∫ θ, (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|))
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z)
        * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.integral_const_mul _ _
  have hVint := integrableOn_gamMixed_slice (b := 0) (a := 1) hα0 hf h6f
    le_rfl (by norm_num) hz
  have hZint := integrableOn_gamMixed_slice (b := 5) (a := 1) hα0 hf h6f
    le_rfl (by norm_num) hz
  have hmaj : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
        * Real.sqrt (b1fiveMX α A z)
        * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 0 1 f z θ) ^ 2
            + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((hVint.add hZint)).div_const 2).const_mul ((Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z))
  have hint1 : MeasureTheory.Integrable (fun θ => (Work.Spaces.w z) ^ 2
        * Real.sqrt (b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed 0 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2|))
        (contOn_sig_abs hf) hz).const_mul ((Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z))
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
      have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
      have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _
      have hc : 0 ≤ (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z) :=
        mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg hc
        (mul_nonneg hσnn (mul_nonneg (abs_nonneg _) (abs_nonneg _))))]
      have habs : |Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|
          ≤ ((Work.Spaces.mixed 0 1 f z θ) ^ 2 + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by
        nlinarith [sq_nonneg (|Work.Spaces.mixed 0 1 f z θ| - |Work.Spaces.mixed 5 1 f z θ|),
          sq_abs (Work.Spaces.mixed 0 1 f z θ), sq_abs (Work.Spaces.mixed 5 1 f z θ)]
      have hAM2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
          ≤ ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 0 1 f z θ) ^ 2
              + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by
        have h := mul_le_mul_of_nonneg_left habs hσnn
        calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
            ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (((Work.Spaces.mixed 0 1 f z θ) ^ 2
                  + (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2) := h
          _ = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 0 1 f z θ) ^ 2
                + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 5 1 f z θ) ^ 2) / 2 := by ring
      exact mul_le_mul_of_nonneg_left hAM2 hc
  calc (∫ θ, |b1fiveF α A f (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ ∫ θ, (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_mono_ae (b1fiveSliceInt α A f hα0 hα1 hA hf h6A h6f z hz) hint1 hpt
    _ = (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z)
        * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hInt_eq
    _ ≤ (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z)
        * (Real.sqrt (b1fivePz α f z) * Real.sqrt (b1fiveQz α f z)) :=
        mul_le_mul_of_nonneg_left (hCSθ z hz) (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    _ ≤ Real.sqrt 2 * M
        * ((Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
          * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))) := by
        have h2 : Real.sqrt (b1fivePz α f z) ≤ Real.sqrt 2 * M := by
          calc Real.sqrt (b1fivePz α f z) ≤ Real.sqrt (2 * M ^ 2) :=
                Real.sqrt_le_sqrt (hPz_le z hz)
            _ = Real.sqrt 2 * M := by
                rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs,
                  abs_of_nonneg hMnn]
        have h3 : 0 ≤ (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z) :=
          mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
        calc (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z)
              * (Real.sqrt (b1fivePz α f z) * Real.sqrt (b1fiveQz α f z))
            ≤ (Work.Spaces.w z) ^ 2 * Real.sqrt (b1fiveMX α A z)
              * ((Real.sqrt 2 * M) * Real.sqrt (b1fiveQz α f z)) := by
              refine mul_le_mul_of_nonneg_left ?_ h3
              exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
          _ = Real.sqrt 2 * M
              * ((Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
                * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))) := by
              ring

set_option maxHeartbeats 1600000 in
/-- Radial integrability of `z ↦ ∫_θ |F|`. -/
theorem b1fiveOuter : ∀ (α : ℝ) (A f : ℝ → ℝ → ℝ) (M : ℝ), α ∈ Set.Ioc 0 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.FTS.Nonlin.Xn α f ≤ M →
    MeasureTheory.Integrable
      (fun z => ∫ θ, |b1fiveF α A f (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  intro α A f M hα hA hf h6A h6f hXnM
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXnM
  have h4f : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf 4 (by norm_num) h6f
  have hMXint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveMX_apply] using (xProdIntLe α A hα0 hα1 hA h6A).1
  have hQint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 * b1fiveQz α f z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveQz_apply] using (zProdIntLe α f hα0 hα1 hf h6f).1
  have hMajAbs_int : MeasureTheory.Integrable (fun z => Real.sqrt 2 * M
      * (((Work.Spaces.w z) ^ 2 * b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2 * b1fiveQz α f z) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hMXint.add hQint).div_const 2).const_mul _
  have hcontF : ContinuousOn (fun p : ℝ × ℝ => b1fiveF α A f p) Work.FTS.EllipticEst.Q0 := by
    simp only [b1fiveF_apply]
    exact (((contOn_leafGam α).mul (smoothOpen_continuousOn (hA.mixed 5 0))).mul
      (smoothOpen_continuousOn (hf.mixed 0 1))).mul
      (smoothOpen_continuousOn (hf.mixed 5 1))
  have hIaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |b1fiveF α A f p|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontF.abs
  refine MeasureTheory.Integrable.mono' hMajAbs_int hIaesm.integral_prod_right' ?_
  filter_upwards [b1fiveInner α A f M hα hA hf h6A h6f hXnM] with z hz
  have hA_nn : 0 ≤ ∫ θ, |b1fiveF α A f (z, θ)|
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integral_nonneg (fun θ => abs_nonneg _)
  rw [Real.norm_of_nonneg hA_nn]
  refine le_trans hz ?_
  have hAMall : (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))
      ≤ ((Work.Spaces.w z) ^ 2 * b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2 * b1fiveQz α f z) / 2 := by
    have hMXnn : 0 ≤ b1fiveMX α A z := by
      rw [b1fiveMX_apply]
      refine add_nonneg (mul_nonneg (by positivity)
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
        (mul_nonneg (div_nonneg (by norm_num) (by rw [hgam_const]; linarith))
          (MeasureTheory.setIntegral_nonneg measurableSet_Icc
            (fun θ hθ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _)
              (sq_nonneg _))))
    have hQznn : 0 ≤ b1fiveQz α f z := by
      rw [b1fiveQz_apply]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))
    have ha : (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2
        = (Work.Spaces.w z) ^ 2 * b1fiveMX α A z := by
      rw [mul_pow, Real.sq_sqrt hMXnn]
    have hb : (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2
        = (Work.Spaces.w z) ^ 2 * b1fiveQz α f z := by
      rw [mul_pow, Real.sq_sqrt hQznn]
    nlinarith [sq_nonneg (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)
      - Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))]
  exact mul_le_mul_of_nonneg_left hAMall (mul_nonneg (Real.sqrt_nonneg 2) hMnn)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6Gam.b1gRad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-- `b1fiveMX` is nonnegative (for `α > 0`). -/
theorem b1gMXnn (α : ℝ) (A : ℝ → ℝ → ℝ) (hα0 : 0 < α) (z : ℝ) :
    0 ≤ b1fiveMX α A z := by
  rw [b1fiveMX_apply]
  refine add_nonneg (mul_nonneg (by positivity)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
    (mul_nonneg (div_nonneg (by norm_num) (by
        rw [hgam_const]; linarith))
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg
          (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))))

/-- `b1fiveQz` is nonnegative. -/
theorem b1gQznn (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ b1fiveQz α f z := by
  rw [b1fiveQz_apply]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))

/-- The AM–GM inequality for the product of the two square roots. -/
theorem b1gAMall (α : ℝ) (A f : ℝ → ℝ → ℝ) (hα0 : 0 < α) (z : ℝ) :
    (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))
      ≤ ((Work.Spaces.w z) ^ 2 * b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2 * b1fiveQz α f z) / 2 := by
  have ha : (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2
      = (Work.Spaces.w z) ^ 2 * b1fiveMX α A z := by
    rw [mul_pow, Real.sq_sqrt (b1gMXnn α A hα0 z)]
  have hb : (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2
      = (Work.Spaces.w z) ^ 2 * b1fiveQz α f z := by
    rw [mul_pow, Real.sq_sqrt (b1gQznn α f z)]
  nlinarith [sq_nonneg (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)
    - Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))]

/-- The radial weight is a.e. strongly measurable; `√MX` inherits a.e. strong measurability from
the two slice integrals defining `MX`. -/
theorem b1gMXaesm (α : ℝ) (A : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen A) :
    MeasureTheory.AEStronglyMeasurable (fun z => Real.sqrt (b1fiveMX α A z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ, (Work.Spaces.DzIter 5 A z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    aesm_sliceIntegral ((smoothOpen_continuousOn (hsm.DzIter 5)).pow 2)
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 5 1 A z θ) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    aesm_sliceIntegral (contOn_sig_mixed hsm (le_refl 1))
  have h3 : MeasureTheory.AEStronglyMeasurable (b1fiveMX α A)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [show b1fiveMX α A
        = fun z => (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1)) * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2) from by
      funext z; rw [b1fiveMX_apply]]
    exact (h1.const_mul (4 / Real.pi)).add (h2.const_mul (200 / (Work.Spaces.gam α - 1)))
  exact Real.continuous_sqrt.comp_aestronglyMeasurable h3

/-- A.e. strong measurability of `√Qz`. -/
theorem b1gQzaesm (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun z => Real.sqrt (b1fiveQz α f z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 5 1 f z θ) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    aesm_sliceIntegral (contOn_sig_mixed hsm (le_refl 1))
  have h3 : MeasureTheory.AEStronglyMeasurable (b1fiveQz α f)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [show b1fiveQz α f
        = fun z => ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 f z θ) ^ 2 from by
      funext z; rw [b1fiveQz_apply]]
    exact h2
  exact Real.continuous_sqrt.comp_aestronglyMeasurable h3

/-- **Radial integrability of the AM–GM majorant.** -/
theorem b1gMajInt (α : ℝ) (A f : ℝ → ℝ → ℝ) (M : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h6A : Work.Spaces.HkMem α 6 A) (h6f : Work.Spaces.HkMem α 6 f) (hMnn : 0 ≤ M) :
    MeasureTheory.Integrable (fun z => Real.sqrt 3 * M
      * ((Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z))))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hwnn : ∀ z : ℝ, 0 ≤ Work.Spaces.w z := Work.FTS.TransportS.SlotT2.supOpen_w_nonneg
  have hMXint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveMX_apply] using (xProdIntLe α A hα0 hα1 hA h6A).1
  have hQint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * b1fiveQz α f z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveQz_apply] using (zProdIntLe α f hα0 hα1 hf h6f).1
  have hMajAbs_int : MeasureTheory.Integrable (fun z => Real.sqrt 3 * M
      * (((Work.Spaces.w z) ^ 2 * b1fiveMX α A z
          + (Work.Spaces.w z) ^ 2 * b1fiveQz α f z) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hMXint.add hQint).div_const 2).const_mul _
  refine MeasureTheory.Integrable.mono' hMajAbs_int ?_ ?_
  · exact ((aesm_w.mul (b1gMXaesm α A hA)).mul
      (aesm_w.mul (b1gQzaesm α f hf))).const_mul _
  · filter_upwards with z
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 3) hMnn)
      (mul_nonneg (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))
        (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))))]
    exact mul_le_mul_of_nonneg_left (b1gAMall α A f hα0 z)
      (mul_nonneg (Real.sqrt_nonneg 3) hMnn)

/-- **The radial Cauchy–Schwarz** for the pair `(w√MX, w√Qz)`. -/
theorem b1gRadCS (α : ℝ) (A f : ℝ → ℝ → ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h6A : Work.Spaces.HkMem α 6 A) (h6f : Work.Spaces.HkMem α 6 f) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
        * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveQz α f z) := by
  have hwnn : ∀ z : ℝ, 0 ≤ Work.Spaces.w z := Work.FTS.TransportS.SlotT2.supOpen_w_nonneg
  have hMXint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * b1fiveMX α A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveMX_apply] using (xProdIntLe α A hα0 hα1 hA h6A).1
  have hQint : MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * b1fiveQz α f z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [b1fiveQz_apply] using (zProdIntLe α f hα0 hα1 hf h6f).1
  have h := Work.FTS.StrongPersist.H6Pair6Aux.cs_sqrt_le_fts (s := Work.Spaces.Iz)
    (A := fun z => (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2)
    (B := fun z => (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2)
    (hMXint.congr (Filter.Eventually.of_forall (fun z => by
      show (Work.Spaces.w z) ^ 2 * b1fiveMX α A z
        = (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2
      rw [mul_pow, Real.sq_sqrt (b1gMXnn α A hα0 z)])))
    (hQint.congr (Filter.Eventually.of_forall (fun z => by
      show (Work.Spaces.w z) ^ 2 * b1fiveQz α f z
        = (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2
      rw [mul_pow, Real.sq_sqrt (b1gQznn α f z)])))
    (fun z => sq_nonneg _) (fun z => sq_nonneg _)
  rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveMX α A z from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      simp only [mul_pow, Real.sq_sqrt (b1gMXnn α A hα0 z)])),
    show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * b1fiveQz α f z from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      simp only [mul_pow, Real.sq_sqrt (b1gQznn α f z)]))] at h
  have heqint : (∫ z in Work.Spaces.Iz,
        Real.sqrt ((Work.Spaces.w z * Real.sqrt (b1fiveMX α A z)) ^ 2)
        * Real.sqrt ((Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) ^ 2))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (b1fiveMX α A z))
        * (Work.Spaces.w z * Real.sqrt (b1fiveQz α f z)) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      simp only [Real.sqrt_sq_eq_abs,
        abs_of_nonneg (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))]))
  rwa [heqint] at h

end

end Work.FTS.StrongPersist.H6Row6
end
