import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.coulDualFubini
import Submission.Work.BoseBoxFock.L1Tails.coulKinTailNeg
import Submission.Work.BoseBoxFock.L1Tails.coulMomentumLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.coulombDual` — the `H^{-1}`–`H¹` duality of the Coulomb energy

For an `L¹` weight `W ≥ 0` a.e. with finite Coulomb energy and a complex-valued test function
`ψ ∈ C_c^∞(ℝ³)`,

`‖∫_x W(x)ψ(x) dx‖² ≤ (4π)^{-1} (∬ W(x)W(y)/‖x−y‖ dx dy) · ∑_j ∫_x ‖∂_jψ(x)‖²`,

i.e. `W` acts on `H¹` through `‖W‖_{Ḣ^{-1}}` only.  With the `p`-convention Fourier transform
`kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy` the proof is the three-brick chain

* the dual pairing identity `∫_x Wψ = (2π)^{-3}∫_p Ŵ(p)ψ̂(−p)dp` (`coulDualFubini`);
* the momentum-space Coulomb bound `(2π)^{-3}∫_p ‖Ŵ(p)‖²/‖p‖² dp ≤ (4π)^{-1}∬W(x)W(y)/‖x−y‖`
  (`coulMomentumLe`, whose proof is the subordination identity for `1/‖x‖`);
* the weighted Plancherel identity `(2π)^{-3}∫_p ‖p‖²‖ψ̂(−p)‖²dp = ∑_j ∫_x ‖∂_jψ(x)‖²`
  (`coulKinTailNeg`);

together with Cauchy–Schwarz in `p` with the symmetric weights `‖p‖^{∓1}`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Real ENNReal

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

theorem coulombDual {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hW0 : ∀ᵐ x, 0 ≤ W x)
    (hJ : MeasureTheory.Integrable (Work.BoseBoxFock.coulInt W)) {ψ : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ‖∫ x, ((W x : ℝ) : ℂ) * ψ x‖ ^ 2
      ≤ (4 * Real.pi)⁻¹ * (∫ p, Work.BoseBoxFock.coulInt W p)
          * ∑ j : Fin 3, ∫ x, ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  set Wc : E3 → ℂ := fun x => ((W x : ℝ) : ℂ) with hWc
  set U : E3 → ℂ := fun p => Submission.BoseGases.kinFT Wc p with hU
  set Z : E3 → ℂ := fun p => Submission.BoseGases.kinFT ψ (-p) with hZ
  set A : ℂ := ∫ p, U p * Z p with hA
  set J : ℝ := ∫ q, Work.BoseBoxFock.coulInt W q with hJdef
  set K : ℝ := ∑ j : Fin 3, ∫ x, ‖fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
    with hKdef
  have h2p : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2p3 : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
  have h2piC : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
    have hsq : ‖((2 * Real.pi : ℝ) : ℂ)‖ ^ 2 = (2 * Real.pi) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    nlinarith [norm_nonneg (((2 * Real.pi : ℝ) : ℂ)), h2p]
  -- (0) positivity of `J` and `K`
  have hJnn : 0 ≤ J := by
    have hrew : (∫ q : E3 × E3, Work.BoseBoxFock.coulInt W q)
        = ∫ q : E3 × E3, W q.1 * W q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹ := rfl
    have hprod : (∫ q : E3 × E3, W q.1 * W q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹)
        = ∫ x : E3, ∫ y : E3, W x * W y * (‖x - y‖ : ℝ)⁻¹ :=
      MeasureTheory.integral_prod
        (fun q : E3 × E3 => W q.1 * W q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹) hJ
    rw [hJdef, hrew, hprod]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hW0] with x hx
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hW0] with y hy
    exact mul_nonneg (mul_nonneg hx hy) (inv_nonneg.mpr (norm_nonneg _))
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => by positivity))
  -- (1) the Fubini identity and its integrability
  have hfub := coulDualFubini (W := W) hWi hψ hψc
  have hIntProd : MeasureTheory.Integrable (fun p : E3 => U p * Z p) := by
    simpa only [hWc, hU, hZ] using hfub.1
  have hFubEq : (∫ x, Wc x * ψ x) = ((2 * (Real.pi : ℂ)) ^ 3)⁻¹ * A := by
    simpa only [hWc, hU, hZ, hA] using hfub.2
  have hnormA : ‖∫ x, Wc x * ψ x‖ = ((2 * Real.pi) ^ 3)⁻¹ * ‖A‖ := by
    have hcast : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [hFubEq, hcast, norm_mul, norm_inv, norm_pow, h2piC]
  -- (2) integrability of the two weighted squares
  have hCoul := coulMomentumLe (W := W) hWi hW0 hJ
  have hCoul' : (∫⁻ p, ENNReal.ofReal (‖U p‖ ^ 2 / ‖p‖ ^ 2))
      ≤ ENNReal.ofReal (((2 * Real.pi) ^ 3 * (4 * Real.pi)⁻¹) * J) := by
    simpa only [hWc, hU, hJdef] using hCoul
  have hWc_int : MeasureTheory.Integrable Wc volume := by
    rw [hWc]
    exact hWi.ofReal
  have hUcont : Continuous U := by
    rw [hU]
    exact Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hWc_int
  have hInt1 : MeasureTheory.Integrable (fun p : E3 => ‖U p‖ ^ 2 / ‖p‖ ^ 2) := by
    have hnn : 0 ≤ᵐ[volume] (fun p : E3 => ‖U p‖ ^ 2 / ‖p‖ ^ 2) :=
      Filter.Eventually.of_forall (fun p => by positivity)
    have hfin : HasFiniteIntegral (fun p : E3 => ‖U p‖ ^ 2 / ‖p‖ ^ 2) volume :=
      (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mpr
        (lt_of_le_of_lt hCoul' ENNReal.ofReal_lt_top)
    have hmeas : AEStronglyMeasurable (fun p : E3 => ‖U p‖ ^ 2 / ‖p‖ ^ 2) volume :=
      AEMeasurable.aestronglyMeasurable
        ((hUcont.measurable.norm.pow_const 2).div (measurable_norm.pow_const 2)).aemeasurable
    exact ⟨hmeas, hfin⟩
  have hInt2 : MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * ‖Z p‖ ^ 2) := by
    simpa only [hZ] using (coulKinTailNeg hψ hψc).1
  have hKinId : (∫⁻ p, ENNReal.ofReal (‖p‖ ^ 2 * ‖Z p‖ ^ 2))
      = ENNReal.ofReal (((2 * Real.pi) ^ 3) * K) := by
    simpa only [hZ, hKdef] using (coulKinTailNeg hψ hψc).2
  -- (3) the real-valued bounds
  have hbound1 : (∫ p, ‖U p‖ ^ 2 / ‖p‖ ^ 2) ≤ ((2 * Real.pi) ^ 3 * (4 * Real.pi)⁻¹) * J := by
    have hnn : 0 ≤ᵐ[volume] (fun p : E3 => ‖U p‖ ^ 2 / ‖p‖ ^ 2) :=
      Filter.Eventually.of_forall (fun p => by positivity)
    have h1 : ENNReal.ofReal (∫ p, ‖U p‖ ^ 2 / ‖p‖ ^ 2)
        = ∫⁻ p, ENNReal.ofReal (‖U p‖ ^ 2 / ‖p‖ ^ 2) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt1 hnn
    rw [← h1] at hCoul'
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hJnn)).mp hCoul'
  have hbound2 : (∫ p, ‖p‖ ^ 2 * ‖Z p‖ ^ 2) = ((2 * Real.pi) ^ 3) * K := by
    have hnn : 0 ≤ᵐ[volume] (fun p : E3 => ‖p‖ ^ 2 * ‖Z p‖ ^ 2) :=
      Filter.Eventually.of_forall (fun p => by positivity)
    have h1 : ENNReal.ofReal (∫ p, ‖p‖ ^ 2 * ‖Z p‖ ^ 2)
        = ∫⁻ p, ENNReal.ofReal (‖p‖ ^ 2 * ‖Z p‖ ^ 2) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2 hnn
    refine (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun p => by positivity))
      (mul_nonneg (by positivity) hKnn)).mp ?_
    rw [h1, hKinId]
  -- (4) Cauchy--Schwarz in `p`
  have hIntNorm : MeasureTheory.Integrable (fun p : E3 => ‖U p‖ * ‖Z p‖) :=
    hIntProd.norm.congr (Filter.Eventually.of_forall (fun p => by simp only [norm_mul]))
  have hA_le : ‖A‖ ≤ ∫ p, ‖U p‖ * ‖Z p‖ := by
    rw [hA]
    calc ‖∫ p, U p * Z p‖ ≤ ∫ p, ‖U p * Z p‖ := norm_integral_le_integral_norm _
      _ = ∫ p, ‖U p‖ * ‖Z p‖ := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
          simp only [norm_mul]
  have hψ_int : MeasureTheory.Integrable ψ volume :=
    hψ.continuous.integrable_of_hasCompactSupport hψc
  have hZae : AEMeasurable Z volume := by
    rw [hZ]
    exact ((Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hψ_int).comp
      continuous_neg).aemeasurable
  have hconj : (2 : ℝ).HolderConjugate (2 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hf_ae : AEStronglyMeasurable (fun p : E3 => ‖U p‖ / ‖p‖) volume :=
    ((hUcont.measurable.norm.div measurable_norm)).aemeasurable.aestronglyMeasurable
  have hmemf : MemLp (fun p : E3 => ‖U p‖ / ‖p‖) 2 volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (f := fun p : E3 => ‖U p‖ / ‖p‖) hf_ae).mpr (by
        refine hInt1.congr (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Real.norm_of_nonneg (show (0 : ℝ) ≤ ‖U p‖ / ‖p‖ by positivity), div_pow])
  have hg_ae : AEStronglyMeasurable (fun p : E3 => ‖p‖ * ‖Z p‖) volume :=
    ((measurable_norm.aemeasurable).mul hZae.norm).aestronglyMeasurable
  have hmemg : MemLp (fun p : E3 => ‖p‖ * ‖Z p‖) 2 volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (f := fun p : E3 => ‖p‖ * ‖Z p‖) hg_ae).mpr (by
        refine hInt2.congr (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Real.norm_of_nonneg (show (0 : ℝ) ≤ ‖p‖ * ‖Z p‖ by positivity), mul_pow])
  have hOF : (ENNReal.ofReal (2 : ℝ)) = (2 : ℝ≥0∞) := by norm_num
  have hCS := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := volume)
    (p := 2) (q := 2) (f := fun p : E3 => ‖U p‖ / ‖p‖) (g := fun p : E3 => ‖p‖ * ‖Z p‖)
    hconj (by simpa only [hOF] using hmemf) (by simpa only [hOF] using hmemg)
  have hCS' : (∫ p, ‖U p‖ * ‖Z p‖)
      ≤ Real.sqrt (∫ p, ‖U p‖ ^ 2 / ‖p‖ ^ 2) * Real.sqrt (∫ p, ‖p‖ ^ 2 * ‖Z p‖ ^ 2) := by
    have hL : (∫ p : E3, ‖(fun p : E3 => ‖U p‖ / ‖p‖) p‖
          * ‖(fun p : E3 => ‖p‖ * ‖Z p‖) p‖)
        = ∫ p : E3, ‖U p‖ * ‖Z p‖ := by
      refine integral_congr_ae ?_
      filter_upwards [show ∀ᵐ p : E3, p ≠ 0 from by
        rw [MeasureTheory.ae_iff]
        rw [show {p : E3 | ¬ p ≠ 0} = {0} by ext p; simp]
        exact measure_singleton 0] with p hp
      simp only [Real.norm_of_nonneg (show (0 : ℝ) ≤ ‖U p‖ / ‖p‖ by positivity),
        Real.norm_of_nonneg (show (0 : ℝ) ≤ ‖p‖ * ‖Z p‖ by positivity)]
      have hp' : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
      field_simp
    have hR1 : (∫ p : E3, ‖(fun p : E3 => ‖U p‖ / ‖p‖) p‖ ^ (2 : ℝ))
        = ∫ p : E3, ‖U p‖ ^ 2 / ‖p‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Real.norm_of_nonneg (show (0 : ℝ) ≤ ‖U p‖ / ‖p‖ by positivity),
        Real.rpow_two, div_pow]
    have hR2 : (∫ p : E3, ‖(fun p : E3 => ‖p‖ * ‖Z p‖) p‖ ^ (2 : ℝ))
        = ∫ p : E3, ‖p‖ ^ 2 * ‖Z p‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Real.norm_of_nonneg (show (0 : ℝ) ≤ ‖p‖ * ‖Z p‖ by positivity),
        Real.rpow_two, mul_pow]
    rw [hL, hR1, hR2] at hCS
    simpa only [← Real.sqrt_eq_rpow] using hCS
  -- (5) assemble
  have hA_bound : ‖A‖ ≤ Real.sqrt (((2 * Real.pi) ^ 3 * (4 * Real.pi)⁻¹) * J)
      * Real.sqrt (((2 * Real.pi) ^ 3) * K) :=
    le_trans hA_le (le_trans hCS' (mul_le_mul (Real.sqrt_le_sqrt hbound1)
      (Real.sqrt_le_sqrt (le_of_eq hbound2)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have hconst : Real.sqrt (((2 * Real.pi) ^ 3 * (4 * Real.pi)⁻¹) * J)
      * Real.sqrt (((2 * Real.pi) ^ 3) * K)
      = (2 * Real.pi) ^ 3 * Real.sqrt ((4 * Real.pi)⁻¹ * J * K) := by
    rw [← Real.sqrt_mul (mul_nonneg (by positivity) hJnn)]
    congr 1
    rw [show (((2 * Real.pi) ^ 3 * (4 * Real.pi)⁻¹) * J) * (((2 * Real.pi) ^ 3) * K)
        = ((2 * Real.pi) ^ 3) ^ 2 * ((4 * Real.pi)⁻¹ * J * K) by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3) ^ 2),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hmain : ‖∫ x, Wc x * ψ x‖ ≤ Real.sqrt ((4 * Real.pi)⁻¹ * J * K) := by
    rw [hnormA]
    have h := mul_le_mul_of_nonneg_left (hconst ▸ hA_bound)
      (by positivity : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹)
    have hcancel : ((2 * Real.pi) ^ 3)⁻¹
          * ((2 * Real.pi) ^ 3 * Real.sqrt ((4 * Real.pi)⁻¹ * J * K))
        = Real.sqrt ((4 * Real.pi)⁻¹ * J * K) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h2p3), one_mul]
    rwa [hcancel] at h
  have hYnn : 0 ≤ (4 * Real.pi)⁻¹ * J * K :=
    mul_nonneg (mul_nonneg (by positivity) hJnn) hKnn
  have hgoal : ‖∫ x, Wc x * ψ x‖ ^ 2 ≤ (4 * Real.pi)⁻¹ * J * K :=
    calc ‖∫ x, Wc x * ψ x‖ ^ 2
        ≤ (Real.sqrt ((4 * Real.pi)⁻¹ * J * K)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hmain 2
      _ = (4 * Real.pi)⁻¹ * J * K := Real.sq_sqrt hYnn
  simpa only [hWc, hJdef, hKdef] using hgoal

end Work.BoseBoxFock.L1Tails
