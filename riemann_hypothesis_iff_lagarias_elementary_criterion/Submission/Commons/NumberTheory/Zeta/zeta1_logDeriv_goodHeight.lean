import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_local_approx_ne
import Submission.Commons.NumberTheory.Zeta.zeta_ball3_divisor_le_log
import Submission.Commons.NumberTheory.Zeta.riemannZeta1_ball_divisor_le_log
import Submission.Commons.NumberTheory.Zeta.completedRiemannZeta_zero_re_eq_half
import Submission.Commons.Algebra.BigOperators.norm_finsum_le_of_norm_le

open Complex Filter Metric Set
open scoped Real Topology BigOperators

noncomputable section

set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Zeta

theorem zeta1_logDeriv_goodHeight (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ T δ : ℝ, 5 ≤ T → 0 < δ → 1 ≤ (Real.log (T + 3) + 1) * δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T|) →
      ∀ σ : ℝ, (1/2 : ℝ) ≤ σ → σ ≤ (5/8 : ℝ) →
        ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤
          C * (Real.log (T + 3) + 1) ^ 3 := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := zeta_logDeriv_local_approx_ne
  obtain ⟨K, hKpos, hK⟩ := riemannZeta1_ball_divisor_le_log
  refine ⟨C₁ + 2 * K + 1, by linarith, ?_⟩
  intro T δ hT hδ0 hδprod hgood σ hσlo hσhi
  -- basic set-up
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs
  set c : ℂ := (2 : ℂ) + Complex.I * (T : ℂ) with hc
  set d : ℂ → ℤ := fun u => MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c ((13 : ℝ) / 8)) u with hd
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor completedRiemannZeta (Metric.closedBall c (3 : ℝ)) u with hD
  set S : ℂ := ∑ᶠ u : ℂ,
    (((D u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (s - u)⁻¹ else 0)) with hS
  have hTabs : 5 ≤ |T| := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)]; exact hT
  have hTpos : 0 < T := by linarith
  have hs_im : s.im = T := by rw [hs]; simp
  have hs_re : s.re = σ := by rw [hs]; simp
  -- ζ₁ is nonzero at s, because s itself would be a zero too close to the height T
  have hs_ne : riemannZeta₁ s ≠ 0 := by
    intro h0
    have h1 := hgood s h0
    rw [hs_im] at h1
    simp at h1
    linarith
  -- the local approximation of the logarithmic derivative
  have hloc : ‖logDeriv riemannZeta₁ s - S‖ ≤ C₁ * (Real.log (T + 3) + 1) ^ 3 := by
    have h0 := hC₁ T hTabs σ (by linarith) hσhi (by simpa [hs] using hs_ne)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)] at h0
    simpa [hs, hc, hd, hD, hS] using h0
  -- analyticity of ζ₁ on the ball of radius 13/8
  have hζ1an : AnalyticOnNhd ℂ riemannZeta₁ (Metric.closedBall c ((13 : ℝ) / 8)) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hdnn : ∀ u : ℂ, (0 : ℤ) ≤ d u := by
    intro u
    have hh := MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := riemannZeta₁) hζ1an
    simpa [hd] using hh u
  have hd_fin : Function.HasFiniteSupport d := by
    have hsupp := (MeromorphicOn.divisor riemannZeta₁
      (Metric.closedBall c ((13 : ℝ) / 8))).finiteSupport (isCompact_closedBall c ((13 : ℝ) / 8))
    simpa [Function.HasFiniteSupport, hd] using hsupp
  -- pointwise bound for the summand
  have hbound : ∀ u : ℂ,
      ‖((D u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (s - u)⁻¹ else 0)‖ ≤ (d u : ℝ) / δ := by
    intro u
    have hdu0 : (0 : ℝ) ≤ (d u : ℝ) := Int.cast_nonneg (hdnn u)
    by_cases h1 : ‖s - u‖ ≤ (1 / 8 : ℝ)
    · rw [if_pos h1]
      -- u lies in the ball of radius 13/8 around c
      have hu_mem : u ∈ Metric.closedBall c ((13 : ℝ) / 8) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hsc : ‖s - c‖ = 2 - σ := by
          have h1' : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
          rw [h1', Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          ring
        have h2 : ‖u - c‖ ≤ ‖u - s‖ + ‖s - c‖ := by
          calc ‖u - c‖ = ‖(u - s) + (s - c)‖ := by congr 1; ring
            _ ≤ ‖u - s‖ + ‖s - c‖ := norm_add_le _ _
        rw [norm_sub_rev u s] at h2
        linarith [h2, h1, hsc, hσlo]
      -- identify the divisors
      have hDd : D u = d u := by
        have hR2 : (13 : ℝ) / 4 / 2 = 13 / 8 := by norm_num
        have huR : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (T : ℂ)) ((13 : ℝ) / 4 / 2) := by
          simpa [hR2, hc] using hu_mem
        have h := divisor_riemannZeta1_eq_completedRiemannZeta_ball (t := T) (R := (13 : ℝ) / 4)
            hTabs (by norm_num) (by norm_num) (u := u) huR
        rw [hR2] at h
        simpa [hd, hD, hc] using h.symm
      rw [hDd]
      by_cases hdu : d u = 0
      · rw [hdu]; simp
      · have hdu' : 0 < d u := lt_of_le_of_ne (hdnn u) (Ne.symm hdu)
        -- ζ₁ vanishes at u, so u is far from the height T
        have hz : riemannZeta₁ u = 0 := by
          by_contra hz0
          have hord : analyticOrderAt riemannZeta₁ u = 0 :=
            ((differentiable_riemannZeta₁.analyticAt u).analyticOrderAt_eq_zero).mpr hz0
          have hzero : d u = 0 := by
            have hh : MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c ((13 : ℝ) / 8)) u = 0 := by
              rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζ1an hu_mem, hord]
              simp
            simpa [hd] using hh
          exact hdu hzero
        have hfar : δ ≤ |u.im - T| := hgood u hz
        have hdist : δ ≤ ‖s - u‖ := by
          have him : (s - u).im = T - u.im := by rw [Complex.sub_im, hs_im]
          calc δ ≤ |u.im - T| := hfar
            _ = |T - u.im| := by rw [abs_sub_comm]
            _ = |(s - u).im| := by rw [him]
            _ ≤ ‖s - u‖ := Complex.abs_im_le_norm _
        have hinv : ‖s - u‖⁻¹ ≤ δ⁻¹ := by
          have hpos : 0 < ‖s - u‖ := lt_of_lt_of_le hδ0 hdist
          exact (inv_le_inv₀ hpos hδ0).mpr hdist
        calc ‖((d u : ℤ) : ℂ) * (s - u)⁻¹‖
            = (d u : ℝ) * ‖s - u‖⁻¹ := by
              rw [norm_mul, norm_inv, Complex.norm_intCast, abs_of_nonneg hdu0]
          _ ≤ (d u : ℝ) * δ⁻¹ := mul_le_mul_of_nonneg_left hinv hdu0
          _ = (d u : ℝ) / δ := by rw [div_eq_mul_inv]
    · rw [if_neg h1]
      simp only [mul_zero, norm_zero]
      exact div_nonneg hdu0 (le_of_lt hδ0)
  -- the divisor bound
  have hdivsum : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) ≤ K * (Real.log (T + 6) + 1) := by
    have hKb := hK T hTabs ((13 : ℝ) / 4) (by norm_num) (by norm_num)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)] at hKb
    have hR2 : (13 : ℝ) / 4 / 2 = 13 / 8 := by norm_num
    rw [hR2] at hKb
    simpa [hd, hc] using hKb
  -- bound ‖S‖
  have hS_bound : ‖S‖ ≤ (1 / δ) * (K * (Real.log (T + 6) + 1)) := by
    have hgfin : Function.HasFiniteSupport (fun u : ℂ => (d u : ℝ) / δ) := by
      refine hd_fin.subset ?_
      rw [Function.support_subset_iff]
      intro u hu
      rw [Function.mem_support]
      intro hu0
      exact hu (by rw [hu0]; simp)
    have hbn := Commons.Algebra.BigOperators.norm_finsum_le_of_norm_le
      (f := fun u : ℂ => ((D u : ℤ) : ℂ) * (if ‖s - u‖ ≤ (1 / 8 : ℝ) then (s - u)⁻¹ else 0))
      (g := fun u : ℂ => (d u : ℝ) / δ) hgfin hbound
    rw [hS]
    refine le_trans hbn ?_
    have hsum_eq : (∑ᶠ u : ℂ, (d u : ℝ) / δ) = (1 / δ) * ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) := by
      rw [mul_finsum]
      apply finsum_congr
      intro u
      rw [div_eq_mul_inv, one_div]
      ring
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_left hdivsum (le_of_lt (one_div_pos.mpr hδ0))
  -- arithmetic
  let L : ℝ := Real.log (T + 3) + 1
  have hL1 : (1 : ℝ) ≤ L := by
    dsimp [L]
    have hlog : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hinvδ : 1 / δ ≤ L := by
    rw [div_le_iff₀ hδ0]
    exact hδprod
  have hlogT6 : Real.log (T + 6) + 1 ≤ 2 * L := by
    have hle : T + 6 ≤ (T + 3) ^ 2 := by nlinarith
    have hmono : Real.log (T + 6) ≤ Real.log ((T + 3) ^ 2) :=
      Real.log_le_log (by linarith) hle
    rw [Real.log_pow] at hmono
    push_cast at hmono
    dsimp [L]
    linarith
  have hSb : ‖S‖ ≤ 2 * K * L ^ 3 := by
    have hstep : (1 / δ) * (K * (Real.log (T + 6) + 1)) ≤ L * (K * (2 * L)) := by
      have hK2 : K * (Real.log (T + 6) + 1) ≤ K * (2 * L) :=
        mul_le_mul_of_nonneg_left hlogT6 (le_of_lt hKpos)
      have hKnn : (0 : ℝ) ≤ K * (Real.log (T + 6) + 1) :=
        mul_nonneg (le_of_lt hKpos)
          (by have := Real.log_nonneg (show (1 : ℝ) ≤ T + 6 by linarith); linarith)
      calc (1 / δ) * (K * (Real.log (T + 6) + 1))
          ≤ L * (K * (Real.log (T + 6) + 1)) := mul_le_mul_of_nonneg_right hinvδ hKnn
        _ ≤ L * (K * (2 * L)) := mul_le_mul_of_nonneg_left hK2 (le_of_lt hLpos)
    have hsq : L * (K * (2 * L)) = 2 * K * L ^ 2 := by ring
    have hpow : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 3)
    have hfin : 2 * K * L ^ 2 ≤ 2 * K * L ^ 3 :=
      mul_le_mul_of_nonneg_left hpow (by linarith [hKpos] : (0 : ℝ) ≤ 2 * K)
    calc ‖S‖ ≤ (1 / δ) * (K * (Real.log (T + 6) + 1)) := hS_bound
      _ ≤ L * (K * (2 * L)) := hstep
      _ = 2 * K * L ^ 2 := hsq
      _ ≤ 2 * K * L ^ 3 := hfin
  -- assemble
  have hL3nn : (0 : ℝ) ≤ L ^ 3 := by positivity
  have hfinal : ‖logDeriv riemannZeta₁ s - S‖ + ‖S‖ ≤ (C₁ + 2 * K + 1) * L ^ 3 := by
    have h1 : ‖logDeriv riemannZeta₁ s - S‖ ≤ C₁ * L ^ 3 := by simpa [L] using hloc
    have h2 : ‖S‖ ≤ 2 * K * L ^ 3 := hSb
    calc ‖logDeriv riemannZeta₁ s - S‖ + ‖S‖ ≤ C₁ * L ^ 3 + 2 * K * L ^ 3 := add_le_add h1 h2
      _ = (C₁ + 2 * K) * L ^ 3 := by ring
      _ ≤ (C₁ + 2 * K + 1) * L ^ 3 := by
          have : (C₁ + 2 * K) * L ^ 3 ≤ (C₁ + 2 * K + 1) * L ^ 3 :=
            mul_le_mul_of_nonneg_right (by linarith) hL3nn
          linarith
  have htri : ‖logDeriv riemannZeta₁ s‖ ≤ ‖logDeriv riemannZeta₁ s - S‖ + ‖S‖ := by
    have := norm_add_le (logDeriv riemannZeta₁ s - S) S
    simpa using this
  calc ‖logDeriv riemannZeta₁ (((σ : ℂ) + Complex.I * (T : ℂ)) : ℂ)‖
      = ‖logDeriv riemannZeta₁ s‖ := by rw [hs]
    _ ≤ ‖logDeriv riemannZeta₁ s - S‖ + ‖S‖ := htri
    _ ≤ (C₁ + 2 * K + 1) * L ^ 3 := hfinal
    _ = (C₁ + 2 * K + 1) * (Real.log (T + 3) + 1) ^ 3 := rfl

end Commons.NumberTheory.Zeta
