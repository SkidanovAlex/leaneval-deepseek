import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_negStrip_bound
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg

open Complex
open scoped Real Topology

namespace Commons.NumberTheory.Zeta

/-- **Polynomial growth of the logarithmic derivative of `ζ₁` on `Re s ≥ 1`.**

There is a constant `C > 0` with `‖ζ₁'/ζ₁(s)‖ ≤ C (1+‖s‖)^4` for every complex `s`
with `1 ≤ Re s`.  On the right half-plane `ζ₁` is zero-free, so `ζ₁'/ζ₁` is entire
there; the bound is obtained by combining the log-derivative estimate inside the
logarithmic zero-free region (for `|Im s| ≥ 1`), the constant bound on `Re s ≥ 3/2`
from the absolutely convergent von-Mangoldt series, and compactness on the remaining
bounded rectangle `1 ≤ Re s ≤ 3/2`, `|Im s| ≤ 1`. -/
theorem zeta1_logDeriv_polyGrowth :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 ≤ s.re → ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤ C * (1 + ‖s‖) ^ 4 := by
  -- logarithmic zero-free region bound for `ζ'/ζ`
  obtain ⟨c, C0, hc, hC0, _hZF, hbound⟩ := zeta_zeroFreeRegion_logDeriv_bound
  -- constant bound for `ζ'/ζ` on `Re ≥ 3/2`
  obtain ⟨M, hM, hMb⟩ := logDeriv_zeta_const_bound
  -- compactness on `1 ≤ Re s ≤ 3/2`, `-1 ≤ Im s ≤ 1`
  let K : Set ℂ := Set.Icc (1 : ℝ) (3 / 2) ×ℂ Set.Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcontd : Continuous (deriv riemannZeta₁) := (differentiable_riemannZeta₁.deriv).continuous
  have hcontζ : Continuous riemannZeta₁ := differentiable_riemannZeta₁.continuous
  have hcont : ContinuousOn (fun s : ℂ => deriv riemannZeta₁ s / riemannZeta₁ s) K :=
    hcontd.continuousOn.div hcontζ.continuousOn
      (fun s hs => zeta1_ne_zero_of_one_le_re (mem_reProdIm.mp hs).1.1)
  obtain ⟨Kb, hKb⟩ := hK.exists_bound_of_continuousOn hcont
  -- assemble the constant
  let C : ℝ := max (max (625 * (C0 + 1) + 1) (M + 2))
    (max (Kb + 1) (‖Real.eulerMascheroniConstant‖ + 1))
  have hCpos : 0 < C := by
    have h1 : (1 : ℝ) ≤ ‖Real.eulerMascheroniConstant‖ + 1 := by
      have := norm_nonneg Real.eulerMascheroniConstant
      linarith
    refine lt_of_lt_of_le one_pos (le_trans h1 ?_)
    exact le_trans (le_max_right (Kb + 1) (‖Real.eulerMascheroniConstant‖ + 1))
      (le_max_right (max (625 * (C0 + 1) + 1) (M + 2)) (max (Kb + 1) (‖Real.eulerMascheroniConstant‖ + 1)))
  have hC_ge1 : 625 * (C0 + 1) + 1 ≤ C :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hC_geM : M + 2 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC_geK : Kb + 1 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_geγ : ‖Real.eulerMascheroniConstant‖ + 1 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hCpos, ?_⟩
  intro s hs
  by_cases h_one : s = 1
  · -- the point `s = 1` (where `ζ₁ /ζ₁ = γ`)
    subst h_one
    rw [deriv_riemannZeta₁_one, riemannZeta₁_one, div_one]
    have h1 : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ C := by
      rw [Complex.norm_real]
      exact le_trans (le_add_of_nonneg_right zero_le_one) hC_geγ
    have hnorm1 : ‖(1 : ℂ)‖ = 1 := by simp
    rw [hnorm1]
    have h16 : ((1 : ℝ) + 1) ^ 4 = 16 := by norm_num
    rw [h16]
    exact le_trans h1 (le_mul_of_one_le_right (le_of_lt hCpos) (by norm_num))
  · have hz1 : riemannZeta₁ s ≠ 0 := zeta1_ne_zero_of_one_le_re hs
    have hD1 : (1 : ℝ) ≤ (1 + ‖s‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg s])
    have hD0 : (0 : ℝ) ≤ (1 + ‖s‖) ^ 4 := by positivity
    by_cases hsig : (3 / 2 : ℝ) ≤ s.re
    · -- `Re s ≥ 3/2`: constant bound
      change ‖logDeriv riemannZeta₁ s‖ ≤ C * (1 + ‖s‖) ^ 4
      rw [logDeriv_zeta1_eq h_one hz1]
      have hinv : ‖(s - 1)⁻¹‖ ≤ 2 := by
        rw [norm_inv]
        have hhalf : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
          have hre : (s - 1).re = s.re - 1 := by simp
          have hle : (s - 1).re ≤ ‖s - 1‖ := Complex.re_le_norm (s - 1)
          rw [hre] at hle
          linarith
        have h := inv_anti₀ (b := (1 / 2 : ℝ)) (by norm_num) hhalf
        have h2 : ((1 / 2 : ℝ))⁻¹ = 2 := by norm_num
        rw [h2] at h
        exact h
      calc ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖
          ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := norm_add_le _ _
        _ ≤ M + 2 := add_le_add (hMb s hsig) hinv
        _ ≤ C := hC_geM
        _ ≤ C * (1 + ‖s‖) ^ 4 := le_mul_of_one_le_right (le_of_lt hCpos) hD1
    · push Not at hsig
      by_cases ht : 1 ≤ |s.im|
      · -- `|Im s| ≥ 1`: log-derivative bound in the zero-free region
        change ‖logDeriv riemannZeta₁ s‖ ≤ C * (1 + ‖s‖) ^ 4
        rw [logDeriv_zeta1_eq h_one hz1]
        have htpos : 0 < Real.log (|s.im| + 3) :=
          Real.log_pos (by linarith [abs_nonneg s.im])
        have hσz : 1 - c / Real.log (|s.im| + 3) ≤ s.re := by
          have : 0 ≤ c / Real.log (|s.im| + 3) := div_nonneg (le_of_lt hc) (le_of_lt htpos)
          linarith
        have hs2 : s.re ≤ 2 := by linarith
        have hb := hbound s.im ht s.re hσz hs2
        have hs_eq : ((s.re : ℂ) + I * (s.im : ℂ)) = s := by
          rw [mul_comm I (s.im : ℂ)]
          exact Complex.re_add_im s
        rw [hs_eq] at hb
        have hinv : ‖(s - 1)⁻¹‖ ≤ 1 := by
          rw [norm_inv]
          apply inv_le_one_of_one_le₀
          have : |s.im| ≤ ‖s - 1‖ := by simpa using abs_im_le_norm (s - 1)
          linarith
        have hlog4 : (Real.log (|s.im| + 3) + 1) ^ 4 ≤ 625 * (1 + ‖s‖) ^ 4 := by
          have habs : |s.im| ≤ ‖s‖ := abs_im_le_norm s
          have hlog : Real.log (|s.im| + 3) ≤ |s.im| + 2 := by
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < |s.im| + 3 by positivity)
            linarith
          have hbase : Real.log (|s.im| + 3) + 1 ≤ 5 * (1 + ‖s‖) := by
            linarith [norm_nonneg s]
          have hnn : 0 ≤ Real.log (|s.im| + 3) + 1 := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ |s.im| + 3 by linarith [abs_nonneg s.im])
            linarith
          have hp := pow_le_pow_left₀ hnn hbase 4
          have h5 : (5 * (1 + ‖s‖)) ^ 4 = 625 * (1 + ‖s‖) ^ 4 := by ring
          rwa [h5] at hp
        calc ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖
            ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(s - 1)⁻¹‖ := norm_add_le _ _
          _ ≤ C0 * (Real.log (|s.im| + 3) + 1) ^ 4 + 1 := add_le_add hb hinv
          _ ≤ C * (1 + ‖s‖) ^ 4 := by
              have h1 : C0 * (Real.log (|s.im| + 3) + 1) ^ 4 ≤ C0 * (625 * (1 + ‖s‖) ^ 4) :=
                mul_le_mul_of_nonneg_left hlog4 (le_of_lt hC0)
              have h2 : 625 * C0 + 1 ≤ C := by
                have : 625 * C0 + 1 ≤ 625 * (C0 + 1) + 1 := by nlinarith
                linarith [hC_ge1]
              calc C0 * (Real.log (|s.im| + 3) + 1) ^ 4 + 1
                  ≤ C0 * (625 * (1 + ‖s‖) ^ 4) + (1 + ‖s‖) ^ 4 := by linarith [h1, hD1]
                _ = (625 * C0 + 1) * (1 + ‖s‖) ^ 4 := by ring
                _ ≤ C * (1 + ‖s‖) ^ 4 := mul_le_mul_of_nonneg_right h2 hD0
      · -- `|Im s| ≤ 1` and `Re s ≤ 3/2`: compactness
        have ht1 : |s.im| ≤ 1 := le_of_lt (lt_of_not_ge ht)
        have hmem : s ∈ K := by
          rw [mem_reProdIm]
          exact ⟨⟨hs, le_of_lt hsig⟩, abs_le.mp ht1⟩
        exact le_trans (hKb s hmem)
          (le_trans (le_trans (le_add_of_nonneg_right zero_le_one) hC_geK)
            (le_mul_of_one_le_right (le_of_lt hCpos) hD1))

end Commons.NumberTheory.Zeta
