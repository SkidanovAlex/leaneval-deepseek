import Mathlib

namespace Work.Analysis.PertCrux

/-- Quantitative core of `scale_data_v2`, stated with the data-sum as a free variable
`S = Ξ' + MK + CW + Rgl + 1`.

The witness `Lam = 10^6 · S^3 + 10^6` is chosen so that the logarithmic term is
absorbed.  Writing `X = Ξ' + 3 Lam + MK + 5 CW + 4`, the estimates are:
* `X ≤ 11 S + 3 Lam ≤ 11 S + 6·10^6 S^3 ≤ 10^7 S^3` for `S ≥ 1`;
* `log (10^7 S^3) = 7 log 10 + 3 log S ≤ 63 + 3 S` (using `log 10 ≤ 9`, `log S ≤ S`),
  so `2 + log X ≤ 65 + 3 S`;
* `32 CW (2 + log X) ≤ 32 S (65 + 3 S) = 2080 S + 96 S^2 ≤ 2176 S^3 ≤ 10^6 S^3 ≤ Lam`. -/
private lemma scale_data_aux {Ξ' MK CW Rgl S : ℝ} (hS : S = Ξ' + MK + CW + Rgl + 1)
    (hΞ' : 1 ≤ Ξ') (hMK : 0 ≤ MK) (hCW : 0 ≤ CW) (hRgl : 0 ≤ Rgl) :
    ∃ Lam : ℝ, 64 ≤ Lam ∧ Ξ' ≤ Lam ∧ MK ≤ Lam ∧ CW ≤ Lam ∧ Rgl ≤ Lam / 8 ∧
      Lam ≤ 10 ^ 6 * S ^ 3 + 10 ^ 6 ∧
      32 * CW * (2 + Real.log (Ξ' + 3 * Lam + MK + 5 * CW + 4)) ≤ Lam := by
  have hS1 : 1 ≤ S := by rw [hS]; linarith
  have hS0 : (0:ℝ) ≤ S := by linarith
  have hSpos : (0:ℝ) < S := by linarith
  have hΞS : Ξ' ≤ S := by rw [hS]; linarith
  have hMKS : MK ≤ S := by rw [hS]; linarith
  have hCWS : CW ≤ S := by rw [hS]; linarith
  have hRglS : Rgl ≤ S := by rw [hS]; linarith
  have hS3nn : (0:ℝ) ≤ S ^ 3 := pow_nonneg hS0 3
  have hSsq1 : (1:ℝ) ≤ S ^ 2 := by nlinarith [hS1]
  have hScube : S ≤ S ^ 3 := by
    have h : S ^ 3 = S * S ^ 2 := by ring
    rw [h]; exact le_mul_of_one_le_right hS0 hSsq1
  have hSsq : S ^ 2 ≤ S ^ 3 := by
    have h : S ^ 3 = S ^ 2 * S := by ring
    rw [h]; exact le_mul_of_one_le_right (sq_nonneg S) hS1
  have hS3ge1 : (1:ℝ) ≤ S ^ 3 := le_trans hS1 hScube
  have h1e6 : (1:ℝ) ≤ 10 ^ 6 := by norm_num
  have hS3_le : S ^ 3 ≤ 10 ^ 6 * S ^ 3 := by
    simpa using mul_le_mul_of_nonneg_right h1e6 hS3nn
  refine ⟨10 ^ 6 * S ^ 3 + 10 ^ 6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [hS3nn]
  · nlinarith [hΞS, hScube, hS3_le]
  · nlinarith [hMKS, hScube, hS3_le]
  · nlinarith [hCWS, hScube, hS3_le]
  · have h8 : 8 * Rgl ≤ 10 ^ 6 * S ^ 3 + 10 ^ 6 := by
      nlinarith [hRglS, hScube, hS3_le, hS3nn]
    have hd := div_le_div_of_nonneg_right h8 (by norm_num : (0:ℝ) ≤ 8)
    have he : 8 * Rgl / 8 = Rgl := by ring
    rw [he] at hd
    exact hd
  · rfl
  · have hXpos : 0 < Ξ' + 3 * (10 ^ 6 * S ^ 3 + 10 ^ 6) + MK + 5 * CW + 4 := by
      nlinarith [hΞ', hMK, hCW, hS3nn]
    have hXge1 : 1 ≤ Ξ' + 3 * (10 ^ 6 * S ^ 3 + 10 ^ 6) + MK + 5 * CW + 4 := by
      nlinarith [hΞ', hMK, hCW, hS3nn]
    have hXle : Ξ' + 3 * (10 ^ 6 * S ^ 3 + 10 ^ 6) + MK + 5 * CW + 4 ≤ 10 ^ 7 * S ^ 3 := by
      have hA : Ξ' + MK + 5 * CW + 4 ≤ 11 * S := by nlinarith [hΞS, hMKS, hCWS, hS1]
      have hB : 11 * S ≤ 11 * S ^ 3 := by nlinarith [hScube]
      have hC : 3 * (10 ^ 6 * S ^ 3 + 10 ^ 6) ≤ 6 * 10 ^ 6 * S ^ 3 := by
        nlinarith [hS3ge1, hS3nn]
      nlinarith [hA, hB, hC, hS3nn]
    have hlogmono : Real.log (Ξ' + 3 * (10 ^ 6 * S ^ 3 + 10 ^ 6) + MK + 5 * CW + 4)
        ≤ Real.log (10 ^ 7 * S ^ 3) := Real.log_le_log hXpos hXle
    have h1 : Real.log ((10:ℝ) ^ 7) = 7 * Real.log 10 := Real.log_pow 10 7
    have h2 : Real.log (S ^ 3) = 3 * Real.log S := Real.log_pow S 3
    have hlogsplit : Real.log ((10:ℝ) ^ 7 * S ^ 3) = 7 * Real.log 10 + 3 * Real.log S := by
      rw [Real.log_mul (by norm_num : (10:ℝ) ^ 7 ≠ 0) (ne_of_gt (pow_pos hSpos 3)), h1, h2]
    have hlog10 : Real.log 10 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 10)
      linarith
    have hlogS : Real.log S ≤ S := by
      have := Real.log_le_sub_one_of_pos hSpos
      linarith
    have hB' : 2 + Real.log (Ξ' + 3 * (10 ^ 6 * S ^ 3 + 10 ^ 6) + MK + 5 * CW + 4)
        ≤ 65 + 3 * S := by
      have h1' := hlogmono
      rw [hlogsplit] at h1'
      linarith
    have h32 : 32 * CW ≤ 32 * S := by nlinarith [hCWS]
    have hnn : 0 ≤ 2 + Real.log (Ξ' + 3 * (10 ^ 6 * S ^ 3 + 10 ^ 6) + MK + 5 * CW + 4) := by
      have := Real.log_nonneg hXge1
      linarith
    have hprod : 32 * CW * (2 + Real.log (Ξ' + 3 * (10 ^ 6 * S ^ 3 + 10 ^ 6) + MK + 5 * CW + 4))
        ≤ 32 * S * (65 + 3 * S) :=
      mul_le_mul h32 hB' hnn (by linarith)
    have hfin : 32 * S * (65 + 3 * S) ≤ 10 ^ 6 * S ^ 3 + 10 ^ 6 := by
      nlinarith [hScube, hSsq, hS3nn]
    linarith [hprod, hfin]

/-- Existence of a scale `Lam`, large compared with the input data and bounded by
an explicit cubic in that data, which satisfies
`32 · CW · (2 + log(Ξ' + 3 Lam + MK + 5 CW + 4)) ≤ Lam`.

The choice `Lam = 10^6 · S^3 + 10^6` with `S = Ξ' + MK + CW + Rgl + 1 ≥ 1` works;
see `scale_data_aux` for the estimates. -/
theorem scale_data_v2 {Ξ' MK CW Rgl : ℝ} (hΞ' : 1 ≤ Ξ') (hMK : 0 ≤ MK) (hCW : 0 ≤ CW)
    (hRgl : 0 ≤ Rgl) :
    ∃ Lam : ℝ, 64 ≤ Lam ∧ Ξ' ≤ Lam ∧ MK ≤ Lam ∧ CW ≤ Lam ∧ Rgl ≤ Lam / 8 ∧
      Lam ≤ 10 ^ 6 * (Ξ' + MK + CW + Rgl + 1) ^ 3 + 10 ^ 6 ∧
      32 * CW * (2 + Real.log (Ξ' + 3 * Lam + MK + 5 * CW + 4)) ≤ Lam :=
  scale_data_aux (S := Ξ' + MK + CW + Rgl + 1) rfl hΞ' hMK hCW hRgl

end Work.Analysis.PertCrux
