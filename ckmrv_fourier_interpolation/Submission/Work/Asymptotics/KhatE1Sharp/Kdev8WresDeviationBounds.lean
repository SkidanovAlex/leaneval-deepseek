import Mathlib
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresZAtoms
import Submission.Work.Asymptotics.KhatE1.ZAtomsSecondOrder

/-!
# Deviation bounds for the `z`-atoms of the sharp `8`-dimensional residual

`ZAtomsSecondOrder`/`Kdev8WresZAtoms` express the second-order truncations
`E2Ztr, E4Ztr, E6Ztr, GtTr, phit1Ztr, phit2Ztr` of the `z`-atoms and give the deviation bounds

  `dE2z = O(‖q(z)‖³)`, `dE4z = O(‖q(z)‖³)`, `dE6z = O(‖q(z)‖³)`  on `{T ≤ Im z}`.

This file converts these into the *normalised* deviation bounds needed by the
`u = Ept z`-expansion of the cleared residual `KdevWresClearedPoly_decomp`: each of the two
`phitVec`-atoms is replaced by its truncation (`‖phit1‖ ≤ C‖z‖²‖q‖³`, `‖phit2‖ ≤ C‖z‖²‖q‖³`),
and the bilinear combinations `phit2·E₄²`, `phit1·E₄E₆` as well as the pure Eisenstein
products `E₄²` and `E₄E₆` are estimated against their truncations.  All bounds are uniform in
`Re z` (the `z`-atoms are `q(z)`-series) and carry the prescribed `‖z‖²‖q(z)‖³`-shape.

Every estimate is elementary: `phitVec·E₄ᵏ - phitZtr·E4Ztrᵏ` splits into the deviation of the
`phitVec`-factor times the truncated Eisenstein factor plus the truncation times the deviation
of the Eisenstein factor, and each deviation is bounded by the corresponding `dE2z`/`dE4z`/
`dE6z`-bound.  The only boundedness inputs are `‖E4Ztr‖ ≤ 2401`, `‖E6Ztr‖ ≤ 17137`,
`‖E2Ztr‖ ≤ 97` and `‖GtTr z‖ ≤ 97‖z‖ + 6/π`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `1 ≤ ‖z‖` on the half-plane `{1 ≤ Im z}`. -/
private lemma norm_coe_ge_one (z : ℍ) (hz : 1 ≤ z.im) : 1 ≤ ‖(z : ℂ)‖ := by
  have h := Complex.abs_im_le_norm (z : ℂ)
  rw [UpperHalfPlane.coe_im, abs_of_pos z.im_pos] at h
  linarith

/-- `‖E2Ztr z‖ ≤ 97` for `Im z ≥ 1`. -/
private lemma norm_E2Ztr_le (z : ℍ) (hz : 1 ≤ z.im) : ‖E2Ztr z‖ ≤ 97 := by
  have hq := Work.Asymptotics.norm_qParamFun_le_one z hz
  have hq0 : 0 ≤ ‖qParamFun z‖ := norm_nonneg _
  have h1 : ‖(1 : ℂ) - 24 * qParamFun z‖ ≤ 1 + 24 := by
    calc ‖(1 : ℂ) - 24 * qParamFun z‖ ≤ ‖(1 : ℂ)‖ + ‖24 * qParamFun z‖ := norm_sub_le _ _
      _ = 1 + 24 * ‖qParamFun z‖ := by rw [norm_one, norm_mul, Complex.norm_ofNat]
      _ ≤ 1 + 24 := by linarith
  have h2 : ‖72 * (qParamFun z) ^ 2‖ ≤ 72 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h3 : ‖qParamFun z‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq
    nlinarith
  rw [E2Ztr]
  calc ‖(1 : ℂ) - 24 * qParamFun z - 72 * (qParamFun z) ^ 2‖
      ≤ ‖(1 : ℂ) - 24 * qParamFun z‖ + ‖72 * (qParamFun z) ^ 2‖ := norm_sub_le _ _
    _ ≤ (1 + 24) + 72 := add_le_add h1 h2
    _ = 97 := by norm_num

/-- `‖E4Ztr z‖ ≤ 2401` for `Im z ≥ 1`. -/
private lemma norm_E4Ztr_le (z : ℍ) (hz : 1 ≤ z.im) : ‖E4Ztr z‖ ≤ 2401 := by
  have hq := Work.Asymptotics.norm_qParamFun_le_one z hz
  have hq0 : 0 ≤ ‖qParamFun z‖ := norm_nonneg _
  have h1 : ‖(1 : ℂ) + 240 * qParamFun z‖ ≤ 1 + 240 := by
    calc ‖(1 : ℂ) + 240 * qParamFun z‖ ≤ ‖(1 : ℂ)‖ + ‖240 * qParamFun z‖ := norm_add_le _ _
      _ = 1 + 240 * ‖qParamFun z‖ := by rw [norm_one, norm_mul, Complex.norm_ofNat]
      _ ≤ 1 + 240 := by linarith
  have h2 : ‖2160 * (qParamFun z) ^ 2‖ ≤ 2160 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h3 : ‖qParamFun z‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq
    nlinarith
  rw [E4Ztr]
  calc ‖(1 : ℂ) + 240 * qParamFun z + 2160 * (qParamFun z) ^ 2‖
      ≤ ‖(1 : ℂ) + 240 * qParamFun z‖ + ‖2160 * (qParamFun z) ^ 2‖ := norm_add_le _ _
    _ ≤ (1 + 240) + 2160 := add_le_add h1 h2
    _ = 2401 := by norm_num

/-- `‖E6Ztr z‖ ≤ 17137` for `Im z ≥ 1`. -/
private lemma norm_E6Ztr_le (z : ℍ) (hz : 1 ≤ z.im) : ‖E6Ztr z‖ ≤ 17137 := by
  have hq := Work.Asymptotics.norm_qParamFun_le_one z hz
  have hq0 : 0 ≤ ‖qParamFun z‖ := norm_nonneg _
  have h1 : ‖(1 : ℂ) - 504 * qParamFun z‖ ≤ 1 + 504 := by
    calc ‖(1 : ℂ) - 504 * qParamFun z‖ ≤ ‖(1 : ℂ)‖ + ‖504 * qParamFun z‖ := norm_sub_le _ _
      _ = 1 + 504 * ‖qParamFun z‖ := by rw [norm_one, norm_mul, Complex.norm_ofNat]
      _ ≤ 1 + 504 := by linarith
  have h2 : ‖16632 * (qParamFun z) ^ 2‖ ≤ 16632 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h3 : ‖qParamFun z‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq
    nlinarith
  rw [E6Ztr]
  calc ‖(1 : ℂ) - 504 * qParamFun z - 16632 * (qParamFun z) ^ 2‖
      ≤ ‖(1 : ℂ) - 504 * qParamFun z‖ + ‖16632 * (qParamFun z) ^ 2‖ := norm_sub_le _ _
    _ ≤ (1 + 504) + 16632 := add_le_add h1 h2
    _ = 17137 := by norm_num

/-- `‖GtTr z‖ ≤ 97‖z‖ + 6/π` for `Im z ≥ 1`. -/
private lemma norm_GtTr_le (z : ℍ) (hz : 1 ≤ z.im) :
    ‖GtTr z‖ ≤ 97 * ‖(z : ℂ)‖ + 6 / Real.pi := by
  have hz' := norm_E2Ztr_le z hz
  have h6 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [GtTr]
  calc ‖(z : ℂ) * E2Ztr z - 6 * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖(z : ℂ) * E2Ztr z‖ + ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ = ‖(z : ℂ)‖ * ‖E2Ztr z‖ + 6 / Real.pi := by rw [norm_mul, h6]
    _ ≤ ‖(z : ℂ)‖ * 97 + 6 / Real.pi := by
        have := mul_le_mul_of_nonneg_left hz' (norm_nonneg (z : ℂ))
        linarith
    _ = 97 * ‖(z : ℂ)‖ + 6 / Real.pi := by ring

/-- `‖phit1Ztr z‖ ≤ (97 + 6/π)‖z‖²`. -/
private lemma norm_phit1Ztr_le (z : ℍ) (hz : 1 ≤ z.im) :
    ‖phit1Ztr z‖ ≤ (97 + 6 / Real.pi) * ‖(z : ℂ)‖ ^ 2 := by
  have hle : 97 * ‖(z : ℂ)‖ + 6 / Real.pi ≤ (97 + 6 / Real.pi) * ‖(z : ℂ)‖ := by
    have : 0 ≤ 6 / Real.pi * (‖(z : ℂ)‖ - 1) := by
      have := norm_coe_ge_one z hz; positivity
    nlinarith [this]
  rw [phit1Ztr]
  calc ‖(z : ℂ) * GtTr z‖ = ‖(z : ℂ)‖ * ‖GtTr z‖ := norm_mul _ _
    _ ≤ ‖(z : ℂ)‖ * (97 * ‖(z : ℂ)‖ + 6 / Real.pi) :=
        mul_le_mul_of_nonneg_left (norm_GtTr_le z hz) (norm_nonneg _)
    _ ≤ ‖(z : ℂ)‖ * ((97 + 6 / Real.pi) * ‖(z : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = (97 + 6 / Real.pi) * ‖(z : ℂ)‖ ^ 2 := by ring

/-- `‖phit2Ztr z‖ ≤ (97 + 6/π)²‖z‖²`. -/
private lemma norm_phit2Ztr_le (z : ℍ) (hz : 1 ≤ z.im) :
    ‖phit2Ztr z‖ ≤ (97 + 6 / Real.pi) ^ 2 * ‖(z : ℂ)‖ ^ 2 := by
  have hle : 97 * ‖(z : ℂ)‖ + 6 / Real.pi ≤ (97 + 6 / Real.pi) * ‖(z : ℂ)‖ := by
    have : 0 ≤ 6 / Real.pi * (‖(z : ℂ)‖ - 1) := by
      have := norm_coe_ge_one z hz; positivity
    nlinarith [this]
  have hG := norm_GtTr_le z hz
  have hG' : ‖GtTr z‖ ≤ (97 + 6 / Real.pi) * ‖(z : ℂ)‖ := le_trans hG hle
  rw [phit2Ztr, norm_pow]
  calc ‖GtTr z‖ ^ 2 ≤ ((97 + 6 / Real.pi) * ‖(z : ℂ)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hG' 2
    _ = (97 + 6 / Real.pi) ^ 2 * ‖(z : ℂ)‖ ^ 2 := by ring

/-- `‖E4Fun z‖ ≤ 2401 + C4` on `{1 ≤ Im z}` given `dE4z = O(‖q‖³)`. -/
private lemma norm_E4Fun_le (z : ℍ) (hz : 1 ≤ z.im) (C4 : ℝ) (hC4 : 0 < C4)
    (h4 : ‖dE4z z‖ ≤ C4 * ‖qParamFun z‖ ^ 3) : ‖E4Fun z‖ ≤ 2401 + C4 := by
  have hq1 := Work.Asymptotics.norm_qParamFun_le_one z hz
  have hq0 : 0 ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq3le : ‖qParamFun z‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  calc ‖E4Fun z‖ = ‖E4Ztr z + dE4z z‖ := by rw [E4Fun_eq_trunc_add]
    _ ≤ ‖E4Ztr z‖ + ‖dE4z z‖ := norm_add_le _ _
    _ ≤ 2401 + C4 * ‖qParamFun z‖ ^ 3 := by
        have := norm_E4Ztr_le z hz; linarith
    _ ≤ 2401 + C4 := by
        have h : C4 * ‖qParamFun z‖ ^ 3 ≤ C4 := by
          simpa using mul_le_mul_of_nonneg_left hq3le hC4.le
        linarith

/-- `‖E6Fun z‖ ≤ 17137 + C6` on `{1 ≤ Im z}` given `dE6z = O(‖q‖³)`. -/
private lemma norm_E6Fun_le (z : ℍ) (hz : 1 ≤ z.im) (C6 : ℝ) (hC6 : 0 < C6)
    (h6 : ‖dE6z z‖ ≤ C6 * ‖qParamFun z‖ ^ 3) : ‖E6Fun z‖ ≤ 17137 + C6 := by
  have hq1 := Work.Asymptotics.norm_qParamFun_le_one z hz
  have hq0 : 0 ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq3le : ‖qParamFun z‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  calc ‖E6Fun z‖ = ‖E6Ztr z + dE6z z‖ := by rw [E6Fun_eq_trunc_add]
    _ ≤ ‖E6Ztr z‖ + ‖dE6z z‖ := norm_add_le _ _
    _ ≤ 17137 + C6 * ‖qParamFun z‖ ^ 3 := by
        have := norm_E6Ztr_le z hz; linarith
    _ ≤ 17137 + C6 := by
        have h : C6 * ‖qParamFun z‖ ^ 3 ≤ C6 := by
          simpa using mul_le_mul_of_nonneg_left hq3le hC6.le
        linarith

/-- **Deviation of the `phit1`-atom**: `phitVec z 1 - phit1Ztr z = O(‖z‖²‖q(z)‖³)`. -/
private lemma dev_phit1 (T C2 : ℝ) (_hT1 : 1 ≤ T) (_hC2 : 0 < C2)
    (h2 : ∀ z : ℍ, T ≤ z.im → ‖dE2z z‖ ≤ C2 * ‖qParamFun z‖ ^ 3) :
    ∀ z : ℍ, T ≤ z.im →
      ‖Work.Kernels.phitVec z 1 - phit1Ztr z‖
        ≤ C2 * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3 := by
  intro z hz
  have hd := h2 z hz
  have hsplit : Work.Kernels.phitVec z 1 - phit1Ztr z = (z : ℂ) * ((z : ℂ) * dE2z z) := by
    rw [phitVec_one_split]; ring
  rw [hsplit, norm_mul, norm_mul]
  calc ‖(z : ℂ)‖ * (‖(z : ℂ)‖ * ‖dE2z z‖)
      ≤ ‖(z : ℂ)‖ * (‖(z : ℂ)‖ * (C2 * ‖qParamFun z‖ ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) (norm_nonneg _)
    _ = C2 * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3 := by ring

/-- **Deviation of the `phit2`-atom**: `phitVec z 2 - phit2Ztr z = O(‖z‖²‖q(z)‖³)`. -/
private lemma dev_phit2 (T C2 : ℝ) (hT1 : 1 ≤ T) (hC2 : 0 < C2)
    (h2 : ∀ z : ℍ, T ≤ z.im → ‖dE2z z‖ ≤ C2 * ‖qParamFun z‖ ^ 3) :
    ∀ z : ℍ, T ≤ z.im →
      ‖Work.Kernels.phitVec z 2 - phit2Ztr z‖
        ≤ (2 * (97 + 6 / Real.pi) * C2 + C2 ^ 2) * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3 := by
  intro z hz
  have hz1 : 1 ≤ z.im := le_trans hT1 hz
  have hq1 := Work.Asymptotics.norm_qParamFun_le_one z hz1
  have hq0 : 0 ≤ ‖qParamFun z‖ := norm_nonneg _
  have hr1 : 1 ≤ ‖(z : ℂ)‖ := norm_coe_ge_one z hz1
  have hr0 : 0 ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have hG := norm_GtTr_le z hz1
  have hd := h2 z hz
  have hq3le1 : ‖qParamFun z‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  have hsplit : Work.Kernels.phitVec z 2 - phit2Ztr z
      = 2 * GtTr z * ((z : ℂ) * dE2z z) + ((z : ℂ) * dE2z z) ^ 2 := by
    rw [phitVec_two_split]; ring
  have hD : ‖(z : ℂ) * dE2z z‖ ≤ ‖(z : ℂ)‖ * (C2 * ‖qParamFun z‖ ^ 3) := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hd hr0
  have hterm1 : ‖2 * GtTr z * ((z : ℂ) * dE2z z)‖
      ≤ 2 * (97 * ‖(z : ℂ)‖ + 6 / Real.pi) * (‖(z : ℂ)‖ * (C2 * ‖qParamFun z‖ ^ 3)) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have hA : 0 ≤ 2 * (97 * ‖(z : ℂ)‖ + 6 / Real.pi) := by positivity
    have hG' : 2 * ‖GtTr z‖ ≤ 2 * (97 * ‖(z : ℂ)‖ + 6 / Real.pi) := by linarith
    exact mul_le_mul hG' hD (norm_nonneg _) hA
  have hterm2 : ‖((z : ℂ) * dE2z z) ^ 2‖ ≤ (‖(z : ℂ)‖ * (C2 * ‖qParamFun z‖ ^ 3)) ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hD 2
  rw [hsplit]
  calc ‖2 * GtTr z * ((z : ℂ) * dE2z z) + ((z : ℂ) * dE2z z) ^ 2‖
      ≤ ‖2 * GtTr z * ((z : ℂ) * dE2z z)‖ + ‖((z : ℂ) * dE2z z) ^ 2‖ := norm_add_le _ _
    _ ≤ 2 * (97 * ‖(z : ℂ)‖ + 6 / Real.pi) * (‖(z : ℂ)‖ * (C2 * ‖qParamFun z‖ ^ 3))
          + (‖(z : ℂ)‖ * (C2 * ‖qParamFun z‖ ^ 3)) ^ 2 := add_le_add hterm1 hterm2
    _ ≤ (2 * (97 + 6 / Real.pi) * C2) * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3
          + C2 ^ 2 * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3 := by
        refine add_le_add ?_ ?_
        · have hprod : 0 ≤ 2 * (6 / Real.pi) * C2 * ‖qParamFun z‖ ^ 3 * ‖(z : ℂ)‖
              * (‖(z : ℂ)‖ - 1) := by
            have h6p : (0:ℝ) < 6 / Real.pi := by positivity
            positivity
          nlinarith [hprod]
        · have h1 : 0 ≤ 1 - ‖qParamFun z‖ ^ 3 := by linarith
          have hprod : 0 ≤ C2 ^ 2 * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3
              * (1 - ‖qParamFun z‖ ^ 3) := by positivity
          nlinarith [hprod]
    _ = (2 * (97 + 6 / Real.pi) * C2 + C2 ^ 2) * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3 := by ring

/-- **Deviation of `E₄²`**: `E4Fun z² - E4Ztr z² = O(‖q(z)‖³)`. -/
private lemma dev_E4sq (T C4 : ℝ) (hT1 : 1 ≤ T) (hC4 : 0 < C4)
    (h4 : ∀ z : ℍ, T ≤ z.im → ‖dE4z z‖ ≤ C4 * ‖qParamFun z‖ ^ 3) :
    ∀ z : ℍ, T ≤ z.im →
      ‖(E4Fun z) ^ 2 - (E4Ztr z) ^ 2‖
        ≤ C4 * (4802 + C4) * ‖qParamFun z‖ ^ 3 := by
  intro z hz
  have hz1 : 1 ≤ z.im := le_trans hT1 hz
  have hd := h4 z hz
  have hE4Z := norm_E4Ztr_le z hz1
  have hE4F := norm_E4Fun_le z hz1 C4 hC4 hd
  have hsum : ‖E4Fun z + E4Ztr z‖ ≤ 4802 + C4 := by
    calc ‖E4Fun z + E4Ztr z‖ ≤ ‖E4Fun z‖ + ‖E4Ztr z‖ := norm_add_le _ _
      _ ≤ (2401 + C4) + 2401 := by linarith
      _ = 4802 + C4 := by ring
  have hkey : (E4Fun z) ^ 2 - (E4Ztr z) ^ 2 = dE4z z * (E4Fun z + E4Ztr z) := by
    rw [E4Fun_eq_trunc_add z]; ring
  rw [hkey, norm_mul]
  calc ‖dE4z z‖ * ‖E4Fun z + E4Ztr z‖
      ≤ (C4 * ‖qParamFun z‖ ^ 3) * (4802 + C4) :=
        mul_le_mul hd hsum (norm_nonneg _) (by positivity)
    _ = C4 * (4802 + C4) * ‖qParamFun z‖ ^ 3 := by ring

/-- **Deviation of `E₄E₆`**: `E4Fun z·E6Fun z - E4Ztr z·E6Ztr z = O(‖q(z)‖³)`. -/
private lemma dev_E4E6 (T C4 C6 : ℝ) (hT1 : 1 ≤ T) (hC4 : 0 < C4) (hC6 : 0 < C6)
    (h4 : ∀ z : ℍ, T ≤ z.im → ‖dE4z z‖ ≤ C4 * ‖qParamFun z‖ ^ 3)
    (h6 : ∀ z : ℍ, T ≤ z.im → ‖dE6z z‖ ≤ C6 * ‖qParamFun z‖ ^ 3) :
    ∀ z : ℍ, T ≤ z.im →
      ‖E4Fun z * E6Fun z - E4Ztr z * E6Ztr z‖
        ≤ (C4 * (17137 + C6) + 2401 * C6) * ‖qParamFun z‖ ^ 3 := by
  intro z hz
  have hz1 : 1 ≤ z.im := le_trans hT1 hz
  have h4z := h4 z hz
  have h6z := h6 z hz
  have hE4Z := norm_E4Ztr_le z hz1
  have hE6F := norm_E6Fun_le z hz1 C6 hC6 h6z
  have hkey : E4Fun z * E6Fun z - E4Ztr z * E6Ztr z
      = dE4z z * E6Fun z + E4Ztr z * dE6z z := by
    rw [E4Fun_eq_trunc_add z, E6Fun_eq_trunc_add z]; ring
  rw [hkey]
  calc ‖dE4z z * E6Fun z + E4Ztr z * dE6z z‖
      ≤ ‖dE4z z * E6Fun z‖ + ‖E4Ztr z * dE6z z‖ := norm_add_le _ _
    _ ≤ (C4 * ‖qParamFun z‖ ^ 3) * (17137 + C6) + 2401 * (C6 * ‖qParamFun z‖ ^ 3) := by
        have ha : ‖dE4z z * E6Fun z‖ ≤ (C4 * ‖qParamFun z‖ ^ 3) * (17137 + C6) := by
          calc ‖dE4z z * E6Fun z‖ = ‖dE4z z‖ * ‖E6Fun z‖ := norm_mul _ _
            _ ≤ (C4 * ‖qParamFun z‖ ^ 3) * (17137 + C6) :=
                mul_le_mul h4z hE6F (norm_nonneg _) (by positivity)
        have hb : ‖E4Ztr z * dE6z z‖ ≤ 2401 * (C6 * ‖qParamFun z‖ ^ 3) := by
          calc ‖E4Ztr z * dE6z z‖ = ‖E4Ztr z‖ * ‖dE6z z‖ := norm_mul _ _
            _ ≤ 2401 * (C6 * ‖qParamFun z‖ ^ 3) :=
                mul_le_mul hE4Z h6z (norm_nonneg _) (by positivity)
        linarith
    _ = (C4 * (17137 + C6) + 2401 * C6) * ‖qParamFun z‖ ^ 3 := by ring

/-- **Deviation of `phit2·E₄²`**: `phitVec z 2·E4Fun z² - phit2Ztr z·E4Ztr z² = O(‖z‖²‖q(z)‖³)`. -/
private lemma dev_phit2E4sq (T C2 C4 : ℝ) (hT1 : 1 ≤ T) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (h2 : ∀ z : ℍ, T ≤ z.im → ‖dE2z z‖ ≤ C2 * ‖qParamFun z‖ ^ 3)
    (h4 : ∀ z : ℍ, T ≤ z.im → ‖dE4z z‖ ≤ C4 * ‖qParamFun z‖ ^ 3) :
    ∀ z : ℍ, T ≤ z.im →
      ‖Work.Kernels.phitVec z 2 * (E4Fun z) ^ 2 - phit2Ztr z * (E4Ztr z) ^ 2‖
        ≤ ((2 * (97 + 6 / Real.pi) * C2 + C2 ^ 2) * (2401 + C4) ^ 2
            + (97 + 6 / Real.pi) ^ 2 * (C4 * (4802 + C4)))
          * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3 := by
  intro z hz
  have hz1 : 1 ≤ z.im := le_trans hT1 hz
  have hdelta := dev_phit2 T C2 hT1 hC2 h2 z hz
  have hE4F := norm_E4Fun_le z hz1 C4 hC4 (h4 z hz)
  have hE4Fsq : ‖(E4Fun z) ^ 2‖ ≤ (2401 + C4) ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4F 2
  have hphit2 := norm_phit2Ztr_le z hz1
  have hdev := dev_E4sq T C4 hT1 hC4 h4 z hz
  have hkey : Work.Kernels.phitVec z 2 * (E4Fun z) ^ 2 - phit2Ztr z * (E4Ztr z) ^ 2
      = (Work.Kernels.phitVec z 2 - phit2Ztr z) * (E4Fun z) ^ 2
        + phit2Ztr z * ((E4Fun z) ^ 2 - (E4Ztr z) ^ 2) := by ring
  rw [hkey]
  calc ‖(Work.Kernels.phitVec z 2 - phit2Ztr z) * (E4Fun z) ^ 2
        + phit2Ztr z * ((E4Fun z) ^ 2 - (E4Ztr z) ^ 2)‖
      ≤ ‖(Work.Kernels.phitVec z 2 - phit2Ztr z) * (E4Fun z) ^ 2‖
        + ‖phit2Ztr z * ((E4Fun z) ^ 2 - (E4Ztr z) ^ 2)‖ := norm_add_le _ _
    _ ≤ ((2 * (97 + 6 / Real.pi) * C2 + C2 ^ 2) * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3)
          * (2401 + C4) ^ 2
        + ((97 + 6 / Real.pi) ^ 2 * ‖(z : ℂ)‖ ^ 2)
          * (C4 * (4802 + C4) * ‖qParamFun z‖ ^ 3) := by
        have hA : ‖(Work.Kernels.phitVec z 2 - phit2Ztr z) * (E4Fun z) ^ 2‖
            ≤ ((2 * (97 + 6 / Real.pi) * C2 + C2 ^ 2) * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3)
              * (2401 + C4) ^ 2 := by
          calc ‖(Work.Kernels.phitVec z 2 - phit2Ztr z) * (E4Fun z) ^ 2‖
              = ‖Work.Kernels.phitVec z 2 - phit2Ztr z‖ * ‖(E4Fun z) ^ 2‖ := norm_mul _ _
            _ ≤ _ := mul_le_mul hdelta hE4Fsq (norm_nonneg _) (by positivity)
        have hB : ‖phit2Ztr z * ((E4Fun z) ^ 2 - (E4Ztr z) ^ 2)‖
            ≤ ((97 + 6 / Real.pi) ^ 2 * ‖(z : ℂ)‖ ^ 2)
              * (C4 * (4802 + C4) * ‖qParamFun z‖ ^ 3) := by
          calc ‖phit2Ztr z * ((E4Fun z) ^ 2 - (E4Ztr z) ^ 2)‖
              = ‖phit2Ztr z‖ * ‖(E4Fun z) ^ 2 - (E4Ztr z) ^ 2‖ := norm_mul _ _
            _ ≤ _ := mul_le_mul hphit2 hdev (norm_nonneg _) (by positivity)
        exact add_le_add hA hB
    _ = ((2 * (97 + 6 / Real.pi) * C2 + C2 ^ 2) * (2401 + C4) ^ 2
            + (97 + 6 / Real.pi) ^ 2 * (C4 * (4802 + C4)))
          * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3 := by ring

/-- **Deviation of `phit1·E₄E₆`**:
`phitVec z 1·E4Fun z·E6Fun z - phit1Ztr z·E4Ztr z·E6Ztr z = O(‖z‖²‖q(z)‖³)`. -/
private lemma dev_phit1E4E6 (T C2 C4 C6 : ℝ) (hT1 : 1 ≤ T)
    (hC2 : 0 < C2) (hC4 : 0 < C4) (hC6 : 0 < C6)
    (h2 : ∀ z : ℍ, T ≤ z.im → ‖dE2z z‖ ≤ C2 * ‖qParamFun z‖ ^ 3)
    (h4 : ∀ z : ℍ, T ≤ z.im → ‖dE4z z‖ ≤ C4 * ‖qParamFun z‖ ^ 3)
    (h6 : ∀ z : ℍ, T ≤ z.im → ‖dE6z z‖ ≤ C6 * ‖qParamFun z‖ ^ 3) :
    ∀ z : ℍ, T ≤ z.im →
      ‖Work.Kernels.phitVec z 1 * E4Fun z * E6Fun z - phit1Ztr z * E4Ztr z * E6Ztr z‖
        ≤ (C2 * (2401 + C4) * (17137 + C6)
            + (97 + 6 / Real.pi) * (C4 * (17137 + C6) + 2401 * C6))
          * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3 := by
  intro z hz
  have hz1 : 1 ≤ z.im := le_trans hT1 hz
  have hdelta := dev_phit1 T C2 hT1 hC2 h2 z hz
  have hE4F := norm_E4Fun_le z hz1 C4 hC4 (h4 z hz)
  have hE6F := norm_E6Fun_le z hz1 C6 hC6 (h6 z hz)
  have hE4E6 : ‖E4Fun z * E6Fun z‖ ≤ (2401 + C4) * (17137 + C6) := by
    rw [norm_mul]; exact mul_le_mul hE4F hE6F (norm_nonneg _) (by positivity)
  have hphit1 := norm_phit1Ztr_le z hz1
  have hdev := dev_E4E6 T C4 C6 hT1 hC4 hC6 h4 h6 z hz
  have hkey : Work.Kernels.phitVec z 1 * E4Fun z * E6Fun z - phit1Ztr z * E4Ztr z * E6Ztr z
      = (Work.Kernels.phitVec z 1 - phit1Ztr z) * (E4Fun z * E6Fun z)
        + phit1Ztr z * (E4Fun z * E6Fun z - E4Ztr z * E6Ztr z) := by ring
  rw [hkey]
  calc ‖(Work.Kernels.phitVec z 1 - phit1Ztr z) * (E4Fun z * E6Fun z)
        + phit1Ztr z * (E4Fun z * E6Fun z - E4Ztr z * E6Ztr z)‖
      ≤ ‖(Work.Kernels.phitVec z 1 - phit1Ztr z) * (E4Fun z * E6Fun z)‖
        + ‖phit1Ztr z * (E4Fun z * E6Fun z - E4Ztr z * E6Ztr z)‖ := norm_add_le _ _
    _ ≤ (C2 * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3) * ((2401 + C4) * (17137 + C6))
        + ((97 + 6 / Real.pi) * ‖(z : ℂ)‖ ^ 2)
          * ((C4 * (17137 + C6) + 2401 * C6) * ‖qParamFun z‖ ^ 3) := by
        have hA : ‖(Work.Kernels.phitVec z 1 - phit1Ztr z) * (E4Fun z * E6Fun z)‖
            ≤ (C2 * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3) * ((2401 + C4) * (17137 + C6)) := by
          calc ‖(Work.Kernels.phitVec z 1 - phit1Ztr z) * (E4Fun z * E6Fun z)‖
              = ‖Work.Kernels.phitVec z 1 - phit1Ztr z‖ * ‖E4Fun z * E6Fun z‖ := norm_mul _ _
            _ ≤ _ := mul_le_mul hdelta hE4E6 (norm_nonneg _) (by positivity)
        have hB : ‖phit1Ztr z * (E4Fun z * E6Fun z - E4Ztr z * E6Ztr z)‖
            ≤ ((97 + 6 / Real.pi) * ‖(z : ℂ)‖ ^ 2)
              * ((C4 * (17137 + C6) + 2401 * C6) * ‖qParamFun z‖ ^ 3) := by
          calc ‖phit1Ztr z * (E4Fun z * E6Fun z - E4Ztr z * E6Ztr z)‖
              = ‖phit1Ztr z‖ * ‖E4Fun z * E6Fun z - E4Ztr z * E6Ztr z‖ := norm_mul _ _
            _ ≤ _ := mul_le_mul hphit1 hdev (norm_nonneg _) (by positivity)
        exact add_le_add hA hB
    _ = (C2 * (2401 + C4) * (17137 + C6)
            + (97 + 6 / Real.pi) * (C4 * (17137 + C6) + 2401 * C6))
          * ‖(z : ℂ)‖ ^ 2 * ‖qParamFun z‖ ^ 3 := by ring

theorem Kdev8WresDeviationBounds :
    (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.phitVec z 2 - Work.Asymptotics.KhatE1.phit2Ztr z‖
          ≤ C * ‖(z : ℂ)‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3)
    ∧ (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.phitVec z 1 - Work.Asymptotics.KhatE1.phit1Ztr z‖
          ≤ C * ‖(z : ℂ)‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3)
    ∧ (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.phitVec z 2 * (Work.Kernels.E4Fun z) ^ 2
            - Work.Asymptotics.KhatE1.phit2Ztr z * (Work.Asymptotics.KhatE1.E4Ztr z) ^ 2‖
          ≤ C * ‖(z : ℂ)‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3)
    ∧ (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.phitVec z 1 * Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
            - Work.Asymptotics.KhatE1.phit1Ztr z * Work.Asymptotics.KhatE1.E4Ztr z
                * Work.Asymptotics.KhatE1.E6Ztr z‖
          ≤ C * ‖(z : ℂ)‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3)
    ∧ (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖(Work.Kernels.E4Fun z) ^ 2 - (Work.Asymptotics.KhatE1.E4Ztr z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3)
    ∧ (∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
        ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
            - Work.Asymptotics.KhatE1.E4Ztr z * Work.Asymptotics.KhatE1.E6Ztr z‖
          ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
  obtain ⟨T2, C2, hT2, hC2, hb2⟩ := exists_dE2z_bound
  obtain ⟨T4, C4, hT4, hC4, hb4⟩ := exists_dE4z_bound
  obtain ⟨T6, C6, hT6, hC6, hb6⟩ := exists_dE6z_bound
  have hT2le : T2 ≤ max (max T2 T4) T6 :=
    le_trans (le_max_left T2 T4) (le_max_left (max T2 T4) T6)
  have hT4le : T4 ≤ max (max T2 T4) T6 :=
    le_trans (le_max_right T2 T4) (le_max_left (max T2 T4) T6)
  have hT6le : T6 ≤ max (max T2 T4) T6 := le_max_right (max T2 T4) T6
  have hT1 : 1 ≤ max (max T2 T4) T6 := le_trans hT2 hT2le
  have h2 : ∀ z : ℍ, max (max T2 T4) T6 ≤ z.im → ‖dE2z z‖ ≤ C2 * ‖qParamFun z‖ ^ 3 :=
    fun z hz => hb2 z (le_trans hT2le hz)
  have h4 : ∀ z : ℍ, max (max T2 T4) T6 ≤ z.im → ‖dE4z z‖ ≤ C4 * ‖qParamFun z‖ ^ 3 :=
    fun z hz => hb4 z (le_trans hT4le hz)
  have h6 : ∀ z : ℍ, max (max T2 T4) T6 ≤ z.im → ‖dE6z z‖ ≤ C6 * ‖qParamFun z‖ ^ 3 :=
    fun z hz => hb6 z (le_trans hT6le hz)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨max (max T2 T4) T6, 2 * (97 + 6 / Real.pi) * C2 + C2 ^ 2, hT1, by positivity,
      fun z hz => dev_phit2 (max (max T2 T4) T6) C2 hT1 hC2 h2 z hz⟩
  · exact ⟨max (max T2 T4) T6, C2, hT1, hC2,
      fun z hz => dev_phit1 (max (max T2 T4) T6) C2 hT1 hC2 h2 z hz⟩
  · exact ⟨max (max T2 T4) T6,
      (2 * (97 + 6 / Real.pi) * C2 + C2 ^ 2) * (2401 + C4) ^ 2
        + (97 + 6 / Real.pi) ^ 2 * (C4 * (4802 + C4)), hT1, by positivity,
      fun z hz => dev_phit2E4sq (max (max T2 T4) T6) C2 C4 hT1 hC2 hC4 h2 h4 z hz⟩
  · exact ⟨max (max T2 T4) T6,
      C2 * (2401 + C4) * (17137 + C6)
        + (97 + 6 / Real.pi) * (C4 * (17137 + C6) + 2401 * C6), hT1, by positivity,
      fun z hz =>
        dev_phit1E4E6 (max (max T2 T4) T6) C2 C4 C6 hT1 hC2 hC4 hC6 h2 h4 h6 z hz⟩
  · exact ⟨max (max T2 T4) T6, C4 * (4802 + C4), hT1, by positivity,
      fun z hz => dev_E4sq (max (max T2 T4) T6) C4 hT1 hC4 h4 z hz⟩
  · exact ⟨max (max T2 T4) T6, C4 * (17137 + C6) + 2401 * C6, hT1, by positivity,
      fun z hz => dev_E4E6 (max (max T2 T4) T6) C4 C6 hT1 hC4 hC6 h4 h6 z hz⟩

end

end Work.Asymptotics.KhatE1
