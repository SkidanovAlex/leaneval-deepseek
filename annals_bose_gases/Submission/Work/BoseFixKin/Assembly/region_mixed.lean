import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixKin.FSRegime
import Submission.Work.BoseKinLoc.Assembly.tprR_branches_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixKin.Assembly

open Work.BoseKinLoc.Assembly

/-- **Region II (first far, second near) of the three-region budget for `core_budget_fs`.**
`tprR (2s) C q = (q - (4s)⁻¹)²` (`tprR_far_gen`, `(2*(2*s))⁻¹ = (4*s)⁻¹`) and
`tprR (2ds) C q = C (2ds)³ q²` (`tprR_near`).  Write `c := cFS K C`, `A := (1+K)/2`,
`a := (4s)⁻¹` so `q ≥ (5/6)(2s)⁻¹ = (5/3) a`.
* `q² - T3 = 2qa - a² ≥ (7/5) q a = (7/20) q/s` (as `q ≥ (5/3)a`), so
  `q² - T3 - T4 ≥ (1-εT)(7/20)(q/s)` once `T4 = 8C εT d³s³q² ≤ εT q²`, which follows
  from `8 C s³ ≤ 1/128`.
* `T1 ≤ A εT q/(2d) ≤ (A c/2)(q/s)` by AM–GM (`1 + d²q² ≥ 2 d q`, hence
  `q²/(1+d²q²) ≤ q/(2d)`), `εT s ≤ c d` and `s > 0`.
* `T2 = 2b q²/(q²+1/2) ≤ 2b`.
* Since `q/s ≥ 5/(12s²) ≥ 20/3` (as `s ≤ 1/4`), one has
  `2b + (A c/2)(q/s) ≤ (7/20)(1-εT)(q/s)` using `A c ≤ 1/128`, `2b ≤ 1/8`,
  `1-εT ≥ 3/4`.  Template: `Work.BoseKinLoc.Assembly.budget_mixed`. -/
theorem region_mixed {K C q d s εT b : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hq : 0 ≤ q) (hd : 0 < d) (hd1 : d ≤ 1) (hs : 0 < s) (hsc : s ≤ cFS K C)
    (hε : 0 ≤ εT) (hεc : εT ≤ cFS K C) (hcpl : εT * s ≤ cFS K C * d)
    (hb : 0 ≤ b) (hb16 : b ≤ 1 / 16)
    (h1 : (5 / 6) * (2 * s)⁻¹ ≤ q) (h2 : ¬ ((5 / 6) * (2 * (d * s))⁻¹ ≤ q)) :
    (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
        + b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2))
        + (1 - εT) * Work.BoseKinLoc.Assembly.tprR (2 * s) C q
        + εT * Work.BoseKinLoc.Assembly.tprR (2 * (d * s)) C q
      ≤ q ^ 2 := by
  have hA0 : (0 : ℝ) ≤ (1 + K) / 2 := by linarith
  have hq_pos : 0 < q := by
    have h : (0 : ℝ) < (5 / 6) * (2 * s)⁻¹ := by positivity
    linarith
  have hs4 : s ≤ 1 / 4 := hsc.trans (min_le_left _ _)
  have hε4 : εT ≤ 1 / 4 := hεc.trans (min_le_left _ _)
  have hden : (0 : ℝ) < 64 * (K + C + 1) := by positivity
  -- `A * c ≤ 1/128` with `A = (1+K)/2`, `c = cFS K C`
  have hAc : (1 + K) / 2 * cFS K C ≤ 1 / 128 := by
    have hle : cFS K C ≤ 1 / (64 * (K + C + 1)) := min_le_right _ _
    have h1' := mul_le_mul_of_nonneg_left hle hA0
    have h2' : (1 + K) / 2 * (1 / (64 * (K + C + 1))) ≤ 1 / 128 := by
      rw [mul_one_div, div_le_iff₀ hden]; nlinarith only [hK, hC]
    linarith
  -- `C * s ≤ 1/64`
  have hCs : C * s ≤ 1 / 64 := by
    have hle : s ≤ 1 / (64 * (K + C + 1)) := hsc.trans (min_le_right _ _)
    have h1' := mul_le_mul_of_nonneg_left hle hC.le
    have h2' : C * (1 / (64 * (K + C + 1))) ≤ 1 / 64 := by
      rw [mul_one_div, div_le_iff₀ hden]; nlinarith only [hK, hC]
    linarith
  -- the two branches of `tprR`
  have hfar : tprR (2 * s) C q = (q - (4 * s)⁻¹) ^ 2 := by
    rw [tprR_far_gen (by positivity : (0 : ℝ) < 2 * s) h1, two_two_inv]
  have hnear : tprR (2 * (d * s)) C q = C * (2 * (d * s)) ^ 3 * q ^ 2 := tprR_near h2
  rw [hfar, hnear, show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
  -- `T1`: AM–GM (`q²/(1+d²q²) ≤ q/(2d)`) and the coupling `εT s ≤ c d`
  have hAM : q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ q / (2 * d) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + d ^ 2 * q ^ 2)
      (by positivity : (0 : ℝ) < 2 * d)]
    nlinarith only [mul_nonneg (sq_nonneg (d * q - 1)) hq, hq, hd.le]
  have hcd : εT / (2 * d) ≤ cFS K C / (2 * s) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * d) (by positivity : (0 : ℝ) < 2 * s)]
    linarith only [hcpl]
  have hT1 : (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
      ≤ (1 + K) / 2 * cFS K C / 2 * (q / s) := by
    have hstep1 : (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
        ≤ (1 + K) / 2 * εT * (q / (2 * d)) := by
      have hcoef : (0 : ℝ) ≤ (1 + K) / 2 * εT := mul_nonneg hA0 hε
      have h := mul_le_mul_of_nonneg_left hAM hcoef
      calc (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2)
            = (1 + K) / 2 * εT * (q ^ 2 / (1 + d ^ 2 * q ^ 2)) := by ring
        _ ≤ (1 + K) / 2 * εT * (q / (2 * d)) := h
    have hstep2 : (1 + K) / 2 * εT * (q / (2 * d))
        ≤ (1 + K) / 2 * cFS K C / 2 * (q / s) := by
      have hfac : (0 : ℝ) ≤ (1 + K) / 2 * q := mul_nonneg hA0 hq
      have h := mul_le_mul_of_nonneg_left hcd hfac
      calc (1 + K) / 2 * εT * (q / (2 * d)) = (1 + K) / 2 * q * (εT / (2 * d)) := by ring
        _ ≤ (1 + K) / 2 * q * (cFS K C / (2 * s)) := h
        _ = (1 + K) / 2 * cFS K C / 2 * (q / s) := by ring
    linarith only [hstep1, hstep2]
  -- `T2 ≤ 2b ≤ 1/8`
  have hT2 : b * 2 * (q ^ 2 / (q ^ 2 + 1 / 2)) ≤ 1 / 8 := by
    have h1' : q ^ 2 / (q ^ 2 + 1 / 2) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < q ^ 2 + 1 / 2)]
      linarith only [sq_nonneg q]
    have h2' : (0 : ℝ) ≤ 2 * b := by linarith only [hb]
    have h := mul_le_mul_of_nonneg_left h1' h2'
    have h3 : b * 2 * (q ^ 2 / (q ^ 2 + 1 / 2)) ≤ 2 * b := by linarith only [h]
    linarith only [h3, hb16]
  -- `q/s ≥ 20/3`
  have hqos : 20 / 3 ≤ q / s := by
    have hb1 : (20 / 3) * s ≤ (5 / 6) * (2 * s)⁻¹ := by
      have heq : (5 / 6) * (2 * s)⁻¹ = 5 / (12 * s) := by field_simp; ring
      rw [heq, le_div_iff₀ (by positivity : (0 : ℝ) < 12 * s)]
      have hs2 : s ^ 2 ≤ 1 / 16 := by
        have hm := mul_nonneg (sub_nonneg.mpr hs4) (by linarith only [hs4, hs] : (0 : ℝ) ≤ 1 / 4 + s)
        nlinarith only [hm]
      nlinarith only [hs2]
    rw [le_div_iff₀ hs]
    linarith only [hb1, h1]
  -- `q ≥ (5/3) a` with `a = (4s)⁻¹`
  have hqa : (5 / 3) * (4 * s)⁻¹ ≤ q := by
    have heq : (5 / 3) * (4 * s)⁻¹ = (5 / 6) * (2 * s)⁻¹ := by field_simp; ring
    rw [heq]; exact h1
  -- `q² - T3 ≥ (7/20) q/s`
  have hT3lb : (7 / 20) * (q / s) ≤ q ^ 2 - (q - (4 * s)⁻¹) ^ 2 := by
    have ha : 0 < (4 * s)⁻¹ := by positivity
    have h35 : (0 : ℝ) ≤ (3 / 5) * q - (4 * s)⁻¹ := by linarith only [hqa]
    have hprod : 0 ≤ (4 * s)⁻¹ * ((3 / 5) * q - (4 * s)⁻¹) := mul_nonneg ha.le h35
    have h7 : (7 / 20) * (q / s) = (7 / 5) * q * (4 * s)⁻¹ := by field_simp; ring
    rw [h7]; nlinarith only [hprod]
  -- `T4 ≤ (7/20) q/s`
  have hqbd : q ≤ 5 / (12 * d * s) := by
    have h := not_le.mp h2
    have heq : (5 / 6) * (2 * (d * s))⁻¹ = 5 / (12 * d * s) := by field_simp; ring
    rw [heq] at h
    exact h.le
  have hT4b : C * (2 * (d * s)) ^ 3 * q ^ 2 ≤ (7 / 20) * (q / s) := by
    have hR : (0 : ℝ) ≤ 5 / (12 * d * s) := by positivity
    have hqsq : q ^ 2 ≤ (5 / (12 * d * s)) ^ 2 := by nlinarith only [hqbd, hq, hR]
    have hcoef : (0 : ℝ) ≤ C * (2 * (d * s)) ^ 3 := by positivity
    have h := mul_le_mul_of_nonneg_left hqsq hcoef
    have heq : C * (2 * (d * s)) ^ 3 * (5 / (12 * d * s)) ^ 2 = (25 / 18) * C * d * s := by
      field_simp; ring
    have hbd : (25 / 18) * C * d * s ≤ 7 / 3 := by
      have hh : C * s * d ≤ C * s * 1 := mul_le_mul_of_nonneg_left hd1 (by positivity : (0 : ℝ) ≤ C * s)
      nlinarith only [hh, hCs]
    have hq3 : 7 / 3 ≤ (7 / 20) * (q / s) := by nlinarith only [hqos]
    linarith only [h, heq, hbd, hq3]
  -- assemble: `T1 + T2 ≤ (1-εT)(7/20)(q/s)`
  have hmain1 : (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) + b * 2 * (q ^ 2 / (q ^ 2 + 1 / 2))
      ≤ (1 - εT) * ((7 / 20) * (q / s)) := by
    have hAc2 : (1 + K) / 2 * cFS K C / 2 ≤ 1 / 256 := by linarith only [hAc]
    have hqs0 : (0 : ℝ) ≤ q / s := by linarith only [hqos]
    have hT1' : (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) ≤ (1 / 256) * (q / s) := by
      nlinarith only [hT1, hAc2, hqs0]
    have hε1 : (3 / 4 : ℝ) ≤ 1 - εT := by linarith only [hε4]
    nlinarith only [hT1', hT2, hε1, hqos, hqs0]
  -- and `(1-εT)(7/20)(q/s) ≤ q² - T3 - εT T4`
  have hmain2 : (1 - εT) * ((7 / 20) * (q / s))
      ≤ q ^ 2 - (q - (4 * s)⁻¹) ^ 2 - εT * (C * (2 * (d * s)) ^ 3 * q ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hT4b hε
    nlinarith only [h, hT3lb]
  nlinarith only [hmain1, hmain2, sq_nonneg (q - (4 * s)⁻¹), hε]

end Work.BoseFixKin.Assembly
