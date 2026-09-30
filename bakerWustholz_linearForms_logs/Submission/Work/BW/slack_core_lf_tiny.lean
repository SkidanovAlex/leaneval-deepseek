import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Numeric core: for `r ≥ 2`, `R ≥ 2`, `H ≥ 19`, `L ≥ 1` we have
`2(H+1) ≤ 0.032 · (32^{r+1} R^{r+1}) H L`. -/
private lemma slack_core_lf_tiny_numCore {r : ℕ} (hr : 2 ≤ r) {R H L : ℝ}
    (hR : 2 ≤ R) (hH : 19 ≤ H) (hL : 1 ≤ L) :
    2 * (H + 1) ≤ 0.032 * ((32 : ℝ) ^ (r + 1) * R ^ (r + 1)) * H * L := by
  have h3 : 3 ≤ r + 1 := by omega
  have hp32 : (32768 : ℝ) ≤ (32 : ℝ) ^ (r + 1) := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 32 by norm_num) h3
    norm_num at h
    exact h
  have hpR : (8 : ℝ) ≤ R ^ (r + 1) := by
    have h2 : (2 : ℝ) ^ (r + 1) ≤ R ^ (r + 1) := pow_le_pow_left₀ (by norm_num) hR (r + 1)
    have h3' : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (r + 1) := pow_le_pow_right₀ (by norm_num) h3
    norm_num at h3'
    linarith
  have hprod : (262144 : ℝ) ≤ (32 : ℝ) ^ (r + 1) * R ^ (r + 1) := by
    have hm := mul_le_mul hp32 hpR (by norm_num) (by positivity)
    norm_num at hm
    exact hm
  have hA : 2 * (H + 1) ≤ 0.032 * (262144 : ℝ) * H := by nlinarith [hH]
  have hB : 0.032 * (262144 : ℝ) * H ≤ 0.032 * (262144 : ℝ) * H * L := by
    have hc : (0 : ℝ) ≤ 0.032 * 262144 * H := by positivity
    simpa using mul_le_mul_of_nonneg_left hL hc
  have hC : 0.032 * (262144 : ℝ) * H * L
      ≤ 0.032 * ((32 : ℝ) ^ (r + 1) * R ^ (r + 1)) * H * L := by
    have hs0 : 0.032 * (262144 : ℝ) ≤ 0.032 * ((32 : ℝ) ^ (r + 1) * R ^ (r + 1)) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    have hs1 := mul_le_mul_of_nonneg_right hs0 (by linarith : (0 : ℝ) ≤ H)
    exact mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℝ) ≤ L)
  linarith [hA, hB, hC]

theorem slack_core_lf_tiny {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h)
    (σ : Fin r → ℝ) (hP : ((1 : ℝ) / (d : ℝ)) ^ r ≤ ∏ j, σ j) :
    2 * (d : ℝ) * (d : ℝ) * ((h : ℝ) + 1) ≤
      0.001 * ((pS r d h : ℝ) * pD r d σ) := by
  have hR2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hH19 : (19 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hRpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hDpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hHpos : (0 : ℝ) < (h : ℝ) := by linarith
  have hLpos : (0 : ℝ) < Real.log (2 * (r : ℝ) * (d : ℝ)) := by
    apply Real.log_pos
    nlinarith
  have hL1 : (1 : ℝ) ≤ Real.log (2 * (r : ℝ) * (d : ℝ)) := by
    have h4 : (4 : ℝ) ≤ 2 * (r : ℝ) * (d : ℝ) := by nlinarith
    have hlog : Real.log 4 ≤ Real.log (2 * (r : ℝ) * (d : ℝ)) :=
      Real.log_le_log (by norm_num) h4
    have h14 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 4)]
      linarith [Real.exp_one_lt_three]
    linarith
  -- core numeric inequality
  have hnum : 2 * ((h : ℝ) + 1) ≤
      0.032 * ((32 : ℝ) ^ (r + 1) * (r : ℝ) ^ (r + 1)) * (h : ℝ)
        * Real.log (2 * (r : ℝ) * (d : ℝ)) :=
    slack_core_lf_tiny_numCore hr hR2 hH19 hL1
  -- `1 ≤ d^r · ∏ σ` from `hP`
  have hstep : (1 : ℝ) ≤ (d : ℝ) ^ r * (∏ j, σ j) := by
    have hpow : 0 < (d : ℝ) ^ r := pow_pos hDpos r
    have h := mul_le_mul_of_nonneg_right hP (le_of_lt hpow)
    rw [div_pow, one_pow, div_mul_cancel₀ 1 (ne_of_gt hpow)] at h
    linarith [h]
  have hcoefnn : (0 : ℝ) ≤ 32 * (32 : ℝ) ^ (r + 1) * (r : ℝ) ^ (r + 1) * (d : ℝ) ^ 2
      * (h : ℝ) * Real.log (2 * (r : ℝ) * (d : ℝ)) := by
    have h1 : (0 : ℝ) ≤ (32 : ℝ) ^ (r + 1) := pow_nonneg (by norm_num) _
    have h2 : (0 : ℝ) ≤ (r : ℝ) ^ (r + 1) := pow_nonneg (le_of_lt hRpos) _
    have h3 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
    have h4 : (0 : ℝ) ≤ (h : ℝ) := le_of_lt hHpos
    have h5 : (0 : ℝ) ≤ Real.log (2 * (r : ℝ) * (d : ℝ)) := le_of_lt hLpos
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3)
      h4) h5
  have hle : 32 * (32 : ℝ) ^ (r + 1) * (r : ℝ) ^ (r + 1) * (d : ℝ) ^ 2 * (h : ℝ)
        * Real.log (2 * (r : ℝ) * (d : ℝ))
      ≤ 32 * (32 : ℝ) ^ (r + 1) * (r : ℝ) ^ (r + 1) * (d : ℝ) ^ 2 * (h : ℝ)
        * Real.log (2 * (r : ℝ) * (d : ℝ)) * ((d : ℝ) ^ r * (∏ j, σ j)) := by
    simpa using mul_le_mul_of_nonneg_left hstep hcoefnn
  have hid : 32 * (32 : ℝ) ^ (r + 1) * (r : ℝ) ^ (r + 1) * (d : ℝ) ^ 2 * (h : ℝ)
        * Real.log (2 * (r : ℝ) * (d : ℝ)) * ((d : ℝ) ^ r * (∏ j, σ j))
      = (16 * (r : ℝ) * (d : ℝ) * (h : ℝ)) *
        (2 * (r : ℝ) ^ r * (32 * (d : ℝ)) ^ (r + 1) * Real.log (2 * (r : ℝ) * (d : ℝ))
          * (∏ j, σ j)) := by
    rw [mul_pow, pow_succ (d : ℝ) r, pow_succ (r : ℝ) r]
    ring
  have hAunfold : ((pS r d h : ℝ) * pD r d σ)
      = (16 * (r : ℝ) * (d : ℝ) * (h : ℝ)) *
        (2 * (r : ℝ) ^ r * (32 * (d : ℝ)) ^ (r + 1) * Real.log (2 * (r : ℝ) * (d : ℝ))
          * (∏ j, σ j)) := by
    simp only [pS, pD]
    push_cast
    ring
  have hmain : 32 * (32 : ℝ) ^ (r + 1) * (r : ℝ) ^ (r + 1) * (d : ℝ) ^ 2 * (h : ℝ)
        * Real.log (2 * (r : ℝ) * (d : ℝ)) ≤ ((pS r d h : ℝ) * pD r d σ) := by
    rw [hAunfold, ← hid]
    exact hle
  have hfin : 2 * (d : ℝ) * (d : ℝ) * ((h : ℝ) + 1)
      ≤ 0.001 * (32 * (32 : ℝ) ^ (r + 1) * (r : ℝ) ^ (r + 1) * (d : ℝ) ^ 2 * (h : ℝ)
          * Real.log (2 * (r : ℝ) * (d : ℝ))) := by
    have hD2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
    have h2 := mul_le_mul_of_nonneg_right hnum hD2
    have hl : 2 * (d : ℝ) * (d : ℝ) * ((h : ℝ) + 1) = 2 * ((h : ℝ) + 1) * (d : ℝ) ^ 2 := by
      ring
    have he : 0.001 * (32 * (32 : ℝ) ^ (r + 1) * (r : ℝ) ^ (r + 1) * (d : ℝ) ^ 2 * (h : ℝ)
          * Real.log (2 * (r : ℝ) * (d : ℝ)))
        = 0.032 * ((32 : ℝ) ^ (r + 1) * (r : ℝ) ^ (r + 1)) * (h : ℝ)
          * Real.log (2 * (r : ℝ) * (d : ℝ)) * (d : ℝ) ^ 2 := by
      have he' : (0.001 : ℝ) * 32 = 0.032 := by norm_num
      rw [← he']
      ring
    rw [hl, he]
    linarith [h2]
  rw [hAunfold]
  have h3 := mul_le_mul_of_nonneg_left hmain (by norm_num : (0 : ℝ) ≤ 0.001)
  linarith [hfin, h3]

end Work.BW
