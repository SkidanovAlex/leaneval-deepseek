import Mathlib
import Submission.Work.BMF.liouville.vk_large_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The uniform bound on `log (2·C₀) / (2rs)` for the large-`λ` Vinogradov extraction

For `λ ≥ 13/5` the Ford §5 parameters give `r = k·⌈300λ²/k⌉ ≈ 300λ²` and `s = g·⌈200λ²/g⌉ ≈ 200λ²`,
so that `2rs ≈ 120000 λ⁴`; the total logarithm `log (2·C₀)` splits (`vk_dC0_log_expand_aux`) into
`log 2`, the two power terms `k·log(5r)`, `(h−1)·log s`, the two Stechkin constants
`stechK·k·r'·(k+r')·(1+log k)` and `stechK·g·s'·(g+s')·(1+log g)`, and `(g+3)(g−h+1)·log 2`.
Each is dominated by `(1/8)·10^33·(1+stechK)·2rs`, using the elementary parameter bounds
(`vk_large_param_bounds_aux`); consequently
`log (2·C₀)/(2rs) ≤ 10^33 (1 + stechK)`.

The `10^33` is enormously generous: the two Stechkin terms only cost `O(stechK/λ)` and the
remaining terms `O(lam^2)/r s = O(1/λ²)`, uniformly in `λ`, because the bounds on `k + r'`, `g + s'`
and `1 + log` of the parameters are linear in `λ` while `rs ≥ 60000 λ⁴`.
-/

namespace Work.BMF.liouville

open Finset
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 4000000


private lemma vk_log_prod5 {a b c d e : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    Real.log (a * b * c * d * e) = Real.log a + Real.log b + Real.log c + Real.log d + Real.log e := by
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd) he,
      Real.log_mul (mul_ne_zero (mul_ne_zero ha hb) hc) hd,
      Real.log_mul (mul_ne_zero ha hb) hc,
      Real.log_mul ha hb]

private theorem vk_large_param_bounds_aux (lam : ℝ) (hlam : 13/5 ≤ lam) :
    0 < dC0 lam ∧
    0 < (dR lam : ℝ) ∧ 0 < (dS lam : ℝ) ∧
    1 ≤ (dK lam : ℝ) ∧ 1 ≤ (dG lam : ℝ) ∧
    (dK lam : ℝ) ≤ 6 * lam ∧ (dG lam : ℝ) ≤ 6 * lam ∧
    (dH lam : ℝ) ≤ 2 * lam ∧
    ((dH lam - 1 : ℕ) : ℝ) ≤ 2 * lam ∧
    300 * lam ^ 2 ≤ (dR lam : ℝ) ∧ 200 * lam ^ 2 ≤ (dS lam : ℝ) ∧
    (dS lam : ℝ) ≤ 300 * lam ^ 2 ∧
    5 * (dR lam : ℝ) ≤ 2000 * lam ^ 2 ∧
    (dK lam : ℝ) + (dRp lam : ℝ) ≤ 67 * lam ∧
    (dG lam : ℝ) + (dSp lam : ℝ) ≤ 47 * lam ∧
    1 + Real.log (dK lam : ℝ) ≤ 7 * lam ∧
    1 + Real.log (dG lam : ℝ) ≤ 7 * lam ∧
    (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) ≤ 54 * lam ^ 2 := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hGge : 5 * lam ≤ (dG lam : ℝ) := by simpa [dG] using Nat.le_ceil (5 * lam)
  have hGlt : (dG lam : ℝ) < 5 * lam + 1 := by
    simpa [dG] using Nat.ceil_lt_add_one (show (0:ℝ) ≤ 5 * lam by linarith)
  have hHge : lam ≤ (dH lam : ℝ) := by simpa [dH] using Nat.le_ceil lam
  have hHlt : (dH lam : ℝ) < lam + 1 := by
    simpa [dH] using Nat.ceil_lt_add_one (show (0:ℝ) ≤ lam by linarith)
  have hKcast : ((dK lam : ℝ)) = (dG lam : ℝ) + 1 := by rw [dK]; push_cast; ring
  have hRcast : ((dR lam : ℝ)) = (dK lam : ℝ) * (dRp lam : ℝ) := by rw [dR]; push_cast; ring
  have hScast : ((dS lam : ℝ)) = (dG lam : ℝ) * (dSp lam : ℝ) := by rw [dS]; push_cast; ring
  have hGpos : 0 < (dG lam : ℝ) := by linarith
  have hKpos : 0 < (dK lam : ℝ) := by rw [hKcast]; linarith
  have hRpge : 300 * lam ^ 2 / (dK lam : ℝ) ≤ (dRp lam : ℝ) := by
    simpa [dRp] using Nat.le_ceil (300 * lam ^ 2 / (dK lam : ℝ))
  have hRplt : (dRp lam : ℝ) < 300 * lam ^ 2 / (dK lam : ℝ) + 1 := by
    simpa [dRp] using Nat.ceil_lt_add_one
      (show (0:ℝ) ≤ 300 * lam ^ 2 / (dK lam : ℝ) from div_nonneg (by positivity) hKpos.le)
  have hSpge : 200 * lam ^ 2 / (dG lam : ℝ) ≤ (dSp lam : ℝ) := by
    simpa [dSp] using Nat.le_ceil (200 * lam ^ 2 / (dG lam : ℝ))
  have hSplt : (dSp lam : ℝ) < 200 * lam ^ 2 / (dG lam : ℝ) + 1 := by
    simpa [dSp] using Nat.ceil_lt_add_one
      (show (0:ℝ) ≤ 200 * lam ^ 2 / (dG lam : ℝ) from div_nonneg (by positivity) hGpos.le)
  have hmultK : (dK lam : ℝ) * (300 * lam ^ 2 / (dK lam : ℝ)) = 300 * lam ^ 2 := by
    rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hKpos)
  have hmultG : (dG lam : ℝ) * (200 * lam ^ 2 / (dG lam : ℝ)) = 200 * lam ^ 2 := by
    rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hGpos)
  have hRge : 300 * lam ^ 2 ≤ (dR lam : ℝ) := by
    rw [hRcast]
    calc (300:ℝ) * lam ^ 2 = (dK lam : ℝ) * (300 * lam ^ 2 / (dK lam : ℝ)) := hmultK.symm
      _ ≤ (dK lam : ℝ) * (dRp lam : ℝ) := mul_le_mul_of_nonneg_left hRpge hKpos.le
  have hSge : 200 * lam ^ 2 ≤ (dS lam : ℝ) := by
    rw [hScast]
    calc (200:ℝ) * lam ^ 2 = (dG lam : ℝ) * (200 * lam ^ 2 / (dG lam : ℝ)) := hmultG.symm
      _ ≤ (dG lam : ℝ) * (dSp lam : ℝ) := mul_le_mul_of_nonneg_left hSpge hGpos.le
  have hSle : (dS lam : ℝ) ≤ 300 * lam ^ 2 := by
    rw [hScast]
    have h1 : (dG lam : ℝ) * (dSp lam : ℝ) < 200 * lam ^ 2 + (dG lam : ℝ) := by
      calc (dG lam : ℝ) * (dSp lam : ℝ) < (dG lam : ℝ) * (200 * lam ^ 2 / (dG lam : ℝ) + 1) :=
            mul_lt_mul_of_pos_left hSplt hGpos
        _ = (dG lam : ℝ) * (200 * lam ^ 2 / (dG lam : ℝ)) + (dG lam : ℝ) := by ring
        _ = 200 * lam ^ 2 + (dG lam : ℝ) := by rw [hmultG]
    nlinarith [h1, hGlt, hlam]
  have hKle : (dK lam : ℝ) ≤ 6 * lam := by linarith [hKcast, hGlt, hlam]
  have hGle : (dG lam : ℝ) ≤ 6 * lam := by linarith [hGlt, hlam]
  have hHle : (dH lam : ℝ) ≤ 2 * lam := by linarith [hHlt, hlam]
  have hHm1 : ((dH lam - 1 : ℕ) : ℝ) ≤ 2 * lam := by
    have h1 : ((dH lam - 1 : ℕ) : ℝ) ≤ (dH lam : ℝ) := by
      exact_mod_cast Nat.sub_le (dH lam) 1
    linarith
  have hK1 : 1 ≤ (dK lam : ℝ) := by rw [hKcast]; linarith
  have hG1 : 1 ≤ (dG lam : ℝ) := by linarith
  have hRle : (dR lam : ℝ) ≤ 300 * lam ^ 2 + (dK lam : ℝ) := by
    rw [hRcast]
    calc (dK lam : ℝ) * (dRp lam : ℝ)
        ≤ (dK lam : ℝ) * (300 * lam ^ 2 / (dK lam : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hRplt.le hKpos.le
      _ = (dK lam : ℝ) * (300 * lam ^ 2 / (dK lam : ℝ)) + (dK lam : ℝ) := by ring
      _ = 300 * lam ^ 2 + (dK lam : ℝ) := by rw [hmultK]
  have h5R : 5 * (dR lam : ℝ) ≤ 2000 * lam ^ 2 := by
    have h1 : 5 * (dR lam : ℝ) ≤ 5 * (300 * lam ^ 2 + (dK lam : ℝ)) := by linarith [hRle]
    have h2 : 5 * (300 * lam ^ 2 + (dK lam : ℝ)) ≤ 2000 * lam ^ 2 := by
      rw [hKcast]; nlinarith [hGlt, hlam]
    linarith
  have hKge5 : 5 * lam ≤ (dK lam : ℝ) := by rw [hKcast]; linarith [hGge]
  have hdiv1 : 300 * lam ^ 2 / (dK lam : ℝ) ≤ 60 * lam := by
    have h1 : 300 * lam ^ 2 / (dK lam : ℝ) ≤ 300 * lam ^ 2 / (5 * lam) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hKge5
    have h2 : 300 * lam ^ 2 / (5 * lam) = 60 * lam := by
      rw [div_eq_iff (by linarith : (5:ℝ) * lam ≠ 0)]; ring
    linarith [h1, h2]
  have hdiv2 : 200 * lam ^ 2 / (dG lam : ℝ) ≤ 40 * lam := by
    have h1 : 200 * lam ^ 2 / (dG lam : ℝ) ≤ 200 * lam ^ 2 / (5 * lam) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hGge
    have h2 : 200 * lam ^ 2 / (5 * lam) = 40 * lam := by
      rw [div_eq_iff (by linarith : (5:ℝ) * lam ≠ 0)]; ring
    linarith [h1, h2]
  have hKRp : (dK lam : ℝ) + (dRp lam : ℝ) ≤ 67 * lam := by
    have h1 : (dRp lam : ℝ) < 60 * lam + 1 := by linarith [hRplt, hdiv1]
    linarith [hKcast, hGlt, h1, hlam]
  have hGSp : (dG lam : ℝ) + (dSp lam : ℝ) ≤ 47 * lam := by
    have h1 : (dSp lam : ℝ) < 40 * lam + 1 := by linarith [hSplt, hdiv2]
    linarith [hGlt, h1, hlam]
  have hlogK : 1 + Real.log (dK lam : ℝ) ≤ 7 * lam := by
    have h1 : Real.log (dK lam : ℝ) ≤ (dK lam : ℝ) := Real.log_le_self hKpos.le
    have h2 : (dK lam : ℝ) ≤ 5 * lam + 2 := by linarith [hKcast, hGlt]
    linarith [h1, h2, hlam]
  have hlogG : 1 + Real.log (dG lam : ℝ) ≤ 7 * lam := by
    have h1 : Real.log (dG lam : ℝ) ≤ (dG lam : ℝ) := Real.log_le_self hGpos.le
    linarith [h1, hGlt, hlam]
  have hGH : (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) ≤ 54 * lam ^ 2 := by
    have h1 : ((dG lam + 3 : ℕ) : ℝ) ≤ 9 * lam := by
      have hc : ((dG lam + 3 : ℕ) : ℝ) = (dG lam : ℝ) + 3 := by push_cast; ring
      rw [hc]; linarith [hGlt, hlam]
    have h2 : ((dG lam - dH lam + 1 : ℕ) : ℝ) ≤ 6 * lam := by
      have hc : ((dG lam - dH lam + 1 : ℕ) : ℝ) ≤ ((dG lam + 1 : ℕ) : ℝ) := by
        apply Nat.cast_le.mpr; omega
      have hc2 : ((dG lam + 1 : ℕ) : ℝ) = (dG lam : ℝ) + 1 := by push_cast; ring
      rw [hc2] at hc; linarith [hc, hGlt, hlam]
    have hcast : (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ)
        = ((dG lam + 3 : ℕ) : ℝ) * ((dG lam - dH lam + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    have h3 := mul_le_mul h1 h2 (by positivity) (by linarith : (0:ℝ) ≤ 9 * lam)
    nlinarith [h3]
  have hRpos : 0 < (dR lam : ℝ) := by nlinarith [hRge, hlam]
  have hSpos : 0 < (dS lam : ℝ) := by nlinarith [hSge, hlam]
  have hdC0pos : 0 < dC0 lam := by
    rw [dC0]
    exact mul_pos (mul_pos (mul_pos (mul_pos
      (pow_pos (by linarith : (0:ℝ) < 5 * (dR lam : ℝ)) _)
      (pow_pos hSpos _))
      (stechF_pos _ _)) (stechF_pos _ _))
      (pow_pos (by norm_num) _)
  exact ⟨hdC0pos, hRpos, hSpos, hK1, hG1, hKle, hGle, hHle, hHm1, hRge, hSge, hSle, h5R,
    hKRp, hGSp, hlogK, hlogG, hGH⟩

private theorem vk_dC0_log_expand_aux (lam : ℝ) (hlam : 13/5 ≤ lam) :
    Real.log (2 * dC0 lam)
      = Real.log 2 + (dK lam : ℝ) * Real.log (5 * (dR lam : ℝ))
        + ((dH lam - 1 : ℕ) : ℝ) * Real.log (dS lam : ℝ)
        + stechK * (dK lam : ℝ) * (dRp lam : ℝ) * ((dK lam : ℝ) + (dRp lam : ℝ)) * (1 + Real.log (dK lam : ℝ))
        + stechK * (dG lam : ℝ) * (dSp lam : ℝ) * ((dG lam : ℝ) + (dSp lam : ℝ)) * (1 + Real.log (dG lam : ℝ))
        + (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) * Real.log 2 := by
  obtain ⟨hdC0pos, hRpos, hSpos, hK1, hG1, hKle, hGle, hHle, hHm1, hRge, hSge, hSle, h5R,
    hKRp, hGSp, hlogK, hlogG, hGH⟩ := vk_large_param_bounds_aux lam hlam
  have hRne : (dR lam : ℝ) ≠ 0 := ne_of_gt hRpos
  have hSne : (dS lam : ℝ) ≠ 0 := ne_of_gt hSpos
  have h5Rne : 5 * (dR lam : ℝ) ≠ 0 := by linarith
  have hdC0ne : dC0 lam ≠ 0 := ne_of_gt hdC0pos
  have hf1 : (5 * (dR lam : ℝ)) ^ (dK lam) ≠ 0 := pow_ne_zero _ h5Rne
  have hf2 : (dS lam : ℝ) ^ (dH lam - 1) ≠ 0 := pow_ne_zero _ hSne
  have hf3 : stechF (dK lam) (dRp lam) ≠ 0 := (stechF_pos _ _).ne'
  have hf4 : stechF (dG lam) (dSp lam) ≠ 0 := (stechF_pos _ _).ne'
  have hf5 : (2 : ℝ) ^ ((dG lam + 3) * (dG lam - dH lam + 1)) ≠ 0 :=
    (pow_pos (by norm_num) _).ne'
  rw [Real.log_mul (by norm_num) hdC0ne, dC0]
  rw [vk_log_prod5 hf1 hf2 hf3 hf4 hf5]
  rw [Real.log_pow, Real.log_pow, Real.log_pow, stechF, stechF, Real.log_exp, Real.log_exp]
  ring

theorem vk_large_const_bound (lam : ℝ) (hlam : 13/5 ≤ lam) :
    Real.log (2 * dC0 lam) / (2 * (dR lam : ℝ) * (dS lam : ℝ)) ≤ 10 ^ 33 * (1 + stechK) := by
  obtain ⟨hdC0pos, hRpos, hSpos, hK1, hG1, hKle, hGle, hHle, hHm1, hRge, hSge, hSle, h5R,
    hKRp, hGSp, hlogK, hlogG, hGH⟩ := vk_large_param_bounds_aux lam hlam
  have hlam0 : (0:ℝ) < lam := by linarith
  have hstechKpos : 0 < stechK := stechK_pos
  have h1sK : (0:ℝ) ≤ 1 + stechK := by linarith
  have hRcast : (dR lam : ℝ) = (dK lam : ℝ) * (dRp lam : ℝ) := by rw [dR]; push_cast; ring
  have hScast : (dS lam : ℝ) = (dG lam : ℝ) * (dSp lam : ℝ) := by rw [dS]; push_cast; ring
  have hKpos : 0 < (dK lam : ℝ) := by linarith
  have hGpos : 0 < (dG lam : ℝ) := by linarith
  have hRpr0 : 0 < (dRp lam : ℝ) := by nlinarith [hRcast, hRpos, hKpos]
  have hSpr0 : 0 < (dSp lam : ℝ) := by nlinarith [hScast, hSpos, hGpos]
  have hP0 : 0 < (dK lam : ℝ) * (dRp lam : ℝ) := mul_pos hKpos hRpr0
  have hQ0 : 0 < (dG lam : ℝ) * (dSp lam : ℝ) := mul_pos hGpos hSpr0
  have hQle : (dG lam : ℝ) * (dSp lam : ℝ) ≤ 300 * lam ^ 2 := by rw [← hScast]; exact hSle
  have hlog := vk_dC0_log_expand_aux lam hlam
  have hTnn : (0:ℝ) ≤ 10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ)) := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) h1sK
    · nlinarith [hRpos, hSpos]
  have hcoef : (0:ℝ) ≤ (1/8) * 10^33 * (1 + stechK) :=
    mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) h1sK
  have hlam13 : (1:ℝ) ≤ lam := by linarith
  have h2nn : (0:ℝ) ≤ lam ^ 2 := sq_nonneg lam
  have h12 : lam ≤ lam ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlam13 hlam0.le
    nlinarith [h]
  have h34 : lam ^ 3 ≤ lam ^ 4 := by
    have h := mul_le_mul_of_nonneg_right h12 h2nn
    nlinarith [h]
  have h24 : lam ^ 2 ≤ lam ^ 4 := by
    have h1sq : (1:ℝ) ≤ lam ^ 2 := by nlinarith [hlam13]
    have h := mul_le_mul_of_nonneg_left h1sq h2nn
    nlinarith [h]
  have hlam4 : (16:ℝ) ≤ lam ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (by linarith : (2:ℝ) ≤ lam) 4
    norm_num at h; exact h
  have h2RS : 120000 * lam ^ 4 ≤ 2 * (dR lam : ℝ) * (dS lam : ℝ) := by
    have h1 : 300 * lam ^ 2 * (200 * lam ^ 2) ≤ (dR lam : ℝ) * (dS lam : ℝ) :=
      mul_le_mul hRge hSge (by positivity) hRpos.le
    nlinarith [h1]
  have hT2 : 15000 * 10^33 * (1 + stechK) * lam ^ 4 ≤
      (1/8) * (10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by
    have hstep := mul_le_mul_of_nonneg_left h2RS hcoef
    have hr1 : (1/8) * 10^33 * (1 + stechK) * (120000 * lam ^ 4)
        = 15000 * 10^33 * (1 + stechK) * lam ^ 4 := by ring
    have hr2 : (1/8) * 10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ))
        = (1/8) * (10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by ring
    rwa [hr1, hr2] at hstep
  have hT1 : 50 * 10^33 * (1 + stechK) * ((dK lam : ℝ) * (dRp lam : ℝ)) * lam ^ 2 ≤
      (1/8) * (10^33 * (1 + stechK) * (2 * ((dK lam : ℝ) * (dRp lam : ℝ)) * (dS lam : ℝ))) := by
    have hcoef2 : (0:ℝ) ≤ (1/4) * 10^33 * (1 + stechK) * ((dK lam : ℝ) * (dRp lam : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) h1sK) hP0.le
    have hstep := mul_le_mul_of_nonneg_left hSge hcoef2
    have hr1 : (1/4) * 10^33 * (1 + stechK) * ((dK lam : ℝ) * (dRp lam : ℝ)) * (200 * lam ^ 2)
        = 50 * 10^33 * (1 + stechK) * ((dK lam : ℝ) * (dRp lam : ℝ)) * lam ^ 2 := by ring
    have hr2 : (1/4) * 10^33 * (1 + stechK) * ((dK lam : ℝ) * (dRp lam : ℝ)) * (dS lam : ℝ)
        = (1/8) * (10^33 * (1 + stechK) * (2 * ((dK lam : ℝ) * (dRp lam : ℝ)) * (dS lam : ℝ))) := by ring
    rwa [hr1, hr2] at hstep
  have hA : Real.log 2 ≤ (1/8) * (10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have h1 : (1:ℝ) ≤ 15000 * 10^33 * (1 + stechK) * lam ^ 4 := by
      have h2 : (1:ℝ) ≤ 15000 * 10^33 * lam ^ 4 := by
        have h3 := mul_le_mul_of_nonneg_left hlam4 (by norm_num : (0:ℝ) ≤ 15000 * 10^33)
        have h4 : (1:ℝ) ≤ 15000 * 10^33 * 16 := by norm_num
        linarith [h3, h4]
      have h3 := mul_le_mul_of_nonneg_left h2 h1sK
      nlinarith [h3]
    linarith [hlog2, h1, hT2]
  have hB : (dK lam : ℝ) * Real.log (5 * (dR lam : ℝ)) ≤
      (1/8) * (10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by
    have hlogR : Real.log (5 * (dR lam : ℝ)) ≤ 5 * (dR lam : ℝ) :=
      Real.log_le_self (by linarith [hRpos])
    have hstep : (dK lam : ℝ) * Real.log (5 * (dR lam : ℝ)) ≤ (dK lam : ℝ) * (5 * (dR lam : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogR hKpos.le
    rw [hRcast] at hstep ⊢
    have hP5 : (0:ℝ) ≤ 5 * ((dK lam : ℝ) * (dRp lam : ℝ)) := by nlinarith [hP0]
    have hkk : (dK lam : ℝ) * (5 * ((dK lam : ℝ) * (dRp lam : ℝ))) ≤
        30 * lam * ((dK lam : ℝ) * (dRp lam : ℝ)) := by
      have hmm := mul_le_mul_of_nonneg_right hKle hP5
      nlinarith [hmm]
    have hscalar : 30 * lam ≤ 50 * 10^33 * (1 + stechK) * lam ^ 2 := by nlinarith [hlam, h1sK]
    have hscal : 30 * lam * ((dK lam : ℝ) * (dRp lam : ℝ)) ≤
        50 * 10^33 * (1 + stechK) * ((dK lam : ℝ) * (dRp lam : ℝ)) * lam ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hscalar hP0.le
      nlinarith [h]
    linarith [hstep, hkk, hscal, hT1]
  have hC : ((dH lam - 1 : ℕ) : ℝ) * Real.log (dS lam : ℝ) ≤
      (1/8) * (10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by
    have hlogS : Real.log (dS lam : ℝ) ≤ (dS lam : ℝ) := Real.log_le_self hSpos.le
    have hHnn : (0:ℝ) ≤ ((dH lam - 1 : ℕ) : ℝ) := by positivity
    have hstep : ((dH lam - 1 : ℕ) : ℝ) * Real.log (dS lam : ℝ) ≤
        ((dH lam - 1 : ℕ) : ℝ) * (dS lam : ℝ) := mul_le_mul_of_nonneg_left hlogS hHnn
    have hstep2 : ((dH lam - 1 : ℕ) : ℝ) * (dS lam : ℝ) ≤ (2 * lam) * (300 * lam ^ 2) :=
      mul_le_mul hHm1 hSle hSpos.le (by positivity)
    have hscal0 : (2 * lam) * (300 * lam ^ 2) ≤ 15000 * 10^33 * lam ^ 4 := by
      have h5 := mul_le_mul_of_nonneg_left h34 (by norm_num : (0:ℝ) ≤ 600)
      have h6 := mul_le_mul_of_nonneg_right (by norm_num : (600:ℝ) ≤ 15000 * 10^33)
        (by positivity : (0:ℝ) ≤ lam ^ 4)
      nlinarith [h5, h6]
    have hscal : (2 * lam) * (300 * lam ^ 2) ≤ 15000 * 10^33 * (1 + stechK) * lam ^ 4 := by
      have h := mul_le_mul_of_nonneg_left hscal0 h1sK
      nlinarith [h]
    linarith [hstep, hstep2, hscal, hT2]
  have hD : stechK * (dK lam : ℝ) * (dRp lam : ℝ) * ((dK lam : ℝ) + (dRp lam : ℝ)) *
      (1 + Real.log (dK lam : ℝ)) ≤
      (1/8) * (10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by
    rw [hRcast]
    have hnn : (0:ℝ) ≤ 1 + Real.log (dK lam : ℝ) := by
      have := Real.log_nonneg hK1; linarith
    have hSP : (0:ℝ) ≤ stechK * ((dK lam : ℝ) * (dRp lam : ℝ)) := mul_nonneg hstechKpos.le hP0.le
    have hstep1 : stechK * ((dK lam : ℝ) * (dRp lam : ℝ)) * ((dK lam : ℝ) + (dRp lam : ℝ)) *
        (1 + Real.log (dK lam : ℝ))
        ≤ stechK * ((dK lam : ℝ) * (dRp lam : ℝ)) * (67 * lam) * (7 * lam) := by
      have ha : ((dK lam : ℝ) + (dRp lam : ℝ)) * (1 + Real.log (dK lam : ℝ)) ≤ (67 * lam) * (7 * lam) :=
        mul_le_mul hKRp hlogK hnn (by linarith)
      have hb := mul_le_mul_of_nonneg_left ha hSP
      nlinarith [hb]
    have hscal0 : (469:ℝ) * stechK ≤ 50 * 10^33 * (1 + stechK) := by nlinarith [hstechKpos]
    have hscal : stechK * ((dK lam : ℝ) * (dRp lam : ℝ)) * (67 * lam) * (7 * lam)
        ≤ 50 * 10^33 * (1 + stechK) * ((dK lam : ℝ) * (dRp lam : ℝ)) * lam ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_right hscal0 hP0.le
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ lam ^ 2)
      nlinarith [h2]
    have hgoal : stechK * (dK lam : ℝ) * (dRp lam : ℝ) * ((dK lam : ℝ) + (dRp lam : ℝ)) *
        (1 + Real.log (dK lam : ℝ))
        ≤ 50 * 10^33 * (1 + stechK) * ((dK lam : ℝ) * (dRp lam : ℝ)) * lam ^ 2 := by
      rw [show stechK * (dK lam : ℝ) * (dRp lam : ℝ) * ((dK lam : ℝ) + (dRp lam : ℝ)) *
            (1 + Real.log (dK lam : ℝ))
          = stechK * ((dK lam : ℝ) * (dRp lam : ℝ)) * ((dK lam : ℝ) + (dRp lam : ℝ)) *
            (1 + Real.log (dK lam : ℝ)) from by ring]
      linarith [hstep1, hscal]
    linarith [hgoal, hT1]
  have hE : stechK * (dG lam : ℝ) * (dSp lam : ℝ) * ((dG lam : ℝ) + (dSp lam : ℝ)) *
      (1 + Real.log (dG lam : ℝ)) ≤
      (1/8) * (10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by
    have hnn : (0:ℝ) ≤ 1 + Real.log (dG lam : ℝ) := by
      have := Real.log_nonneg hG1; linarith
    have hSQ : (0:ℝ) ≤ stechK * ((dG lam : ℝ) * (dSp lam : ℝ)) := mul_nonneg hstechKpos.le hQ0.le
    have hstep1 : stechK * ((dG lam : ℝ) * (dSp lam : ℝ)) * ((dG lam : ℝ) + (dSp lam : ℝ)) *
        (1 + Real.log (dG lam : ℝ))
        ≤ stechK * ((dG lam : ℝ) * (dSp lam : ℝ)) * (47 * lam) * (7 * lam) := by
      have ha : ((dG lam : ℝ) + (dSp lam : ℝ)) * (1 + Real.log (dG lam : ℝ)) ≤ (47 * lam) * (7 * lam) :=
        mul_le_mul hGSp hlogG hnn (by linarith)
      have hb := mul_le_mul_of_nonneg_left ha hSQ
      nlinarith [hb]
    have hstep2 : stechK * ((dG lam : ℝ) * (dSp lam : ℝ)) * (47 * lam) * (7 * lam)
        ≤ 98700 * stechK * lam ^ 4 := by
      have h0 : (0:ℝ) ≤ 329 * stechK * lam ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hstechKpos.le) (sq_nonneg lam)
      have h1 := mul_le_mul_of_nonneg_left hQle h0
      nlinarith [h1]
    have hstep3 : 98700 * stechK * lam ^ 4 ≤ 15000 * 10^33 * (1 + stechK) * lam ^ 4 := by
      have h0 : 98700 * stechK ≤ 15000 * 10^33 * (1 + stechK) := by nlinarith [hstechKpos]
      exact mul_le_mul_of_nonneg_right h0 (by positivity : (0:ℝ) ≤ lam ^ 4)
    have hgoal : stechK * (dG lam : ℝ) * (dSp lam : ℝ) * ((dG lam : ℝ) + (dSp lam : ℝ)) *
        (1 + Real.log (dG lam : ℝ)) ≤ 98700 * stechK * lam ^ 4 := by
      rw [show stechK * (dG lam : ℝ) * (dSp lam : ℝ) * ((dG lam : ℝ) + (dSp lam : ℝ)) *
            (1 + Real.log (dG lam : ℝ))
          = stechK * ((dG lam : ℝ) * (dSp lam : ℝ)) * ((dG lam : ℝ) + (dSp lam : ℝ)) *
            (1 + Real.log (dG lam : ℝ)) from by ring]
      linarith [hstep1, hstep2]
    linarith [hgoal, hstep3, hT2]
  have hF : (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) * Real.log 2 ≤
      (1/8) * (10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ))) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have hlog2nn : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : (((dG lam + 3) * (dG lam - dH lam + 1) : ℕ) : ℝ) * Real.log 2 ≤ (54 * lam ^ 2) * 1 :=
      mul_le_mul hGH hlog2 hlog2nn (by positivity)
    have h2 : (54 * lam ^ 2) * 1 ≤ 15000 * 10^33 * (1 + stechK) * lam ^ 4 := by
      have h2a : (54:ℝ) * lam ^ 2 ≤ 15000 * 10^33 * lam ^ 4 := by
        have h5 := mul_le_mul_of_nonneg_left h24 (by norm_num : (0:ℝ) ≤ 54)
        have h6 := mul_le_mul_of_nonneg_right (by norm_num : (54:ℝ) ≤ 15000 * 10^33)
          (by positivity : (0:ℝ) ≤ lam ^ 4)
        nlinarith [h5, h6]
      have h := mul_le_mul_of_nonneg_left h2a h1sK
      nlinarith [h]
    linarith [h1, h2, hT2]
  have key : Real.log (2 * dC0 lam) ≤ 10^33 * (1 + stechK) * (2 * (dR lam : ℝ) * (dS lam : ℝ)) := by
    rw [hlog]
    linarith [hA, hB, hC, hD, hE, hF, hTnn]
  have hpos2 : 0 < 2 * (dR lam : ℝ) * (dS lam : ℝ) := by nlinarith [hRpos, hSpos]
  rw [div_le_iff₀ hpos2]
  exact key


end

end Work.BMF.liouville
