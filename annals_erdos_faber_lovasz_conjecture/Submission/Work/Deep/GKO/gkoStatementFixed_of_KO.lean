import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.Combine
import Submission.Work.Deep.GKO.maxDeg_ge_of_lowerReg
import Submission.Work.Deep.GKO.minDeg_ge_of_lowerReg
import Submission.Work.Deep.GKO.lowerReg_of_delete
import Submission.Work.Deep.GKO.robustExpander_lowerReg
import Submission.Work.Deep.GKO.exists_deficiencyMatchings_split
import Submission.Work.Deep.GKO.exists_spanningLinearForest
import Submission.Work.Deep.GKO.exists_perfectMatching_of_lowerReg
import Submission.Work.Deep.GKO.linearForest_matchingDecomposition
import Submission.Work.Deep.GKO.hasMatchingDecomposition_finsetSup
import Submission.Work.Deep.GKO.colorable_of_matchingDecomposition
import Submission.Work.Deep.GKO.oneFactorization_of_hamDecomp
import Submission.Work.Deep.GKO.degree_graphOf
import Submission.Work.Deep.GKO.maxDegree_graphOf
import Submission.Work.Deep.GKO.selfLowerRegular_iff_lowerReg
import Submission.Work.Deep.GKO.asm_helpers

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false


open scoped BigOperators
open Classical
open ErdosFaberLovaszConjecture

namespace Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-! ## Numeric helpers for the thresholds -/

/-- `28 * ν / α ≤ c` from `ν ≤ α * c / 28`. -/
lemma div28_le {α c ν : ℝ} (hα : 0 < α) (hν : ν ≤ α * c / 28) : 28 * ν / α ≤ c := by
  rw [div_le_iff₀ hα]
  have h1 : 28 * ν ≤ 28 * (α * c / 28) := mul_le_mul_of_nonneg_left hν (by norm_num)
  have h2 : 28 * (α * c / 28) = α * c := by ring
  linarith [h1, h2.le, h2.ge]

lemma le_of_sum {Y a b c d e f : ℝ} (h : Y = a + b + c + d + e + f) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) : a ≤ Y := by
  rw [h]; linarith

lemma prod4_le_pow4 {Y a b c d : ℝ} (hY : 1 ≤ Y) (ha : a ≤ Y) (hb : b ≤ Y) (hc : c ≤ Y)
    (hd : d ≤ Y) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) :
    a * b * c * d ≤ Y ^ 4 := by
  have hY0 : 0 ≤ Y := le_trans zero_le_one hY
  have h1 : a * b ≤ Y * Y := mul_le_mul ha hb hb0 hY0
  have h2 : c * d ≤ Y * Y := mul_le_mul hc hd hd0 hY0
  have h3 : a * b * (c * d) ≤ (Y * Y) * (Y * Y) :=
    mul_le_mul h1 h2 (mul_nonneg hc0 hd0) (mul_nonneg hY0 hY0)
  have h4 : (Y * Y) * (Y * Y) = Y ^ 4 := by ring
  have h5 : a * b * c * d = a * b * (c * d) := by ring
  rw [h5, ← h4]
  exact h3

lemma prod2_le_one {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    a * b ≤ 1 := by nlinarith [ha, ha1, hb, hb1]

lemma prod3_le_one {a b c : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) : a * b * c ≤ 1 := by
  have hab : a * b ≤ 1 := by nlinarith [ha, ha1, hb, hb1]
  calc a * b * c ≤ 1 * c := mul_le_mul_of_nonneg_right hab hc
    _ = c := one_mul c
    _ ≤ 1 := hc1

lemma div_le_div_const_left {x K L : ℝ} (hx : 0 ≤ x) (hL : 0 < L) (hKL : L ≤ K) :
    x / K ≤ x / L := by
  have h1 : K⁻¹ ≤ L⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hL hKL
  calc x / K = x * K⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ x * L⁻¹ := mul_le_mul_of_nonneg_left h1 hx
    _ = x / L := by rw [div_eq_mul_inv]

/-- Combining the bound on `2 * km` with the two half-bounds on the two summands. -/
lemma two_k_le {α c ν nn : ℝ} {km : ℕ} (hα : 0 < α) (hn : 0 < nn)
    (hk : (km : ℝ) ≤ 14 * (ν * nn + 1) / α)
    (h1 : 28 * ν / α ≤ c / 2) (h2 : 28 / α ≤ c * nn / 2) :
    2 * (km : ℝ) ≤ c * nn := by
  have hk2 : 2 * (km : ℝ) ≤ 28 * (ν * nn + 1) / α := by
    have h := mul_le_mul_of_nonneg_left hk (by norm_num : (0:ℝ) ≤ 2)
    have h2 : 2 * (14 * (ν * nn + 1) / α) = 28 * (ν * nn + 1) / α := by ring
    linarith [h, h2.le, h2.ge]
  have h7 : 28 * (ν * nn + 1) / α = 28 * ν * nn / α + 28 / α := by
    rw [mul_add, mul_one, add_div]
    ring
  have h8 : 28 * ν * nn / α ≤ c / 2 * nn := by
    rw [div_le_iff₀ hα]
    have h1' : 28 * ν ≤ c / 2 * α := by
      rw [div_le_iff₀ hα] at h1
      linarith [h1]
    nlinarith [h1', hn, hα]
  have h9 : 28 / α ≤ c * nn / 2 := h2
  have h10 : c / 2 * nn + c * nn / 2 = c * nn := by ring
  linarith [hk2, h7.le, h7.ge, h8, h9, h10.le, h10.ge]

/-- `2 * √(x) ≤ c` from `x ≤ (c/2)^2` and `0 ≤ c`. -/
lemma two_sqrt_le {x c : ℝ} (hx : x ≤ (c / 2) ^ 2) (hc : 0 ≤ c) : 2 * Real.sqrt x ≤ c := by
  have h1 : Real.sqrt x ≤ Real.sqrt ((c / 2) ^ 2) := Real.sqrt_le_sqrt hx
  have h2 : Real.sqrt ((c / 2) ^ 2) = c / 2 := Real.sqrt_sq (by linarith)
  linarith [h1, h2.le, h2.ge]

lemma aux16 {p τ' α : ℝ} (hp0 : 0 < p) (hτ0 : 0 < τ') (hα1 : α ≤ 1) :
    16 * (p * τ' * α) ≤ p * τ' * 10 ^ 20 := by
  have h5 : p * τ' * α ≤ p * τ' * 1 := mul_le_mul_of_nonneg_left hα1 (by positivity)
  have h6 : (0:ℝ) < p * τ' := by positivity
  have h7 : (16:ℝ) * (p * τ') ≤ p * τ' * 10 ^ 20 := by
    have h8 : (16:ℝ) ≤ 10^20 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left h8 (le_of_lt h6)]
  linarith [h5, h7]

lemma two_eps_le8 {p τ' α ε : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hτ0 : 0 < τ') (hτ1 : τ' ≤ 1)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (h : ε ≤ p * τ' * α / 10^20) : 2 * ε ≤ p * τ' / 8 := by
  have h10 : (0:ℝ) < 10^20 := by norm_num
  have h2 : 2 * ε ≤ 2 * (p * τ' * α / 10 ^ 20) := by linarith [h]
  refine le_trans h2 ?_
  rw [show 2 * (p * τ' * α / 10 ^ 20) = 2 * (p * τ' * α) / 10 ^ 20 by ring,
    div_le_div_iff₀ h10 (by norm_num : (0:ℝ) < 8)]
  have h3 : 2 * (p * τ' * α) * 8 = 16 * (p * τ' * α) := by ring
  rw [h3]
  exact aux16 hp0 hτ0 hα1

lemma two_eps_leα {p τ' α ε : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hτ0 : 0 < τ') (hτ1 : τ' ≤ 1)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (h : ε ≤ p * τ' * α / 10^20) : 2 * ε ≤ α / 100 := by
  have h10 : (0:ℝ) < 10^20 := by norm_num
  have h2 : 2 * ε ≤ 2 * (p * τ' * α / 10 ^ 20) := by linarith [h]
  refine le_trans h2 ?_
  rw [show 2 * (p * τ' * α / 10 ^ 20) = 2 * (p * τ' * α) / 10 ^ 20 by ring,
    div_le_div_iff₀ h10 (by norm_num : (0:ℝ) < 100)]
  have h3 : p * τ' * α ≤ α := by
    have h4 : p * τ' ≤ 1 := by nlinarith [hp0, hp1, hτ0, hτ1]
    have h5 : p * τ' * α ≤ 1 * α := mul_le_mul_of_nonneg_right h4 (le_of_lt hα0)
    linarith [h5]
  nlinarith [h3, hα0]

lemma two_eps_lep {p τ' α ε : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hτ0 : 0 < τ') (hτ1 : τ' ≤ 1)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (h : ε ≤ p * τ' * α / 10^20) : 2 * ε ≤ p / 100 := by
  have h10 : (0:ℝ) < 10^20 := by norm_num
  have h2 : 2 * ε ≤ 2 * (p * τ' * α / 10 ^ 20) := by linarith [h]
  refine le_trans h2 ?_
  rw [show 2 * (p * τ' * α / 10 ^ 20) = 2 * (p * τ' * α) / 10 ^ 20 by ring,
    div_le_div_iff₀ h10 (by norm_num : (0:ℝ) < 100)]
  have h3 : p * τ' * α ≤ p := by
    have h4 : τ' * α ≤ 1 := by nlinarith [hτ0, hτ1, hα0, hα1]
    have h5 : p * (τ' * α) ≤ p * 1 := mul_le_mul_of_nonneg_left h4 (le_of_lt hp0)
    linarith [h5]
  nlinarith [h3, hp0]

lemma hkey_aux {p τ τ' x : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hτ0 : 0 < τ) (hτ'τ : τ' ≤ τ)
    (hτ'1 : τ' ≤ 1) (hx : x ≤ p * τ' / 8) : x < (p - x) * (τ - x) := by
  have hx1 : x ≤ p / 8 := by nlinarith [hx, hp0, hτ'1]
  have hx2 : x ≤ τ / 8 := by nlinarith [hx, hp1, hτ'τ, hτ0, hp0]
  have h1 : p - x ≥ 7 * p / 8 := by linarith [hx1, hp0]
  have h2 : τ - x ≥ 7 * τ / 8 := by linarith [hx2, hτ0]
  have h3 : 0 ≤ p - x := by linarith [h1, hp0]
  have h4 : 0 ≤ 7 * τ / 8 := by linarith [hτ0]
  have h5 : (7 * p / 8) * (7 * τ / 8) ≤ (p - x) * (τ - x) := mul_le_mul h1 h2 h4 h3
  have h6 : x < (7 * p / 8) * (7 * τ / 8) := by nlinarith [hx2, hp0, hτ0]
  linarith [h5, h6]

lemma hroom_aux {p τ τ' x n : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hτ0 : 0 < τ) (hτ'τ : τ' ≤ τ)
    (hτ'1 : τ' ≤ 1) (hn : 0 < n) (hx : x ≤ p * τ' / 8) (hnτ : 2 ≤ τ * n) :
    1 ≤ (τ - x - x / (p - x)) * n := by
  have hx1 : x ≤ p / 8 := by nlinarith [hx, hp0, hτ'1]
  have hx2 : x ≤ τ / 8 := by nlinarith [hx, hp1, hτ'τ, hτ0, hp0]
  have h1 : p - x ≥ 7 * p / 8 := by linarith [hx1, hp0]
  have hpε : 0 < p - x := by linarith [h1, hp0]
  have h2 : x / (p - x) ≤ τ / 7 := by
    rw [div_le_iff₀ hpε]
    nlinarith [hx1, hp0, hτ0]
  have h4 : τ - x - x / (p - x) ≥ τ / 2 := by linarith [hx2, h2, hτ0]
  have h5 : τ / 2 * n ≤ (τ - x - x / (p - x)) * n := mul_le_mul_of_nonneg_right h4 (le_of_lt hn)
  have h6 : (1:ℝ) ≤ τ / 2 * n := by nlinarith [hnτ, hτ0]
  linarith [h5, h6]

lemma eps2tau_aux {p τ τ' x : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hτ'0 : 0 < τ') (hτ'τ : τ' ≤ τ)
    (hx : x ≤ p * τ' / 8) : 2 * x ≤ τ := by
  have h1 : 2 * x ≤ 2 * (p * τ' / 8) := mul_le_mul_of_nonneg_left hx (by norm_num)
  have h2 : 2 * (p * τ' / 8) = p * τ' / 4 := by ring
  have h3 : p * τ' / 4 ≤ τ := by
    have h4 : p * τ' ≤ 1 * τ' := mul_le_mul_of_nonneg_right hp1 (le_of_lt hτ'0)
    have h5 : p * τ' ≤ τ := by linarith [h4, hτ'τ]
    linarith [h5]
  calc 2 * x ≤ 2 * (p * τ' / 8) := h1
    _ = p * τ' / 4 := h2
    _ ≤ τ := h3

lemma hminG_aux {p α n K D : ℝ} (hp0 : 0 < p) (hn : 0 < n) (hα2 : α ≤ p / 2)
    (hD : (9/10) * p * n ≤ D) (hK : K ≤ (p/8) * n) (hK0 : 0 ≤ K) : α * n + K ≤ D := by
  have h1 : α * n ≤ (p/2) * n := mul_le_mul_of_nonneg_right hα2 (le_of_lt hn)
  have h2 : (p/2) * n + K ≤ D := by nlinarith [hD, hK, hp0, hn]
  linarith [h1, h2]

lemma halphaKO_aux {p α n K D : ℝ} (hp0 : 0 < p) (hn : 0 < n) (hα2 : α ≤ p / 2)
    (hD : (9/10) * p * n ≤ D) (hK : K ≤ (p/8) * n) (hK0 : 0 ≤ K) : α * n ≤ D - K := by
  have h1 : α * n ≤ (p/2) * n := mul_le_mul_of_nonneg_right hα2 (le_of_lt hn)
  have h2 : (p/2) * n ≤ D - K := by nlinarith [hD, hK, hp0, hn]
  linarith [h1, h2]

lemma halphaKO'_aux {p α n K D : ℝ} (hp0 : 0 < p) (hn : 0 < n) (hα2 : α ≤ p / 2)
    (hD : (9/10) * p * n ≤ D) (hK : K ≤ (p/8) * n) (hnp : 4 ≤ p * n) :
    α * n + 1 ≤ D - K := by
  have h1 : α * n ≤ (p/2) * n := mul_le_mul_of_nonneg_right hα2 (le_of_lt hn)
  have h2 : (1:ℝ) ≤ (11/40) * p * n := by nlinarith [hnp, hp0]
  have h3 : (p/2) * n + (11/40) * p * n = (9/10) * p * n - (p/8) * n := by ring
  have h4 : (9/10) * p * n - (p/8) * n ≤ D - K := by nlinarith [hD, hK]
  linarith [h1, h2, h3.le, h3.ge, h4]

lemma hDelta9_aux {p ε ν n D : ℝ} (hn : 0 < n) (hν0 : 0 ≤ ν) (h : 3 * ε + ν ≤ p / 10)
    (hD : (p - 3 * ε) * n ≤ D) : (9 / 10) * p * n ≤ D := by
  have h1 : (9/10) * p ≤ p - 3 * ε := by linarith
  have h2 : (9/10) * p * n ≤ (p - 3*ε) * n := mul_le_mul_of_nonneg_right h1 (le_of_lt hn)
  linarith [h2, hD]

lemma four_eps_le_alpha {α x : ℝ} (hx : x ≤ α / 100) (hα : 0 < α) : 4 * x ≤ α := by linarith

lemma six_eps_le_one {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hx : x ≤ p / 100) : 6 * x ≤ 1 := by
  linarith

lemma eps_lt_p {p x : ℝ} (hp0 : 0 < p) (hx : x ≤ p / 100) : x < p := by linarith

lemma big_aux {α x n : ℝ} (hα : 0 < α) (hn : 0 < n) (hx : x ≤ α / 100) (hnα : 12 ≤ n * α) :
    1 ≤ (α - 2 * x) * n := by
  have h1 : 2 * x ≤ α / 2 := by linarith
  have h2 : α - 2 * x ≥ α / 2 := by linarith
  have h3 : (1:ℝ) ≤ α / 2 * n := by nlinarith [hnα, hα]
  have h4 : α / 2 * n ≤ (α - 2 * x) * n := mul_le_mul_of_nonneg_right h2 (le_of_lt hn)
  linarith [h3, h4]

lemma sqrt_inv_le {n c : ℝ} (hn : 0 < n) (hc : 0 ≤ c) (h : 4 ≤ c ^ 2 * n) :
    2 * Real.sqrt (1 / n) ≤ c := by
  refine two_sqrt_le ?_ hc
  rw [div_le_iff₀ hn]
  nlinarith [h]

lemma hkey_o_aux {p τ τ' x : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hτ0 : 0 < τ) (hτ'τ : τ' ≤ τ)
    (hτ'1 : τ' ≤ 1) (hx : x ≤ p * τ' / 4) : x < (p - x) * (τ - x) := by
  have hx1 : x ≤ p / 4 := by nlinarith [hx, hp0, hτ'1]
  have hx2 : x ≤ τ / 4 := by nlinarith [hx, hp1, hτ'τ, hτ0, hp0]
  have h1 : p - x ≥ 3 * p / 4 := by linarith [hx1, hp0]
  have h2 : τ - x ≥ 3 * τ / 4 := by linarith [hx2, hτ0]
  have h3 : 0 ≤ p - x := by linarith [h1, hp0]
  have h4 : 0 ≤ 3 * τ / 4 := by linarith [hτ0]
  have h5 : (3 * p / 4) * (3 * τ / 4) ≤ (p - x) * (τ - x) := mul_le_mul h1 h2 h4 h3
  have h6 : x < (3 * p / 4) * (3 * τ / 4) := by nlinarith [hx2, hp0, hτ0]
  linarith [h5, h6]

lemma hroom_o_aux {p τ τ' x n : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hτ0 : 0 < τ) (hτ'τ : τ' ≤ τ)
    (hτ'1 : τ' ≤ 1) (hn : 0 < n) (hx : x ≤ p * τ' / 4) (hnτ : 4 ≤ τ * n) :
    1 ≤ (τ - x - x / (p - x)) * n := by
  have hx1 : x ≤ p / 4 := by nlinarith [hx, hp0, hτ'1]
  have hx2 : x ≤ τ / 4 := by nlinarith [hx, hp1, hτ'τ, hτ0, hp0]
  have h1 : p - x ≥ 3 * p / 4 := by linarith [hx1, hp0]
  have hpε : 0 < p - x := by linarith [h1, hp0]
  have h2 : x / (p - x) ≤ τ / 3 := by
    rw [div_le_iff₀ hpε]
    nlinarith [hx1, hp0, hτ0]
  have h4 : τ - x - x / (p - x) ≥ τ / 4 := by linarith [hx2, h2, hτ0]
  have h5 : τ / 4 * n ≤ (τ - x - x / (p - x)) * n := mul_le_mul_of_nonneg_right h4 (le_of_lt hn)
  have h6 : (1:ℝ) ≤ τ / 4 * n := by nlinarith [hnτ, hτ0]
  linarith [h5, h6]

lemma eps_o_2tau {p τ τ' x : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hτ'0 : 0 < τ') (hτ'τ : τ' ≤ τ)
    (hx : x ≤ p * τ' / 4) : 2 * x ≤ τ := by
  have h1 : 2 * x ≤ 2 * (p * τ' / 4) := mul_le_mul_of_nonneg_left hx (by norm_num)
  have h2 : 2 * (p * τ' / 4) = p * τ' / 2 := by ring
  have h3 : p * τ' / 2 ≤ τ := by
    have h4 : p * τ' ≤ 1 * τ' := mul_le_mul_of_nonneg_right hp1 (le_of_lt hτ'0)
    have h5 : p * τ' ≤ τ := by linarith [h4, hτ'τ]
    linarith [h5]
  calc 2 * x ≤ 2 * (p * τ' / 4) := h1
    _ = p * τ' / 2 := h2
    _ ≤ τ := h3

/-- **Theorem 10.8 of Glock–Kühn–Osthus, reduced to the Kühn–Osthus Hamilton decomposition theorem.**

Assume `Work.Deep.GKO.KOStatement`.  Then `Work.Deep.GKO.GKOStatementFixed` holds: for every `p ∈ (0,1)` there are thresholds `ν₀, ε₀ > 0` such that every 2-uniform hypergraph `𝓖` on a large even number of vertices which is lower `(p,ε)`-regular with `ε ≤ ε₀`, has `Δ - δ ≤ νn` with `ν ≤ ν₀`, and whose minimum-degree vertex satisfies the paper's `(def_ineq)` condition, is `Δ`-edge-colourable.

This is the paper's §10.2 argument.  Fix `p ∈ (0,1)`; put `α := p/4`, let `τ := τ(α)` be the robustness threshold supplied by `KOStatement` for `α`, and put
`δ₀ := min (p/1000) (τ/1000)`, `ε₀ := min δ₀ (p*τ/8)`, and `ν₀ := min τ (ε₀^2 * α / 10^4)`.
(These are suggested values; any choice with `ε ≤ ε₀`, `ν ≤ ν₀` making `2√(12ν/αmin) ≤ ε₀`,
`2k ≤ (1/12)(p/2)n` and the room hypothesis of `robustExpander_lowerReg` hold will do —
the thresholds are existential so the proof is free to take them as small as necessary.)
Given `ν ≤ ν₀`, `ε ≤ ε₀`, a large even `n`, and a 2-uniform `𝓖` on `Fin n` satisfying the hypotheses, write `G := graphOf 𝓖`, `Δ := maxDeg G`, `d v := Nat.card (G.neighborSet v)`, and `αmin := min (p/2) (1/10)`.

1. `LowerReg G p ε` by `selfLowerRegular_iff_lowerReg`, hence `Δ ≥ (p-3ε)n`
   (`maxDeg_ge_of_lowerReg`), so `δ ≥ Δ - νn ≥ (p-3ε-ν)n ≥ (9/10)pn` by the hypothesis
   `Δ - d(v) ≤ νn` — this is the min-degree bound used in step 3.
2. The deficiencies `def v := Δ - d v` have even sum (from `Even n`), satisfy the Hakimi
   condition at *every* vertex (`(def_ineq)` at a minimum-degree vertex, which has the largest
   deficiency) and are `≤ ⌈νn⌉`; `exists_deficiencyMatchings_split` with `D := ⌈νn⌉` and
   `s := ⌊αmin*n/6⌋` produces nonempty matchings `M 1, …, M k`, each with at most `s` edges and
   `k ≤ 2⌈νn⌉(1 + n/(2s)) ≤ 12νn/αmin`, such that each vertex `v` is covered by exactly
   `def v` of them.
3. For each `i`, let `L i` be the Finset of vertices covered by `M i`.  Then `L i` is even and
   `2 ≤ |L i| ≤ 2s ≤ αmin*n/3 ≤ 2*αmin*n/5`, so `exists_spanningLinearForest` applies to the
   graph `G (i-1) := G \ (F 1 ⊔ ⋯ ⊔ F (i-1))` (with `F 1, …, F (i-1)` chosen inductively):
   every vertex of that graph has degree at least `d(v) - 2k ≥ (9/10)pn - (1/12)(p/2)n ≥ αmin*n`,
   and by `lowerReg_of_delete` applied to `H := F 1 ⊔ ⋯ ⊔ F (i-1)` (maximum degree `≤ 2k`) it is
   lower `(p, ε'')`-regular for `ε'' := max (2ε) (2√(2k/n)) ≤ ε₀`, by the choice of `ν₀` and `ε₀`.
4. Hence `Gk := G \ (F 1 ⊔ ⋯ ⊔ F k)` is `r`-regular with `r := Δ - 2k ≥ (3/4)pn ≥ αn`
   (`degree_delete_spanningLinearForest`, iterated: the degree removed at `v` is
   `2k - def v`), and it is lower `(p, ε'')`-regular, hence a robust `(ε'', τ)`-expander
   (`robustExpander_lowerReg`; the room hypothesis holds by `ε'' ≤ ε₀ ≤ pτ/8` and `n` large),
   and therefore a robust `(ν', τ)`-expander for a fixed `ν' ≤ ε''`
   (`RobustExpander.mono_nu`), which is what `KOStatement` needs.
5. If `r` is even, `KOStatement` gives a Hamilton decomposition of `Gk`, hence a 1-factorization
   with `r` perfect matchings (`oneFactorization_of_hamDecomp`).  If `r` is odd,
   `exists_perfectMatching_of_lowerReg` gives a perfect matching `M* ⊆ Gk`; colour it with one
   colour and apply the same argument to `Gk \ M*`, which is `(r-1)`-regular and still lower
   regular with parameter `≤ max (2ε'') (2√(1/n))` and minimum degree `≥ αmin*n`.
6. Each `F i` is a linear forest, hence decomposes into two matchings
   (`linearForest_matchingDecomposition`); `hasMatchingDecomposition_finsetSup` combines these
   `2k` matchings with the `r` (respectively `r - 1`, plus `M*`) matchings of the remainder into
   a partition of `E(G)` into `2k + r = Δ` matchings.
7. `colorable_of_matchingDecomposition` converts that partition into
   `𝓖.Colorable (hypergraphMaxDegree 𝓖)`, using `maxDeg G = hypergraphMaxDegree 𝓖`
   (`maxDegree_graphOf`); every `n ≥ N₀` can be chosen large enough for the finitely many
   largeness conditions above. -/
theorem gkoStatementFixed_of_KO (hKO : Work.Deep.GKO.KOStatement) :
    Work.Deep.GKO.GKOStatementFixed := by
  intro p hp0 hp1
  have hαpos0 : 0 < min (p / 2) (1 / 10) := lt_min (by linarith) (by norm_num)
  obtain ⟨τ, hτpos, hKOapp⟩ := hKO (min (p / 2) (1 / 10)) hαpos0
  set α : ℝ := min (p / 2) (1 / 10) with hαdef
  have hαpos : 0 < α := by rw [hαdef]; exact hαpos0
  have hαle10 : α ≤ 1 / 10 := by rw [hαdef]; exact min_le_right _ _
  have hαlep2 : α ≤ p / 2 := by rw [hαdef]; exact min_le_left _ _
  have hαlep : α ≤ p := by linarith [hαlep2, hp0]
  have hαle1 : α ≤ 1 := by linarith [hαle10]
  set τ' : ℝ := min τ 1 with hτ'def
  have hτ'pos : 0 < τ' := by rw [hτ'def]; exact lt_min hτpos one_pos
  have hτ'le1 : τ' ≤ 1 := by rw [hτ'def]; exact min_le_right _ _
  have hτ'leτ : τ' ≤ τ := by rw [hτ'def]; exact min_le_left _ _
  set ε₀ : ℝ := p * τ' * α / 10 ^ 20 with hε₀def
  set ν₀ : ℝ := min (α * p ^ 2 * τ' ^ 2 / 10 ^ 20) (α ^ 3 / 10 ^ 20) with hν₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; positivity
  have hν₀pos : 0 < ν₀ := by rw [hν₀def]; exact lt_min (by positivity) (by positivity)
  have hε₀lep : ε₀ ≤ p := by
    rw [hε₀def, div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 20)]
    have h1 : τ' * α ≤ 1 := prod2_le_one (le_of_lt hτ'pos) hτ'le1 (le_of_lt hαpos) hαle1
    nlinarith [h1, hp0]
  refine ⟨ν₀, ε₀, hν₀pos, hε₀pos, hε₀lep, ?_⟩
  intro ν ε hνpos hνle hεpos hεle
  have hν'pos : 0 < 2 * ε := by positivity
  have hν'leτ : 2 * ε ≤ τ := by
    have h1 : ε ≤ p * τ' * α / 10 ^ 20 := by rw [← hε₀def]; exact hεle
    have h2 : p * τ' * α / 10 ^ 20 ≤ τ / 2 := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 10^20) (by norm_num : (0:ℝ) < 2)]
      have h4 : p * τ' * α ≤ τ := by
        have hpα1 : p * α ≤ 1 := prod2_le_one (le_of_lt hp0) (le_of_lt hp1) (le_of_lt hαpos) hαle1
        nlinarith [hτ'leτ, hpα1, hτ'pos]
      nlinarith [h4]
    linarith [h1, h2]
  obtain ⟨n₀, hn₀⟩ := hKOapp (2 * ε) hν'pos hν'leτ
  have hε_small : ε ≤ p * τ' * α / 10 ^ 20 := by rw [← hε₀def]; exact hεle
  have hν_small1 : ν ≤ α * p ^ 2 * τ' ^ 2 / 10 ^ 20 := le_trans hνle (min_le_left _ _)
  have hν_small2 : ν ≤ α ^ 3 / 10 ^ 20 := le_trans hνle (min_le_right _ _)
  have hfacts : ∀ᶠ k : ℕ in Filter.atTop,
      (12 / α ≤ (k : ℝ)) ∧ (448 / (α * p) ≤ (k : ℝ)) ∧
      (14336 / (α * p ^ 2 * τ' ^ 2) ≤ (k : ℝ)) ∧ (2240000 / α ^ 3 ≤ (k : ℝ)) ∧
      (2240000 / (α * p ^ 2) ≤ (k : ℝ)) ∧ (4 / τ ≤ (k : ℝ)) ∧
      (1 / ε ≤ (k : ℝ)) ∧ (4 / p ≤ (k : ℝ)) ∧ (64 / (p ^ 2 * τ' ^ 2) ≤ (k : ℝ)) ∧
      (20000 / α ^ 2 ≤ (k : ℝ)) ∧ (20000 / p ^ 2 ≤ (k : ℝ)) ∧ (n₀ ≤ k) := by
    filter_upwards [eventually_ge_const (12 / α), eventually_ge_const (448 / (α * p)),
      eventually_ge_const (14336 / (α * p ^ 2 * τ' ^ 2)), eventually_ge_const (2240000 / α ^ 3),
      eventually_ge_const (2240000 / (α * p ^ 2)), eventually_ge_const (4 / τ),
      eventually_ge_const (1 / ε), eventually_ge_const (4 / p),
      eventually_ge_const (64 / (p ^ 2 * τ' ^ 2)), eventually_ge_const (20000 / α ^ 2),
      eventually_ge_const (20000 / p ^ 2),
      Filter.eventually_atTop.mpr ⟨n₀, fun k h => h⟩] with k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hfacts
  refine ⟨N₀, ?_⟩
  intro n hnN 𝓖 h2 hself hdev hneven hineq
  obtain ⟨hn12, hn448, hn14336, hn224a3, hn224ap2, hn2τ, hn1ε, hn4p, hn64, hnwα, hnwp, hn0'⟩ :=
    hN₀ n hnN
  have hpn : (0 : ℝ) < (n : ℝ) := by
    have h1 : (0 : ℝ) < 1 / ε := by positivity
    linarith [hn1ε, h1]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h2 : (1 : ℝ) ≤ 1 / ε := by
      rw [le_div_iff₀ hεpos]
      have h3 : ε ≤ 1 := by
        have h3' : ε ≤ p * τ' * α / 10 ^ 20 := hε_small
        have hpτα : p * τ' * α ≤ 1 := prod3_le_one (le_of_lt hp0) (le_of_lt hp1) (le_of_lt hτ'pos)
          hτ'le1 (le_of_lt hαpos) hαle1
        have h4 : p * τ' * α / 10 ^ 20 ≤ 1 := by
          rw [div_le_one (by norm_num : (0:ℝ) < 10^20)]
          linarith [hpτα]
        linarith [h3', h4]
      linarith [h3]
    linarith [hn1ε, h2]
  have hεn : (1 : ℝ) ≤ ε * (n : ℝ) := by
    rw [div_le_iff₀ hεpos] at hn1ε
    linarith [hn1ε]
  have hτpos : (0:ℝ) < τ := lt_of_lt_of_le hτ'pos hτ'leτ
  have hnposN : 0 < n := by
    have h : (0 : ℝ) < (n : ℝ) := by linarith [hn1]
    exact_mod_cast h
  -- the graph
  set G : SimpleGraph (Fin n) := graphOf 𝓖 with hGdef
  have hmaxG : maxDeg G = hypergraphMaxDegree 𝓖 := by
    rw [hGdef]; exact maxDegree_graphOf 𝓖 h2
  have hdegG : ∀ v : Fin n, Nat.card (G.neighborSet v) = degAt 𝓖 v := by
    intro v; rw [hGdef]; exact degree_graphOf 𝓖 h2 v
  have hlrG : LowerReg G p ε := by
    rw [hGdef]; exact (selfLowerRegular_iff_lowerReg 𝓖 p ε).mp hself
  have hdevG : ∀ v : Fin n, (maxDeg G : ℝ) - (Nat.card (G.neighborSet v) : ℝ) ≤ ν * (n : ℝ) := by
    intro v
    have h := hdev v
    rw [← hmaxG, ← hdegG v] at h
    exact h
  set Δ : ℕ := maxDeg G with hΔdef
  have hdeg_le_Δ : ∀ v : Fin n, Nat.card (G.neighborSet v) ≤ Δ := fun v => by
    rw [hΔdef]
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
      (f := fun u => Nat.card (G.neighborSet u)) (Finset.mem_univ v)
  have hε13 : ε ≤ 1 / 3 := by
    have h4 : ε ≤ p * τ' * α / 10 ^ 20 := hε_small
    have h5 : p * τ' * α / 10 ^ 20 ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 10^20) (by norm_num : (0:ℝ) < 3)]
      have hpτα : p * τ' * α ≤ 1 := prod3_le_one (le_of_lt hp0) (le_of_lt hp1) (le_of_lt hτ'pos)
        hτ'le1 (le_of_lt hαpos) hαle1
      linarith [hpτα]
    linarith [h4, h5]
  have hεp : ε ≤ p := by
    have h4 : ε ≤ p * τ' * α / 10 ^ 20 := hε_small
    have h5 : p * τ' * α / 10 ^ 20 ≤ p := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10^20)]
      have h6 : τ' * α ≤ 1 := prod2_le_one (le_of_lt hτ'pos) hτ'le1 (le_of_lt hαpos) hαle1
      nlinarith [h6, hp0]
    linarith [h4, h5]
  have hΔge : (p - 3 * ε) * (n : ℝ) ≤ (Δ : ℝ) := by
    have h6 : Δ = maxDeg G := hΔdef
    rw [h6]
    exact maxDeg_ge_of_lowerReg G hlrG hεn hε13 hεp (le_of_lt hp1) (by exact_mod_cast hn1 : 1 ≤ n)
  -- smallness of ν and ε
  have hν_p : ν ≤ α * p / 448 := by
    have h1 : α * p ^ 2 * τ' ^ 2 / 10 ^ 20 ≤ α * p / 448 := by
      have h2 : α * p ^ 2 * τ' ^ 2 ≤ α * p := by
        have h3 : p ^ 2 * τ' ^ 2 ≤ p := by
          have hp2 : p ^ 2 ≤ p := by nlinarith [hp0, le_of_lt hp1]
          have ht2 : τ' ^ 2 ≤ 1 := by nlinarith [hτ'pos, hτ'le1]
          calc p ^ 2 * τ' ^ 2 ≤ p * 1 := mul_le_mul hp2 ht2 (by positivity) (le_of_lt hp0)
            _ = p := by ring
        nlinarith [h3, hαpos]
      exact le_trans (div_le_div_of_nonneg_right h2 (by norm_num))
        (div_le_div_const_left (by positivity) (by norm_num) (by norm_num))
    linarith [hν_small1, h1]
  have hν_p2t : ν ≤ α * p ^ 2 * τ' ^ 2 / 14336 := by
    have h1 : α * p ^ 2 * τ' ^ 2 / 10 ^ 20 ≤ α * p ^ 2 * τ' ^ 2 / 14336 :=
      div_le_div_const_left (by positivity) (by norm_num) (by norm_num)
    linarith [hν_small1, h1]
  have hν_α3 : ν ≤ α ^ 3 / 2240000 := by
    have h1 : α ^ 3 / 10 ^ 20 ≤ α ^ 3 / 2240000 :=
      div_le_div_const_left (by positivity) (by norm_num) (by norm_num)
    linarith [hν_small2, h1]
  have hν_αp2 : ν ≤ α * p ^ 2 / 2240000 := by
    have h1 : α * p ^ 2 * τ' ^ 2 / 10 ^ 20 ≤ α * p ^ 2 / 2240000 := by
      have h2 : α * p ^ 2 * τ' ^ 2 ≤ α * p ^ 2 := by
        have ht2 : τ' ^ 2 ≤ 1 := by nlinarith [hτ'pos, hτ'le1]
        have hp2 : (0:ℝ) ≤ p ^ 2 := by positivity
        calc α * p ^ 2 * τ' ^ 2 ≤ α * p ^ 2 * 1 := by
              exact mul_le_mul_of_nonneg_left ht2 (by positivity)
          _ = α * p ^ 2 := by ring
      exact le_trans (div_le_div_of_nonneg_right h2 (by norm_num))
        (div_le_div_const_left (by positivity) (by norm_num) (by norm_num))
    linarith [hν_small1, h1]
  -- the four half-bounds for 2 * km
  have hc1 : 28 * ν / α ≤ (p / 8) / 2 := div28_le hαpos (by linarith [hν_p])
  have hc2 : 28 * ν / α ≤ (p ^ 2 * τ' ^ 2 / 256) / 2 :=
    div28_le hαpos (by linarith [hν_p2t])
  have hc3 : 28 * ν / α ≤ (α ^ 2 / 40000) / 2 := div28_le hαpos (by linarith [hν_α3])
  have hc4 : 28 * ν / α ≤ (p ^ 2 / 40000) / 2 := div28_le hαpos (by linarith [hν_αp2])
  -- the deficiency bound
  have h3εν : 3 * ε + ν ≤ p / 10 := by
    have hε20 : 3 * ε ≤ p / 20 := by
      have h2 : 3 * (p * τ' * α / 10 ^ 20) ≤ p / 20 := by
        have h5 : 3 * (p * τ' * α / 10 ^ 20) = 3 * (p * τ' * α) / 10 ^ 20 := by ring
        rw [h5, div_le_div_iff₀ (by norm_num : (0:ℝ) < 10^20) (by norm_num : (0:ℝ) < 20)]
        have h6 : τ' * α ≤ 1 := prod2_le_one (le_of_lt hτ'pos) hτ'le1 (le_of_lt hαpos) hαle1
        nlinarith [h6, hp0]
      linarith [hε_small, h2]
    have hν20 : ν ≤ p / 20 := by
      have h4 : α * p ^ 2 * τ' ^ 2 / 10 ^ 20 ≤ p / 20 := by
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 10^20) (by norm_num : (0:ℝ) < 20)]
        have h5 : τ' ^ 2 ≤ 1 := by nlinarith [hτ'pos, hτ'le1]
        have h7 : α * p ^ 2 * τ' ^ 2 ≤ α * p ^ 2 := by
          calc α * p ^ 2 * τ' ^ 2 ≤ α * p ^ 2 * 1 := by
                exact mul_le_mul_of_nonneg_left h5 (by positivity)
            _ = α * p ^ 2 := by ring
        have h8 : α * p ^ 2 ≤ p := by nlinarith [hαlep2, hαpos, hp0, sq_nonneg p, le_of_lt hp1]
        nlinarith [h7, h8]
      linarith [hν_small1, h4]
    linarith [hε20, hν20]
  have hd_low : ∀ v : Fin n, (9 / 10) * p * (n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
    intro v
    have h1 := hdevG v
    have h3 : (9 / 10) * p ≤ p - 3 * ε - ν := by linarith [h3εν]
    have h4 : (9 / 10) * p * n ≤ (p - 3 * ε - ν) * n :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hpn)
    have h5 : (p - 3 * ε - ν) * n = (p - 3 * ε) * n - ν * n := by ring
    have h6 : (p - 3 * ε) * n ≤ (Δ : ℝ) := hΔge
    have h7 : (Δ : ℝ) - ν * n ≤ (Nat.card (G.neighborSet v) : ℝ) := by linarith [h1]
    linarith [h4, h5.le, h5.ge, h6, h7]
  -- degree sequence: even total deficiency, Hakimi condition, bound
  have heven : Even (∑ v : Fin n, (Δ - Nat.card (G.neighborSet v))) := by
    have h1 : (∑ v : Fin n, (Δ - Nat.card (G.neighborSet v)))
        = (∑ v : Fin n, (maxDeg G - Nat.card (G.neighborSet v))) := by rw [hΔdef]
    rw [h1]; exact even_sum_deficiency G hneven
  have hD : ∀ v : Fin n, Δ - Nat.card (G.neighborSet v) ≤ ⌈ν * (n : ℝ)⌉₊ := by
    intro v
    have h1 : ((Δ - Nat.card (G.neighborSet v) : ℕ) : ℝ) = (Δ : ℝ) - (Nat.card (G.neighborSet v) : ℝ) :=
      Nat.cast_sub (hdeg_le_Δ v)
    have h2 : ((Δ - Nat.card (G.neighborSet v) : ℕ) : ℝ) ≤ ν * (n : ℝ) := by
      rw [h1, hΔdef]; exact hdevG v
    have h3 : ((Δ - Nat.card (G.neighborSet v) : ℕ) : ℝ) ≤ (⌈ν * (n : ℝ)⌉₊ : ℝ) :=
      le_trans h2 (Nat.le_ceil _)
    exact_mod_cast h3
  have hmax : ∀ v : Fin n, Δ - Nat.card (G.neighborSet v) ≤
      ∑ u ∈ Finset.univ.erase v, (Δ - Nat.card (G.neighborSet u)) := by
    intro v
    obtain ⟨w, hw1, hw2⟩ := hineq
    have hw1' : ∀ u : Fin n, Nat.card (G.neighborSet w) ≤ Nat.card (G.neighborSet u) := by
      intro u; rw [hdegG w, hdegG u]; exact hw1 u
    have hw2R : (Δ : ℝ) - (Nat.card (G.neighborSet w) : ℝ) ≤
        ∑ u ∈ Finset.univ.erase w, ((Δ : ℝ) - (Nat.card (G.neighborSet u) : ℝ)) := by
      have h := hw2
      rw [← hmaxG] at h
      simp only [← hdegG] at h
      exact h
    have hcast : (((∑ u ∈ Finset.univ.erase w, (Δ - Nat.card (G.neighborSet u)) : ℕ)) : ℝ)
        = ∑ u ∈ Finset.univ.erase w, ((Δ : ℝ) - (Nat.card (G.neighborSet u) : ℝ)) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun u _ => Nat.cast_sub (hdeg_le_Δ u))
    have hw2N : Δ - Nat.card (G.neighborSet w) ≤
        ∑ u ∈ Finset.univ.erase w, (Δ - Nat.card (G.neighborSet u)) := by
      have h1 : ((Δ - Nat.card (G.neighborSet w) : ℕ) : ℝ) = (Δ : ℝ) - (Nat.card (G.neighborSet w) : ℝ) :=
        Nat.cast_sub (hdeg_le_Δ w)
      have hw2R' : ((Δ - Nat.card (G.neighborSet w) : ℕ) : ℝ) ≤
          (((∑ u ∈ Finset.univ.erase w, (Δ - Nat.card (G.neighborSet u)) : ℕ)) : ℝ) := by
        rw [hcast, h1]
        exact hw2R
      exact Nat.cast_le.mp hw2R'
    exact hakimi_condition_of_minDegree G hw1' hw2N v
  -- the split matchings
  set s : ℕ := ⌊α * (n : ℝ) / 6⌋₊ with hsdef
  have hspos : 0 < s := by
    rw [hsdef, Nat.floor_pos]
    have h1 : (1 : ℝ) ≤ α * (n : ℝ) / 6 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 6)]
      rw [div_le_iff₀ hαpos] at hn12
      linarith [hn12]
    linarith [h1]
  obtain ⟨km, M, hkm_le, hMm, hMne, hMcard, hMcount⟩ :=
    exists_deficiencyMatchings_split (fun v : Fin n => Δ - Nat.card (G.neighborSet v))
      heven hmax hD hspos
  set L : Fin km → Finset (Fin n) := fun i => Finset.univ.filter (fun v => ∃ w, (M i).Adj v w)
    with hLdef
  have hLmem : ∀ (i : Fin km) (v : Fin n), v ∈ L i ↔ ∃ w, (M i).Adj v w := by
    intro i v; rw [hLdef]; simp
  have hLcard : ∀ i, (L i).card = 2 * Nat.card ((M i).edgeSet) := fun i =>
    matching_covered_card (hMm i)
  have hLeven : ∀ i, Even (L i).card := fun i => by
    rw [hLcard i]; exact even_two_mul _
  have hL2 : ∀ i, 2 ≤ (L i).card := fun i => by
    rw [hLcard i]; have := hMne i; omega
  have hLup : ∀ i, ((L i).card : ℝ) ≤ 2 * α * (n : ℝ) / 5 := by
    intro i
    have h1 : (L i).card ≤ 2 * s := by
      rw [hLcard i]; have := hMcard i; omega
    have h2 : (s : ℝ) ≤ α * (n : ℝ) / 6 := by rw [hsdef]; exact Nat.floor_le (by positivity)
    have h3 : ((L i).card : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast h1
    have h4 : 2 * (α * (n : ℝ) / 6) ≤ 2 * α * (n : ℝ) / 5 := by
      nlinarith [hαpos, hpn]
    linarith [h3, h2, h4]
  -- the bound on 2 * (km : ℝ)
  have hs_ge : (s : ℝ) ≥ α * (n : ℝ) / 12 := by
    rw [hsdef]
    have h2 : α * (n : ℝ) / 12 ≤ α * (n : ℝ) / 6 - 1 := by
      rw [div_le_iff₀ hαpos] at hn12
      rw [div_sub_one (by norm_num : (6:ℝ) ≠ 0)]
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 12) (by norm_num : (0:ℝ) < 6)]
      nlinarith [hn12]
    have h3 : α * (n : ℝ) / 6 - 1 ≤ ((⌊α * (n : ℝ) / 6⌋₊ : ℕ) : ℝ) := by
      have := Nat.sub_one_lt_floor (α * (n : ℝ) / 6)
      linarith [this]
    linarith [h2, h3]
  have hkmR : (km : ℝ) ≤ 14 * (ν * (n : ℝ) + 1) / α := by
    have hD' : (⌈ν * (n : ℝ)⌉₊ : ℝ) ≤ ν * n + 1 := by
      have := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ ν * n)
      linarith
    have hs0 : 0 < (s : ℝ) := by exact_mod_cast hspos
    have h7 : (km : ℝ) ≤ 2 * (⌈ν * (n : ℝ)⌉₊ : ℝ) * (1 + (n : ℝ) / (2 * (s : ℝ))) := by
      have h8 : ((2 * ⌈ν * (n : ℝ)⌉₊ * (1 + n / (2 * s)) : ℕ) : ℝ)
          = 2 * (⌈ν * (n : ℝ)⌉₊ : ℝ) * (1 + ((n / (2 * s) : ℕ) : ℝ)) := by push_cast; ring
      have h9 : ((n / (2 * s) : ℕ) : ℝ) ≤ (n : ℝ) / (2 * (s : ℝ)) := by
        have h := Nat.cast_div_le (α := ℝ) (m := n) (n := 2 * s)
        push_cast at h
        exact h
      have h10 : (km : ℝ) ≤ ((2 * ⌈ν * (n : ℝ)⌉₊ * (1 + n / (2 * s)) : ℕ) : ℝ) := by
        exact_mod_cast hkm_le
      rw [h8] at h10
      have h11 : 0 ≤ (⌈ν * (n : ℝ)⌉₊ : ℝ) := by positivity
      nlinarith [h10, h9, h11]
    have hn2s : (n : ℝ) / (2 * (s : ℝ)) ≤ 6 / α := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * (s : ℝ)) hαpos]
      nlinarith [hs_ge, hpn, hαpos, hs0]
    have h11 : (1 : ℝ) + (n : ℝ) / (2 * (s : ℝ)) ≤ 7 / α := by
      have h12 : (1 : ℝ) + 6 / α ≤ 7 / α := by
        have h13 : (1 : ℝ) ≤ 1 / α := by rw [le_div_iff₀ hαpos, one_mul]; exact hαle1
        have h14 : (6 : ℝ) / α + 1 / α = 7 / α := by ring
        linarith [h13, h14.le, h14.ge]
      linarith [hn2s, h12]
    have h13 : 2 * (⌈ν * (n : ℝ)⌉₊ : ℝ) ≤ 2 * (ν * n + 1) := by linarith [hD']
    have hp1' : (0 : ℝ) ≤ 1 + (n : ℝ) / (2 * (s : ℝ)) := by positivity
    have hp2' : (0 : ℝ) ≤ 2 * (ν * n + 1) := by positivity
    have h15 : 2 * (⌈ν * (n : ℝ)⌉₊ : ℝ) * (1 + (n : ℝ) / (2 * (s : ℝ)))
        ≤ 2 * (ν * n + 1) * (7 / α) := mul_le_mul h13 h11 hp1' hp2'
    have h16 : 2 * (ν * n + 1) * (7 / α) = 14 * (ν * n + 1) / α := by ring
    exact le_trans h7 (le_trans h15 h16.le)
  have h2k_p8 : 2 * (km : ℝ) ≤ (p / 8) * (n : ℝ) :=
    two_k_le hαpos hpn hkmR hc1 (by
      rw [div_le_iff₀ hαpos]
      have h := hn448
      rw [div_le_iff₀ (by positivity : (0:ℝ) < α * p)] at h
      nlinarith [h, hpn, hαpos, hp0])
  have h2k_pt : 2 * (km : ℝ) ≤ (p ^ 2 * τ' ^ 2 / 256) * (n : ℝ) :=
    two_k_le hαpos hpn hkmR hc2 (by
      rw [div_le_iff₀ hαpos]
      have h := hn14336
      rw [div_le_iff₀ (by positivity : (0:ℝ) < α * p ^ 2 * τ' ^ 2)] at h
      nlinarith [h, hpn, hαpos, hp0, hτ'pos])
  have h2k_α : 2 * (km : ℝ) ≤ (α ^ 2 / 40000) * (n : ℝ) :=
    two_k_le hαpos hpn hkmR hc3 (by
      rw [div_le_iff₀ hαpos]
      have h := hn224a3
      rw [div_le_iff₀ (by positivity : (0:ℝ) < α ^ 3)] at h
      nlinarith [h, hpn, hαpos])
  have h2k_p : 2 * (km : ℝ) ≤ (p ^ 2 / 40000) * (n : ℝ) :=
    two_k_le hαpos hpn hkmR hc4 (by
      rw [div_le_iff₀ hαpos]
      have h := hn224ap2
      rw [div_le_iff₀ (by positivity : (0:ℝ) < α * p ^ 2)] at h
      nlinarith [h, hpn, hαpos, hp0])
  -- ε''
  have h2ε_ok : 2 * ε ≤ min (min (p * τ' / 8) (α / 100)) (p / 100) :=
    le_min (le_min (two_eps_le8 hp0 (le_of_lt hp1) hτ'pos hτ'le1 hαpos hαle1 hε_small)
      (two_eps_leα hp0 (le_of_lt hp1) hτ'pos hτ'le1 hαpos hαle1 hε_small))
      (two_eps_lep hp0 (le_of_lt hp1) hτ'pos hτ'le1 hαpos hαle1 hε_small)
  have h2k_div : 2 * (km : ℝ) / (n : ℝ) ≤ (p * τ' / 8 / 2) ^ 2 ∧
      2 * (km : ℝ) / (n : ℝ) ≤ (α / 100 / 2) ^ 2 ∧
      2 * (km : ℝ) / (n : ℝ) ≤ (p / 100 / 2) ^ 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [div_le_iff₀ hpn]
      have h5 : (p * τ' / 8 / 2) ^ 2 = p ^ 2 * τ' ^ 2 / 256 := by ring
      rw [h5]; exact h2k_pt
    · rw [div_le_iff₀ hpn]
      have h5 : (α / 100 / 2) ^ 2 = α ^ 2 / 40000 := by ring
      rw [h5]; exact h2k_α
    · rw [div_le_iff₀ hpn]
      have h5 : (p / 100 / 2) ^ 2 = p ^ 2 / 40000 := by ring
      rw [h5]; exact h2k_p
  have h2sqrt_ok : 2 * Real.sqrt (2 * (km : ℝ) / (n : ℝ))
      ≤ min (min (p * τ' / 8) (α / 100)) (p / 100) := by
    refine le_min (le_min ?_ ?_) ?_
    · exact two_sqrt_le h2k_div.1 (by positivity)
    · exact two_sqrt_le h2k_div.2.1 (by positivity)
    · exact two_sqrt_le h2k_div.2.2 (by positivity)
  set ε'' : ℝ := max (2 * ε) (2 * Real.sqrt (2 * (km : ℝ) / (n : ℝ))) with hε''def
  have hε''pos : 0 < ε'' := by rw [hε''def]; exact lt_max_of_lt_left (by positivity)
  have hε''_le : ε'' ≤ min (min (p * τ' / 8) (α / 100)) (p / 100) := by
    rw [hε''def]; exact max_le h2ε_ok h2sqrt_ok
  have hε''_pτ : ε'' ≤ p * τ' / 8 :=
    le_trans hε''_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε''_α : ε'' ≤ α / 100 := le_trans hε''_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε''_p : ε'' ≤ p / 100 := le_trans hε''_le (min_le_right _ _)
  have hε''_en : (1 : ℝ) ≤ ε'' * (n : ℝ) := by
    have h1 : 2 * ε ≤ ε'' := by rw [hε''def]; exact le_max_left _ _
    have h3 : 2 * ε * (n : ℝ) ≤ ε'' * (n : ℝ) := mul_le_mul_of_nonneg_right h1 (le_of_lt hpn)
    have h4 : (2 : ℝ) ≤ 2 * ε * (n : ℝ) := by nlinarith [hεn]
    linarith [h3, h4]
  have hε''_2τ : 2 * ε'' ≤ τ :=
    eps2tau_aux hp0 (le_of_lt hp1) hτ'pos hτ'leτ hε''_pτ
  have hkey : ε'' < (p - ε'') * (τ - ε'') :=
    hkey_aux hp0 (le_of_lt hp1) hτpos hτ'leτ hτ'le1 hε''_pτ
  have hroom : (1 : ℝ) ≤ (τ - ε'' - ε'' / (p - ε'')) * (n : ℝ) := by
    have h2 : (2:ℝ) ≤ τ * (n : ℝ) := by
      rw [div_le_iff₀ hτpos] at hn2τ
      linarith [hn2τ]
    exact hroom_aux hp0 (le_of_lt hp1) hτpos hτ'leτ hτ'le1 hpn hε''_pτ h2
  -- the minimum degree of G dominates α * n + 2 * km
  have hminG : α * (n : ℝ) + 2 * (km : ℝ) ≤ (minDeg G : ℝ) := by
    refine le_minDeg G hnposN (fun v => ?_)
    have h1 : (9 / 10) * p * (n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := hd_low v
    exact hminG_aux hp0 hpn hαlep2 h1 h2k_p8 (by positivity)
  -- KO bounds
  have hΔ9 : (9 / 10) * p * (n : ℝ) ≤ (Δ : ℝ) :=
    hDelta9_aux hpn (le_of_lt hνpos) h3εν hΔge
  have hαKO : α * (n : ℝ) ≤ ((Δ - 2 * km : ℕ) : ℝ) := by
    have h1 : ((Δ - 2 * km : ℕ) : ℝ) ≥ (Δ : ℝ) - 2 * (km : ℝ) := by
      have h0 := nat_sub_cast_le Δ (2 * km)
      push_cast at h0
      exact h0
    have h2 : α * (n : ℝ) ≤ (Δ : ℝ) - 2 * (km : ℝ) :=
      halphaKO_aux hp0 hpn hαlep2 hΔ9 h2k_p8 (by positivity)
    linarith [h1, h2]
  have hαKO' : α * (n : ℝ) ≤ ((Δ - 2 * km - 1 : ℕ) : ℝ) := by
    have hb : ((Δ - 2 * km : ℕ) : ℝ) ≥ (Δ : ℝ) - 2 * (km : ℝ) := by
      have h0 := nat_sub_cast_le Δ (2 * km)
      push_cast at h0
      exact h0
    have h1 : ((Δ - 2 * km - 1 : ℕ) : ℝ) ≥ ((Δ - 2 * km : ℕ) : ℝ) - 1 := by
      have h0 := nat_sub_cast_le (Δ - 2 * km) 1
      push_cast at h0
      exact h0
    have h2 : α * (n : ℝ) + 1 ≤ (Δ : ℝ) - 2 * (km : ℝ) := by
      rw [div_le_iff₀ hp0] at hn4p
      exact halphaKO'_aux hp0 hpn hαlep2 hΔ9 h2k_p8 (by linarith [hn4p])
    linarith [hb, h1, h2]
  -- the edge-disjoint spanning linear forests
  obtain ⟨F, hF1, hF2⟩ := exists_edgeDisjoint_spanningLinearForests G L hnposN
    hlrG hεpos (le_refl _) hαpos hαle10 (by linarith [hε''_α, hαpos]) (by linarith [hε''_p, hp0])
    hε''_en hminG hLeven hL2 hLup
  set H : SimpleGraph (Fin n) := (Finset.univ : Finset (Fin km)).sup F with hHdef
  have hFle : ∀ i, F i ≤ G := fun i => le_trans (hF2 i) sdiff_le'
  have hHle : H ≤ G := by
    rw [hHdef]
    exact Finset.sup_le_iff.mpr (fun i _ => hFle i)
  have hdisjF : ∀ i j : Fin km, i ≠ j → Disjoint (F i).edgeSet (F j).edgeSet := by
    intro i j hij
    by_cases hlt : (i : ℕ) < (j : ℕ)
    · have h1 : F i ≤ (Finset.univ.filter (fun l : Fin km => l < j)).sup F :=
        Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
      have h2 : F j ≤ G \ (Finset.univ.filter (fun l : Fin km => l < j)).sup F := hF2 j
      have hd : Disjoint ((Finset.univ.filter (fun l : Fin km => l < j)).sup F).edgeSet
          (G \ (Finset.univ.filter (fun l : Fin km => l < j)).sup F).edgeSet := by
        rw [SimpleGraph.edgeSet_sdiff]
        exact disjoint_sdiff_right _ _
      exact Disjoint.mono (SimpleGraph.edgeSet_mono h1) (SimpleGraph.edgeSet_mono h2) hd
    · have hlt' : (j : ℕ) < (i : ℕ) := by
        have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
        omega
      have h1 : F j ≤ (Finset.univ.filter (fun l : Fin km => l < i)).sup F :=
        Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt'⟩)
      have h2 : F i ≤ G \ (Finset.univ.filter (fun l : Fin km => l < i)).sup F := hF2 i
      have hd : Disjoint ((Finset.univ.filter (fun l : Fin km => l < i)).sup F).edgeSet
          (G \ (Finset.univ.filter (fun l : Fin km => l < i)).sup F).edgeSet := by
        rw [SimpleGraph.edgeSet_sdiff]
        exact disjoint_sdiff_right _ _
      exact (Disjoint.mono (SimpleGraph.edgeSet_mono h1) (SimpleGraph.edgeSet_mono h2) hd).symm
  have hcover : ∀ v : Fin n, (Finset.univ.filter (fun i : Fin km => v ∈ L i)).card
      = Δ - Nat.card (G.neighborSet v) := by
    intro v
    rw [← natCard_subtype_filter_eq (fun i : Fin km => v ∈ L i)]
    have h1 : (fun i : Fin km => v ∈ L i) = (fun i : Fin km => ∃ w, (M i).Adj v w) := by
      funext i; exact propext (hLmem i v)
    rw [h1]
    exact hMcount v
  have hdegGk : ∀ v : Fin n, Nat.card ((G \ H).neighborSet v) = Δ - 2 * km := by
    intro v
    rw [hHdef, card_neighborSet_sdiff G _ hHle v, card_neighborSet_sup_eq_sum F v hdisjF]
    rw [Finset.sum_congr rfl (fun i _ => spanningLinearForest_degree_eq (hF1 i) v),
      sum_ite_mem_eq L v, hcover v]
    have h1 : Nat.card (G.neighborSet v) ≤ Δ := hdeg_le_Δ v
    have h2 : Δ - Nat.card (G.neighborSet v) ≤ 2 * km := by
      have h3 := hMcount v
      have h4 : Nat.card {i : Fin km // ∃ w, (M i).Adj v w} ≤ km := by
        rw [Nat.card_eq_fintype_card]
        calc Fintype.card {i : Fin km // ∃ w, (M i).Adj v w} ≤ Fintype.card (Fin km) :=
              Fintype.card_subtype_le _
          _ = km := Fintype.card_fin km
      omega
    omega
  have hregGk : IsRegularOf (G \ H) (Δ - 2 * km) := hdegGk
  have hHdeg : ∀ v : Fin n, Nat.card (H.neighborSet v) ≤ 2 * km := by
    intro v
    rw [hHdef, card_neighborSet_sup_eq_sum F v hdisjF]
    have h1 : ∀ i : Fin km, Nat.card ((F i).neighborSet v) ≤ 2 := fun i => by
      rw [spanningLinearForest_degree_eq (hF1 i) v]; split <;> norm_num
    calc ∑ i : Fin km, Nat.card ((F i).neighborSet v) ≤ ∑ _i : Fin km, 2 :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ = 2 * km := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hlrGk : LowerReg (G \ H) p ε'' := by
    have hη : (0:ℝ) ≤ 2 * (km : ℝ) / (n : ℝ) := by positivity
    have hHbd : ∀ v : Fin n,
        (Nat.card (H.neighborSet v) : ℝ) ≤ (2 * (km : ℝ) / (n : ℝ)) * (n : ℝ) := by
      intro v
      have h1 : (Nat.card (H.neighborSet v) : ℝ) ≤ 2 * (km : ℝ) := by
        exact_mod_cast hHdeg v
      have h3 : (2 * (km:ℝ) / (n:ℝ)) * (n:ℝ) = 2 * (km:ℝ) := by
        rw [div_mul_cancel₀]; exact ne_of_gt hpn
      linarith [h1, h3.le, h3.ge]
    have h0 : max (2 * ε) (2 * Real.sqrt (2 * (km : ℝ) / (n : ℝ))) ≤ ε'' := le_refl _
    exact LowerReg_mono_eps (lowerReg_of_delete G H hlrG hη hHbd) h0
  have hminGk : α * (n : ℝ) ≤ (minDeg (G \ H) : ℝ) := by
    refine le_minDeg _ hnposN (fun v => ?_)
    have h1 : Nat.card (G.neighborSet v) - Nat.card (H.neighborSet v)
        ≤ Nat.card ((G \ H).neighborSet v) := le_card_neighborSet_sdiff G H v
    have h2 : (Nat.card (G.neighborSet v) : ℝ) ≥ α * n + 2 * km := le_trans hminG (minDeg_le_degree G v)
    have h3 : (Nat.card (H.neighborSet v) : ℝ) ≤ 2 * (km : ℝ) := by exact_mod_cast hHdeg v
    have h4 : ((Nat.card (G.neighborSet v) - Nat.card (H.neighborSet v) : ℕ) : ℝ)
        ≥ (Nat.card (G.neighborSet v) : ℝ) - (Nat.card (H.neighborSet v) : ℝ) := nat_sub_cast_le _ _
    have h5 : (Nat.card ((G \ H).neighborSet v) : ℝ)
        ≥ ((Nat.card (G.neighborSet v) - Nat.card (H.neighborSet v) : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  -- robust expansion of the residual graph
  have hRE : RobustExpander (G \ H) (2 * ε) τ := by
    have h1 : RobustExpander (G \ H) ε'' τ :=
      robustExpander_lowerReg (G \ H) hlrGk hε''pos hτpos hε''_2τ hkey hroom
    exact RobustExpander.mono_nu (by rw [hε''def]; exact le_max_left _ _) h1
  -- the matching decomposition of the residual graph
  have hMDres : HasMatchingDecomposition (G \ H) (Δ - 2 * km) := by
    rcases Nat.even_or_odd (Δ - 2 * km) with hev | hod
    · have hham : HasHamiltonDecomposition (G \ H) := hn₀ n hn0' (G \ H) hRE _ hregGk hαKO hev
      exact hasMatchingDecomposition_of_oneFactorization
        (oneFactorization_of_hamDecomp (G \ H) hregGk hneven hham)
    · have h4εα : 4 * ε'' ≤ α := four_eps_le_alpha hε''_α hαpos
      have h6ε : 6 * ε'' ≤ 1 := six_eps_le_one hp0 hp1 hε''_p
      have hεp' : ε'' < p := eps_lt_p hp0 hε''_p
      have hnα12 : 12 ≤ (n : ℝ) * α := by
        rw [div_le_iff₀ hαpos] at hn12
        linarith [hn12]
      have hbig : (1 : ℝ) ≤ (α - 2 * ε'') * (n : ℝ) :=
        big_aux hαpos hpn hε''_α hnα12
      obtain ⟨Mstar, hMstar⟩ := exists_perfectMatching_of_lowerReg (G \ H) hneven hlrGk hε''pos
        hαpos h4εα h6ε hεp' hminGk hbig
      have hMstar_le : Mstar ≤ G \ H := hMstar.1
      have hMstar_perf : ∀ v : Fin n, ∃! w, Mstar.Adj v w := hMstar.2
      have hMstar1 : ∀ v : Fin n, Nat.card (Mstar.neighborSet v) = 1 := by
        intro v
        obtain ⟨w, hw, huniq⟩ := hMstar_perf v
        have hset : Mstar.neighborSet v = {w} := by
          ext x
          simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
          exact ⟨fun hx => huniq x hx, fun hx => hx ▸ hw⟩
        rw [hset, Nat.card_coe_set_eq, Set.ncard_singleton]
      have hreg' : IsRegularOf ((G \ H) \ Mstar) (Δ - 2 * km - 1) := by
        intro v
        rw [card_neighborSet_sdiff _ _ hMstar_le v, hdegGk v, hMstar1 v]
      have hEven' : Even (Δ - 2 * km - 1) := by
        rcases hod with ⟨t, ht⟩
        exact ⟨t, by omega⟩
      have hlr' : LowerReg ((G \ H) \ Mstar) p (max (2 * ε'') (2 * Real.sqrt (1 / (n:ℝ)))) := by
        refine lowerReg_of_delete (G \ H) Mstar hlrGk (by positivity) (fun v => ?_)
        have h1 : (Nat.card (Mstar.neighborSet v) : ℝ) = 1 := by rw [hMstar1 v]; norm_num
        have h2 : (1 : ℝ) / (n:ℝ) * (n:ℝ) = 1 := by rw [div_mul_cancel₀]; exact ne_of_gt hpn
        linarith [h1, h2.le, h2.ge]
      set εo : ℝ := max (2 * ε'') (2 * Real.sqrt (1 / (n:ℝ))) with hεodef
      have hεopos : 0 < εo := by rw [hεodef]; exact lt_max_of_lt_left (by linarith [hε''pos])
      have hb : 2 * Real.sqrt (1 / (n:ℝ)) ≤ p * τ' / 4 := by
        refine sqrt_inv_le hpn (by positivity) ?_
        have h64 : (4:ℝ) ≤ (p * τ' / 4) ^ 2 * (n:ℝ) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < p ^ 2 * τ' ^ 2)] at hn64
          have h5 : (p * τ' / 4) ^ 2 * (n:ℝ) = p ^ 2 * τ' ^ 2 * n / 16 := by ring
          rw [h5]; linarith [hn64]
        exact h64
      have hc : 2 * Real.sqrt (1 / (n:ℝ)) ≤ α / 50 := by
        refine sqrt_inv_le hpn (by positivity) ?_
        have h4 : (4:ℝ) ≤ (α / 50) ^ 2 * (n:ℝ) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < α ^ 2)] at hnwα
          have h5 : (α / 50) ^ 2 * (n:ℝ) = α ^ 2 * n / 2500 := by ring
          rw [h5]; linarith [hnwα]
        exact h4
      have hd : 2 * Real.sqrt (1 / (n:ℝ)) ≤ p / 50 := by
        refine sqrt_inv_le hpn (by positivity) ?_
        have h4 : (4:ℝ) ≤ (p / 50) ^ 2 * (n:ℝ) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < p ^ 2)] at hnwp
          have h5 : (p / 50) ^ 2 * (n:ℝ) = p ^ 2 * n / 2500 := by ring
          rw [h5]; linarith [hnwp]
        exact h4
      have hε1 : 2 * ε'' ≤ p * τ' / 4 := by linarith [hε''_pτ, hp0, hτ'pos]
      have hε2 : 2 * ε'' ≤ α / 50 := by linarith [hε''_α, hαpos]
      have hε3 : 2 * ε'' ≤ p / 50 := by linarith [hε''_p, hp0]
      have hεo_small : εo ≤ min (min (p * τ' / 4) (α / 50)) (p / 50) := by
        rw [hεodef]
        exact max_le (le_min (le_min hε1 hε2) hε3) (le_min (le_min hb hc) hd)
      have hεo_2τ : 2 * εo ≤ τ :=
        eps_o_2tau hp0 (le_of_lt hp1) hτ'pos hτ'leτ (le_trans hεo_small (le_trans (min_le_left _ _) (min_le_left _ _)))
      have hεo_key : εo < (p - εo) * (τ - εo) :=
        hkey_o_aux hp0 (le_of_lt hp1) hτpos hτ'leτ hτ'le1 (le_trans hεo_small (le_trans (min_le_left _ _) (min_le_left _ _)))
      have hεo_room : (1 : ℝ) ≤ (τ - εo - εo / (p - εo)) * (n : ℝ) := by
        have h2 : (4:ℝ) ≤ τ * (n : ℝ) := by
          rw [div_le_iff₀ hτpos] at hn2τ
          linarith [hn2τ]
        exact hroom_o_aux hp0 (le_of_lt hp1) hτpos hτ'leτ hτ'le1 hpn
          (le_trans hεo_small (le_trans (min_le_left _ _) (min_le_left _ _))) h2
      have hlr'o : LowerReg ((G \ H) \ Mstar) p εo := LowerReg_mono_eps hlr' le_rfl
      have h2εεo : 2 * ε ≤ εo := by
        have h1 : 2 * ε ≤ ε'' := by
          rw [hε''def]
          exact le_max_left (2 * ε) (2 * Real.sqrt (2 * (km : ℝ) / (n : ℝ)))
        have h5 : ε'' ≤ εo := by
          rw [hεodef]
          refine le_trans ?_ (le_max_left (2 * ε'') (2 * Real.sqrt (1 / (n : ℝ))))
          linarith [hε''pos]
        linarith [h1, h5]
      have hRE' : RobustExpander ((G \ H) \ Mstar) (2 * ε) τ :=
        RobustExpander.mono_nu h2εεo
          (robustExpander_lowerReg ((G \ H) \ Mstar) hlr'o hεopos hτpos hεo_2τ hεo_key hεo_room)
      have hham' : HasHamiltonDecomposition ((G \ H) \ Mstar) :=
        hn₀ n hn0' ((G \ H) \ Mstar) hRE' _ hreg' hαKO' hEven'
      have h1 : HasMatchingDecomposition ((G \ H) \ Mstar) (Δ - 2 * km - 1) :=
        hasMatchingDecomposition_of_oneFactorization
          (oneFactorization_of_hamDecomp ((G \ H) \ Mstar) hreg' hneven hham')
      have h2 : HasMatchingDecomposition Mstar 1 :=
        hasMatchingDecomposition_self_of_perfectMatching Mstar hMstar_perf
      have h3 : Disjoint Mstar.edgeSet ((G \ H) \ Mstar).edgeSet := by
        rw [SimpleGraph.edgeSet_sdiff]
        exact disjoint_sdiff_right _ _
      have h4 : HasMatchingDecomposition (Mstar ⊔ ((G \ H) \ Mstar)) (1 + (Δ - 2 * km - 1)) :=
        hasMatchingDecomposition_sup_of_disjoint h3 h2 h1
      have h5 : Mstar ⊔ ((G \ H) \ Mstar) = G \ H := sdiff_sup_self' hMstar_le
      have h6 : 1 + (Δ - 2 * km - 1) = Δ - 2 * km := by
        have h8 : (12:ℝ) ≤ α * (n:ℝ) := by
          rw [div_le_iff₀ hαpos] at hn12
          linarith [hn12]
        have h7 : (1:ℝ) ≤ ((Δ - 2 * km : ℕ) : ℝ) := by linarith [hαKO, h8]
        have h9 : 1 ≤ Δ - 2 * km := by exact_mod_cast h7
        omega
      rwa [h5, h6] at h4
  -- combine with the forests
  have hMDf : HasMatchingDecomposition H (∑ _i ∈ (Finset.univ : Finset (Fin km)), (2 : ℕ)) := by
    rw [hHdef]
    exact hasMatchingDecomposition_finsetSup Finset.univ F (fun _ => 2)
      (fun i _ j _ hij => hdisjF i j hij)
      (fun i _ => linearForest_matchingDecomposition (F i)
        (isLinearForest_of_spanning (hF1 i)))
  have hMT : (∑ _i ∈ (Finset.univ : Finset (Fin km)), (2 : ℕ)) = 2 * km := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hMDf' : HasMatchingDecomposition H (2 * km) := by rw [← hMT]; exact hMDf
  have hdisjFH : Disjoint H.edgeSet (G \ H).edgeSet := by
    rw [hHdef, SimpleGraph.edgeSet_sdiff]
    exact disjoint_sdiff_right _ _
  have hMDall : HasMatchingDecomposition (H ⊔ (G \ H)) (2 * km + (Δ - 2 * km)) :=
    hasMatchingDecomposition_sup_of_disjoint hdisjFH hMDf' hMDres
  have hsup : H ⊔ (G \ H) = G := sdiff_sup_self' hHle
  have hnum : 2 * km + (Δ - 2 * km) = Δ := by
    have h11 : ((2 * km : ℕ) : ℝ) = 2 * (km : ℝ) := by push_cast; ring
    have h14 : (2 * km : ℕ) ≤ Δ := by
      rw [← Nat.cast_le (α := ℝ), h11]
      have h15 : (p / 8) * (n:ℝ) ≤ (9/10) * p * n := by
        have h16 : (p / 8) * (n:ℝ) = (1/8) * (p * n) := by ring
        have h17 : (9/10) * p * (n:ℝ) = (9/10) * (p * n) := by ring
        rw [h16, h17]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith [h2k_p8, hΔ9, h15]
    omega
  have hMDG : HasMatchingDecomposition G Δ := by rw [hsup, hnum] at hMDall; exact hMDall
  -- conclude
  have hfin : HasMatchingDecomposition (graphOf 𝓖) (hypergraphMaxDegree 𝓖) := by
    rw [← hGdef, ← hmaxG]
    exact hMDG
  exact colorable_of_matchingDecomposition 𝓖 h2 hfin

end

end Work.Deep.GKO
