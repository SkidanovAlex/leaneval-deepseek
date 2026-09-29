import Mathlib
import Submission.Work.CNum.Jfun_defs

/-! # CNum: basic facts about the constants and norm factors used in `tD_bounds`

Elementary helpers shared by the proofs of the three parts of `tD_bounds`:
positivity/size of `rJ = 79/100` and `uJ = 115/143`, the exact values of the norms
`‖tanf ψ‖ = ‖tanf2 ψ‖ = uJ` (both are `i (w ψ - c₂)` and its negative), the
lower bound `1 - rJ ^ m ≤ ‖1 + (w ψ) ^ m‖` for `‖w ψ‖ ≤ rJ`, and the
monotonicity of powers.
-/

namespace Work.CNum

open Complex

lemma rJ_pos : 0 < rJ := by norm_num [rJ]

lemma rJ_lt_one : rJ < 1 := by norm_num [rJ]

lemma rJ_nonneg : 0 ≤ rJ := le_of_lt rJ_pos

lemma uJ_pos : 0 < uJ := by norm_num [uJ]

lemma uJ_nonneg : 0 ≤ uJ := le_of_lt uJ_pos

lemma one_sub_rJ_pos : 0 < 1 - rJ := by norm_num [rJ]

lemma norm_uJ_cast : ‖(uJ : ℂ)‖ = uJ := by
  have h : ‖(uJ : ℂ)‖ ^ 2 = uJ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (uJ : ℂ), uJ_pos]

lemma wf_sub_cJ (ψ : ℝ) : wf ψ - (cJ : ℂ) = (uJ : ℂ) * Complex.exp (Complex.I * (ψ : ℂ)) := by
  simp [wf]

lemma norm_I : ‖(Complex.I : ℂ)‖ = 1 := Complex.norm_I

lemma norm_tanf (ψ : ℝ) : ‖tanf ψ‖ = uJ := by
  simp only [tanf, wf_sub_cJ, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, norm_I, one_mul,
    norm_uJ_cast]

lemma norm_tanf2 (ψ : ℝ) : ‖tanf2 ψ‖ = uJ := by
  simp only [tanf2, norm_neg, wf_sub_cJ, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
    norm_uJ_cast]

lemma rJ_pow_le_one (m : ℕ) : rJ ^ m ≤ 1 :=
  pow_le_one₀ rJ_nonneg (le_of_lt rJ_lt_one) (n := m)

lemma rJ_pow_le_rJ {m : ℕ} (hm : 1 ≤ m) : rJ ^ m ≤ rJ := by
  calc rJ ^ m ≤ rJ ^ 1 := pow_le_pow_of_le_one rJ_nonneg (le_of_lt rJ_lt_one) hm
    _ = rJ := pow_one rJ

lemma one_sub_rJ_pow_pos {m : ℕ} (hm : 1 ≤ m) : 0 < 1 - rJ ^ m := by
  have : rJ ^ m < 1 := lt_of_le_of_lt (rJ_pow_le_rJ hm) rJ_lt_one
  linarith

lemma one_sub_rJ_pow_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ 1 - rJ ^ m :=
  le_of_lt (one_sub_rJ_pow_pos hm)

lemma norm_pow_wf_le (m : ℕ) {ψ : ℝ} (hψ : ‖wf ψ‖ ≤ rJ) : ‖(wf ψ) ^ m‖ ≤ rJ ^ m := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hψ m

lemma norm_one_add_pow_ge {m : ℕ} {ψ : ℝ} (hψ : ‖wf ψ‖ ≤ rJ) :
    1 - rJ ^ m ≤ ‖(1 : ℂ) + (wf ψ) ^ m‖ := by
  have h : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) + (wf ψ) ^ m‖ + ‖(wf ψ) ^ m‖ := by
    have := norm_add_le ((1 : ℂ) + (wf ψ) ^ m) (-((wf ψ) ^ m))
    simpa using this
  have h2 : ‖(wf ψ) ^ m‖ ≤ rJ ^ m := norm_pow_wf_le m hψ
  simp only [norm_one] at h
  linarith

lemma norm_one_add_pow_pos {m : ℕ} (hm : 1 ≤ m) {ψ : ℝ} (hψ : ‖wf ψ‖ ≤ rJ) :
    0 < ‖(1 : ℂ) + (wf ψ) ^ m‖ :=
  lt_of_lt_of_le (one_sub_rJ_pow_pos hm) (norm_one_add_pow_ge hψ)

lemma u1J_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ u1J m := by
  have h1 := one_sub_rJ_pow_pos hm
  have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h3 : 0 ≤ rJ ^ (m - 1) := pow_nonneg rJ_nonneg _
  have h4 : 0 ≤ 24 * (m : ℝ) * rJ ^ (m - 1) * uJ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h2) h3) uJ_nonneg
  exact div_nonneg h4 (le_of_lt h1)

lemma bndJ_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ bndJ m := by
  have h1 := one_sub_rJ_pow_pos hm
  have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h3 : 0 ≤ rJ ^ (m - 2) := pow_nonneg rJ_nonneg _
  have h3' : 0 ≤ rJ ^ (m - 1) := pow_nonneg rJ_nonneg _
  have h3'' : 0 ≤ rJ ^ (2 * m - 2) := pow_nonneg rJ_nonneg _
  have hml : 0 ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hA : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) * rJ ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m) := by
    apply div_nonneg _ (le_of_lt h1)
    exact mul_nonneg (mul_nonneg (mul_nonneg h2 hml) h3) (sq_nonneg uJ)
  have hB : 0 ≤ (m : ℝ) * rJ ^ (m - 1) * uJ / (1 - rJ ^ m) := by
    apply div_nonneg _ (le_of_lt h1)
    exact mul_nonneg (mul_nonneg h2 h3') uJ_nonneg
  have hC : 0 ≤ (m : ℝ) ^ 2 * rJ ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2 := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) h3'') (sq_nonneg uJ)
  have : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) * rJ ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m)
      + (m : ℝ) * rJ ^ (m - 1) * uJ / (1 - rJ ^ m)
      + (m : ℝ) ^ 2 * rJ ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2 := by linarith
  have := mul_nonneg (by norm_num : (0:ℝ) ≤ 24) this
  simpa [bndJ] using this

end Work.CNum
