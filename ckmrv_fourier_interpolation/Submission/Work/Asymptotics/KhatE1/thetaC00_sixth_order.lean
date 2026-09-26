import Mathlib
import Submission.Work.Asymptotics.KhatE1.cusp_L_fourth

namespace Work.Asymptotics.KhatE1

open Complex

/-- `e^{-π} ≤ 1/2`. -/
private lemma exp_neg_pi_le_half_sixth : Real.exp (-Real.pi) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hlt : Real.exp 1 < Real.exp Real.pi :=
    Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
  have hge : (2 : ℝ) ≤ Real.exp Real.pi := (h2.trans hlt).le
  calc Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hge
    _ = 1 / 2 := by norm_num

/-- **Sixth-order expansion of `θ₀₀`.**  For `z` with `1 ≤ Im z`, writing `q = exp(πiz)`,
`‖θ₀₀(z) - 1 - 2q - 2q⁴‖ ≤ 4 ‖q‖⁶`.

Indeed `θ₀₀(z) = 1 + 2∑_n F n` with `F n = exp(π i (n+1)² z)`, and the first two terms are
`F 0 = q`, `F 1 = q⁴`. With `r = ‖q‖ ≤ 1/2` we have `‖F (n+2)‖ = r^{(n+3)²} ≤ r^{6n+9}`,
so the tail is at most `r⁹/(1-r⁶)` and `2 r⁹/(1-r⁶) ≤ 4 r⁶` since `r ≤ 1/2`. -/
theorem thetaC00_sixth_order (z : ℂ) (hz : 1 ≤ z.im) :
    ‖Work.Kernels.LogLambda.thetaC00 z - 1 - 2 * Complex.exp (Real.pi * Complex.I * z)
        - 2 * (Complex.exp (Real.pi * Complex.I * z)) ^ 4‖
      ≤ 4 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 6 := by
  have hy : 0 < z.im := by linarith
  set q : ℂ := Complex.exp (Real.pi * Complex.I * z) with hq
  set r : ℝ := ‖q‖ with hr
  have hr_eq : r = Real.exp (-(Real.pi * z.im)) := by
    rw [hr, hq, Complex.norm_exp]
    congr 1
    rw [show (Real.pi : ℂ) * Complex.I * z = ((Real.pi : ℝ) : ℂ) * (Complex.I * z) by ring]
    rw [Complex.re_ofReal_mul, Complex.I_mul_re]
    ring
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ 1 / 2 := by
    rw [hr_eq]
    exact (Real.exp_le_exp.mpr (by nlinarith [hz, Real.pi_pos])).trans exp_neg_pi_le_half_sixth
  set F : ℕ → ℂ := fun n => Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * z) with hFdef
  have hsum : HasSum F ((jacobiTheta z - 1) / 2) := hasSum_nat_jacobiTheta hy
  have hSsum : Summable F := hsum.summable
  have hnorm_eq : ∀ m : ℕ, ‖F m‖ = r ^ ((m + 1) ^ 2) := by
    intro m
    have h1 : ‖F m‖ = Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * z.im)) := by
      rw [hFdef]
      exact Work.Residues.norm_cexp_pi_I_sq_mul' z m
    rw [h1, show ((m : ℝ) + 1) ^ 2 = (((m + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring]
    rw [show -(Real.pi * (((m + 1) ^ 2 : ℕ) : ℝ) * z.im)
        = (((m + 1) ^ 2 : ℕ) : ℝ) * (-(Real.pi * z.im)) by ring]
    rw [Real.exp_nat_mul, hr_eq]
  have hF0 : F 0 = q := by
    rw [hFdef, hq]; congr 1; push_cast; ring
  have hF1 : F 1 = q ^ 4 := by
    rw [hFdef, hq]
    norm_num
    rw [show Real.pi * Complex.I * 4 * z = ((4 : ℕ) : ℂ) * (Real.pi * Complex.I * z) by
      push_cast; ring]
    rw [Complex.exp_nat_mul]
  have hth : jacobiTheta z = 1 + 2 * (∑' n : ℕ, F n) := by
    simpa [hFdef] using jacobiTheta_eq_tsum_nat hy
  have hsplit : (∑' n : ℕ, F n) = F 0 + ∑' n : ℕ, F (n + 1) := hSsum.tsum_eq_zero_add
  have hS1 : Summable (fun n : ℕ => F (n + 1)) :=
    hSsum.comp_injective (fun a b h => Nat.add_right_cancel h)
  have hsplit2 : (∑' n : ℕ, F (n + 1)) = F 1 + ∑' n : ℕ, F (n + 2) :=
    hS1.tsum_eq_zero_add
  have hmain : Work.Kernels.LogLambda.thetaC00 z - 1 - 2 * q - 2 * q ^ 4
      = 2 * (∑' n : ℕ, F (n + 2)) := by
    rw [show Work.Kernels.LogLambda.thetaC00 z = jacobiTheta z from rfl, hth, hsplit, hsplit2,
      hF0, hF1]
    ring
  have hS2 : Summable (fun n : ℕ => F (n + 2)) :=
    hSsum.comp_injective (fun a b h => by omega)
  have hnorm_summ : Summable (fun n : ℕ => ‖F (n + 2)‖) := hS2.norm
  have hr6lt : r ^ 6 < 1 := by
    have h : r ^ 6 ≤ (1 / 2 : ℝ) ^ 6 := pow_le_pow_left₀ hr0 hr1 6
    norm_num at h ⊢
    linarith
  have hgeom : HasSum (fun n : ℕ => r ^ (6 * n + 9)) (r ^ 9 / (1 - r ^ 6)) := by
    have h := (hasSum_geometric_of_lt_one (show (0 : ℝ) ≤ r ^ 6 by positivity) hr6lt).mul_left
      (r ^ 9)
    have h' : HasSum (fun n : ℕ => r ^ 9 * (r ^ 6) ^ n) (r ^ 9 * (1 - r ^ 6)⁻¹) := h
    rw [div_eq_mul_inv]
    refine h'.congr_fun (fun n => ?_)
    rw [← pow_mul, ← pow_add, show 9 + 6 * n = 6 * n + 9 by ring]
  have hbound : ∀ n : ℕ, ‖F (n + 2)‖ ≤ r ^ (6 * n + 9) := by
    intro n
    rw [hnorm_eq (n + 2)]
    refine pow_le_pow_of_le_one hr0 (by linarith) ?_
    nlinarith
  have htail : ‖∑' n : ℕ, F (n + 2)‖ ≤ r ^ 9 / (1 - r ^ 6) := by
    refine le_trans (norm_tsum_le_tsum_norm hnorm_summ) ?_
    have h1 : (∑' n : ℕ, ‖F (n + 2)‖) ≤ ∑' n : ℕ, r ^ (6 * n + 9) :=
      Summable.tsum_le_tsum hbound hnorm_summ hgeom.summable
    rw [hgeom.tsum_eq] at h1
    exact h1
  have hd : 0 < 1 - r ^ 6 := by linarith
  have h9 : 2 * (r ^ 9 / (1 - r ^ 6)) ≤ 4 * r ^ 6 := by
    rw [show 2 * (r ^ 9 / (1 - r ^ 6)) = 2 * r ^ 9 / (1 - r ^ 6) by ring]
    rw [div_le_iff₀ hd]
    have h6 : r ^ 6 ≤ (1 / 2 : ℝ) ^ 6 := pow_le_pow_left₀ hr0 hr1 6
    have h3 : r ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := pow_le_pow_left₀ hr0 hr1 3
    nlinarith [pow_nonneg hr0 6, pow_nonneg hr0 3, h6, h3]
  have hfin : ‖Work.Kernels.LogLambda.thetaC00 z - 1 - 2 * q - 2 * q ^ 4‖ ≤ 4 * r ^ 6 := by
    rw [hmain, norm_mul, Complex.norm_ofNat]
    calc 2 * ‖∑' n : ℕ, F (n + 2)‖ ≤ 2 * (r ^ 9 / (1 - r ^ 6)) := by linarith [htail]
      _ ≤ 4 * r ^ 6 := h9
  simpa [hq, hr] using hfin

end Work.Asymptotics.KhatE1
