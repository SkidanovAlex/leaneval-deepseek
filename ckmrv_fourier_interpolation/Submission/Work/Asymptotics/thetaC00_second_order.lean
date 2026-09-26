import Mathlib
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Kernels.LogLambda.LogConstruct

namespace Work.Asymptotics

/-- `e^{-π} ≤ 1/2`; used to control the geometric tail. -/
private lemma exp_neg_pi_le_half : Real.exp (-Real.pi) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hlt : Real.exp 1 < Real.exp Real.pi :=
    Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
  have hge : (2 : ℝ) ≤ Real.exp Real.pi := (h2.trans hlt).le
  calc Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hge
    _ = 1 / 2 := by norm_num

/-- **Second order expansion of `θ₀₀` at the cusp**, in the form used in the paper:
`θ₀₀(z) = 1 + 2e^{πiz} + O(‖e^{πiz}‖⁴)` on `{im z ≥ 1}`, with the explicit constant `4`.

Indeed `θ₀₀(z) = 1 + 2∑_{n} e^{πi(n+1)²z}` and for `r = ‖e^{πiz}‖ = e^{-π im z} ≤ 1/2` the tail
is bounded by `2∑_n r^{2n+4} = 2r⁴/(1-r²) ≤ 4r⁴`. -/
theorem thetaC00_second_order (z : ℂ) (hz : 1 ≤ z.im) :
    ‖Work.Kernels.LogLambda.thetaC00 z - 1 - 2 * Complex.exp (Real.pi * Complex.I * z)‖
      ≤ 4 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 4 := by
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
    exact (Real.exp_le_exp.mpr (by nlinarith [hz, Real.pi_pos])).trans exp_neg_pi_le_half
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
  have htailterm : ∀ n : ℕ, ‖F (n + 1)‖ ≤ r ^ (2 * n + 4) := by
    intro n
    rw [hnorm_eq (n + 1)]
    have h2 : 2 * (n + 2) ≤ (n + 2) ^ 2 := by nlinarith
    calc r ^ ((n + 1 + 1) ^ 2) = r ^ ((n + 2) ^ 2) := by ring_nf
      _ ≤ r ^ (2 * (n + 2)) := pow_le_pow_of_le_one hr0 (by linarith) h2
      _ = r ^ (2 * n + 4) := by rw [show 2 * (n + 2) = 2 * n + 4 by ring]
  have hr2lt : r ^ 2 < 1 := by nlinarith [hr0, hr1]
  have hg : HasSum (fun n : ℕ => r ^ (2 * n + 4)) (r ^ 4 / (1 - r ^ 2)) := by
    have h := (hasSum_geometric_of_lt_one (show (0 : ℝ) ≤ r ^ 2 by positivity) hr2lt).mul_left
      (r ^ 4)
    have h' : HasSum (fun n : ℕ => r ^ 4 * (r ^ 2) ^ n) (r ^ 4 * (1 - r ^ 2)⁻¹) := h
    have h'' : r ^ 4 * (1 - r ^ 2)⁻¹ = r ^ 4 / (1 - r ^ 2) := by rw [div_eq_mul_inv]
    rw [h''] at h'
    refine h'.congr_fun (fun n => ?_)
    rw [← pow_mul, ← pow_add, show 4 + 2 * n = 2 * n + 4 by ring]
  have hsumtail : Summable (fun n : ℕ => ‖F (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) htailterm hg.summable
  have htail : ‖∑' n : ℕ, F (n + 1)‖ ≤ r ^ 4 / (1 - r ^ 2) := by
    refine le_trans (norm_tsum_le_tsum_norm hsumtail) ?_
    have h1 : (∑' n : ℕ, ‖F (n + 1)‖) ≤ ∑' n : ℕ, r ^ (2 * n + 4) :=
      Summable.tsum_le_tsum htailterm hsumtail hg.summable
    rw [hg.tsum_eq] at h1
    exact h1
  have hmain : Work.Kernels.LogLambda.thetaC00 z - 1 - 2 * q = 2 * ∑' n : ℕ, F (n + 1) := by
    have hth : jacobiTheta z = 1 + 2 * ∑' n : ℕ, F n := by
      simpa [hFdef] using jacobiTheta_eq_tsum_nat hy
    have hsplit : (∑' n : ℕ, F n) = F 0 + ∑' n : ℕ, F (n + 1) := hSsum.tsum_eq_zero_add
    have hF0 : F 0 = q := by
      rw [hFdef, hq]
      congr 1
      ring
    rw [show Work.Kernels.LogLambda.thetaC00 z = jacobiTheta z from rfl, hth, hsplit, hF0]
    ring
  rw [hmain, norm_mul, Complex.norm_ofNat]
  have hden : 0 < 1 - r ^ 2 := by linarith
  have hden2 : (1 - r ^ 2)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hr0, hr1]
  calc 2 * ‖∑' n : ℕ, F (n + 1)‖ ≤ 2 * (r ^ 4 / (1 - r ^ 2)) := by linarith [htail]
    _ = 2 * r ^ 4 * (1 - r ^ 2)⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ 2 * r ^ 4 * 2 := mul_le_mul_of_nonneg_left hden2 (by positivity)
    _ = 4 * r ^ 4 := by ring
    _ = 4 * ‖q‖ ^ 4 := by rw [hr]

end Work.Asymptotics
