/-
# The cusp expansion `Λ_S = -16 E + O(‖E‖³)`

The explicit branch `Λ_S(z) = 4 log θ₀₁(z) - 4 log θ₀₀(z)` of `log λ_S` (CKMRV, Section 2.1.5)
satisfies, on `{im z ≥ 1}`,

  `Λ_S(z) = -16 E(z) + O(‖E(z)‖³)`,  `E(z) = e^{πiz}`,

which is the form of the expansion used in the paper: it is the second-order cusp expansion of
`𝓛_S`, whose first nonzero term is `-16 E` because the two `q`-linear contributions of `θ₀₁` and
`θ₀₀` combine and the `q²` contributions cancel inside the logarithm.

The proof proceeds as follows.  From the defining theta series (`jacobiTheta_eq_tsum_nat`) one
gets the two expansions

  `θ₀₀ = 1 + 2E + O(‖E‖⁴)`,  `θ₀₁ = 1 - 2E + O(‖E‖⁴)`

(the second because `θ₀₁ τ = θ₀₀(τ+1)`).  Writing `a = θ₀₁ - 1`, `b = θ₀₀ - 1` and using
`log(1+z) = z - z²/2 + z³/3 + O(‖z‖⁴)` (Mathlib's `Complex.norm_log_sub_logTaylor_le`) gives

  `Λ_S + 16E = 4(log(1+a) - log(1+b) + 4E)`
  `          = 4[(a - b + 4E) - (a² - b²)/2 + (a³ - b³)/3 + O(‖E‖⁴)]`,

and since `a + 2E = O(‖E‖⁴)`, `b - 2E = O(‖E‖⁴)` each bracket is `O(‖E‖³)`:
`a - b + 4E = O(‖E‖⁴)`, `a² - b² = (a-b)(a+b) = O(‖E‖⁵)` and
`a³ - b³ = (a-b)(a²+ab+b²) = O(‖E‖³)`.
-/
import Mathlib
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Kernels.LogLambda.LambdaLaws

namespace Work.Residues

noncomputable section

/-! ## Elementary constant bounds -/

private lemma exp_neg_pi_le_half : Real.exp (-Real.pi) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  have h3e : (2 : ℝ) ≤ Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [h2, Real.exp_pos 1]
  have h3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  have hπ : (2 : ℝ) ≤ Real.exp Real.pi := h3e.trans (Real.exp_le_exp.mpr h3)
  calc Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hπ
    _ = 1 / 2 := by norm_num

private lemma exp_neg_pi_le_eighth : Real.exp (-Real.pi) ≤ 1 / 8 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  have h3e : (8 : ℝ) ≤ Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [h2, Real.exp_pos 1]
  have h3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  have hπ : (8 : ℝ) ≤ Real.exp Real.pi := h3e.trans (Real.exp_le_exp.mpr h3)
  calc Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
    _ ≤ (8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hπ
    _ = 1 / 8 := by norm_num

/-! ## The fourth-order cusp expansions of `θ₀₀` and `θ₀₁` -/

/-- `θ₀₀(τ) = 1 + 2E + O(‖E‖⁴)` with the explicit constant `4`. -/
private lemma theta00_sub_expansion (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ‖ ≤ 4 * ‖Ept τ‖ ^ 4 := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖Ept τ‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact norm_Ept_lt_one τ
  have hy : 0 < (τ : ℂ).im := by simpa using τ.im_pos
  have hsum : HasSum
      (fun n : ℕ => Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ)))
      ((Work.Kernels.theta00Fun τ - 1) / 2) := by
    simpa [Work.Kernels.theta00Fun] using hasSum_nat_jacobiTheta hy
  have htheta : Work.Kernels.theta00Fun τ
      = 1 + 2 * (∑' n : ℕ, Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ))) := by
    have h := jacobiTheta_eq_tsum_nat hy
    rw [show Work.Kernels.theta00Fun τ = jacobiTheta (τ : ℂ) from rfl, h]
  set F : ℕ → ℂ := fun n => Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ))
    with hFdef
  have hSsum : Summable F := hsum.summable
  have hsplit : (∑' n : ℕ, F n) = F 0 + ∑' n : ℕ, F (n + 1) := hSsum.tsum_eq_zero_add
  have hF0 : F 0 = Ept τ := by simp [hFdef, Ept]
  have hnorm_eq : ∀ m : ℕ, ‖F m‖ = r ^ ((m + 1) ^ 2) := by
    intro m
    have h1 : ‖F m‖ = Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * τ.im)) := by
      simp only [hFdef]
      rw [norm_cexp_pi_I_sq_mul' (τ : ℂ) m, UpperHalfPlane.coe_im]
    rw [h1, show ((m : ℝ) + 1) ^ 2 = (((m + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring,
      exp_neg_pi_im_nat_mul, ← hr]
  have htailterm : ∀ n : ℕ, ‖F (n + 1)‖ ≤ r ^ (n + 4) := by
    intro n
    rw [hnorm_eq (n + 1)]
    have h2 : n + 4 ≤ (n + 2) ^ 2 := by nlinarith
    calc r ^ ((n + 1 + 1) ^ 2) = r ^ ((n + 2) ^ 2) := by ring_nf
      _ ≤ r ^ (n + 4) := pow_le_pow_of_le_one hr0 (le_of_lt hr1) h2
  have hg : HasSum (fun n : ℕ => r ^ (n + 4)) (r ^ 4 / (1 - r)) := by
    have h0 : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
      hasSum_geometric_of_lt_one hr0 hr1
    have h1 := h0.mul_left (r ^ 4)
    have h2 : r ^ 4 * (1 - r)⁻¹ = r ^ 4 / (1 - r) := by rw [div_eq_mul_inv]
    rw [h2] at h1
    refine h1.congr_fun (fun n => ?_)
    rw [mul_comm, pow_add]
  have hsumtail : Summable (fun n : ℕ => ‖F (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) htailterm hg.summable
  have htail : ‖∑' n : ℕ, F (n + 1)‖ ≤ r ^ 4 / (1 - r) := by
    refine le_trans (norm_tsum_le_tsum_norm hsumtail) ?_
    have h1 : (∑' n : ℕ, ‖F (n + 1)‖) ≤ ∑' n : ℕ, r ^ (n + 4) :=
      Summable.tsum_le_tsum htailterm hsumtail hg.summable
    rwa [hg.tsum_eq] at h1
  have hmain : Work.Kernels.theta00Fun τ - 1 - 2 * Ept τ = 2 * ∑' n : ℕ, F (n + 1) := by
    rw [htheta, hsplit, hF0]; ring
  have hr2 : r ≤ 1 / 2 := by
    rw [hr]; exact (norm_Ept_le_exp_neg_pi τ hτ).trans exp_neg_pi_le_half
  have hden : 0 < 1 - r := by linarith
  have hden2 : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]; linarith
  have htail2 : ‖∑' n : ℕ, F (n + 1)‖ ≤ 2 * r ^ 4 := by
    calc ‖∑' n : ℕ, F (n + 1)‖ ≤ r ^ 4 / (1 - r) := htail
      _ = r ^ 4 * (1 - r)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ r ^ 4 * 2 := mul_le_mul_of_nonneg_left hden2 (by positivity)
      _ = 2 * r ^ 4 := by ring
  rw [hmain, norm_mul, Complex.norm_ofNat]
  calc 2 * ‖∑' n : ℕ, F (n + 1)‖ ≤ 2 * (2 * r ^ 4) := by linarith [htail2]
    _ = 4 * r ^ 4 := by ring
    _ = 4 * ‖Ept τ‖ ^ 4 := by rw [hr]

/-- `θ₀₁(τ) = 1 - 2E + O(‖E‖⁴)` with the explicit constant `4`. -/
private lemma theta01_sub_expansion (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.theta01Fun τ - 1 + 2 * Ept τ‖ ≤ 4 * ‖Ept τ‖ ^ 4 := by
  have hτ' : (1 : ℝ) ≤ (ModularGroup.T • τ).im := by
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.vadd_im]; exact hτ
  have h := theta00_sub_expansion (ModularGroup.T • τ) hτ'
  rw [Work.Kernels.theta00Fun_T τ, Ept_T τ, norm_neg] at h
  have h' : ‖Work.Kernels.theta01Fun τ - 1 + 2 * Ept τ‖
      = ‖Work.Kernels.theta01Fun τ - 1 - 2 * (-Ept τ)‖ := by
    congr 1; ring
  rw [h']; exact h

/-! ## The logarithm remainder and the abstract expansion step -/

/-- `log(1+z) = z - z²/2 + z³/3 + O(‖z‖⁴)` with constant `1/2`, for `‖z‖ ≤ 1/2`. -/
private lemma log_taylor_remainder (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)‖ ≤ (1 / 2) * ‖z‖ ^ 4 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have h := Complex.norm_log_sub_logTaylor_le 3 hz1
  have hlt : Complex.logTaylor 4 z = z - z ^ 2 / 2 + z ^ 3 / 3 := by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    ring
  rw [hlt] at h
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hpos : 0 ≤ ‖z‖ ^ 4 := by positivity
  have hstep : ‖z‖ ^ 4 * (1 - ‖z‖)⁻¹ / ((↑(3 : ℕ) : ℝ) + 1) ≤ (1 / 2) * ‖z‖ ^ 4 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (↑(3 : ℕ) : ℝ) + 1)]
    nlinarith [h2, hpos]
  calc ‖Complex.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)‖
      ≤ ‖z‖ ^ (3 + 1) * (1 - ‖z‖)⁻¹ / ((↑(3 : ℕ) : ℝ) + 1) := h
    _ = ‖z‖ ^ 4 * (1 - ‖z‖)⁻¹ / ((↑(3 : ℕ) : ℝ) + 1) := by norm_num
    _ ≤ (1 / 2) * ‖z‖ ^ 4 := hstep

/-- The abstract expansion step: if `a + 2q` and `b - 2q` are both `O(‖q‖⁴)` then
`log(1+a) - log(1+b) + 4q = O(‖q‖³)`, with an explicit constant. -/
private lemma log_expansion_step {a b q : ℂ} {M r : ℝ}
    (hM : 0 < M) (hM4 : M ≤ 4) (hr0 : 0 ≤ r) (hr : ‖q‖ ≤ r) (hr8 : r ≤ 1 / 8)
    (ha : ‖a + 2 * q‖ ≤ M * r ^ 4) (hb : ‖b - 2 * q‖ ≤ M * r ^ 4) :
    ‖Complex.log (1 + a) - Complex.log (1 + b) + 4 * q‖ ≤ 200 * r ^ 3 := by
  have hr1 : r ≤ 1 := by linarith
  have hr4 : (0 : ℝ) ≤ r ^ 4 := by positivity
  have hMle : M * r ^ 4 ≤ 4 * r ^ 4 := mul_le_mul_of_nonneg_right hM4 hr4
  have h4r : 4 * r ^ 4 ≤ r := by nlinarith [pow_le_pow_left₀ hr0 hr8 3, hr0, sq_nonneg r]
  have h8r : 8 * r ^ 4 ≤ r := by nlinarith [pow_le_pow_left₀ hr0 hr8 3, hr0, sq_nonneg r]
  have hr43 : r ^ 4 ≤ r ^ 3 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hr53 : r ^ 5 ≤ r ^ 3 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hMr : M * r ^ 4 ≤ r := by linarith [hMle, h4r]
  have h2Mr : 2 * M * r ^ 4 ≤ r := by nlinarith [hMle, h8r]
  have hna : ‖a‖ ≤ 3 * r := by
    have h1 : ‖a‖ ≤ ‖a + 2 * q‖ + ‖2 * q‖ := by
      have h : ‖a‖ = ‖(a + 2 * q) - 2 * q‖ := by congr 1; ring
      rw [h]; exact norm_sub_le _ _
    have h2 : ‖(2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul]; norm_num
    rw [h2] at h1
    linarith [h1, ha, hMr, hr]
  have hnb : ‖b‖ ≤ 3 * r := by
    have h1 : ‖b‖ ≤ ‖b - 2 * q‖ + ‖2 * q‖ := by
      have h : ‖b‖ = ‖(b - 2 * q) + 2 * q‖ := by congr 1; ring
      rw [h]; exact norm_add_le _ _
    have h2 : ‖(2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul]; norm_num
    rw [h2] at h1
    linarith [h1, hb, hMr, hr]
  have hra := log_taylor_remainder a (by linarith : ‖a‖ ≤ 1 / 2)
  have hrb := log_taylor_remainder b (by linarith : ‖b‖ ≤ 1 / 2)
  have hra' : ‖Complex.log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3)‖ ≤ (81 / 2) * r ^ 3 := by
    refine le_trans hra ?_
    have h2 : (1 / 2) * ‖a‖ ^ 4 ≤ (1 / 2) * (3 * r) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg a) hna 4) (by norm_num)
    calc (1 / 2) * ‖a‖ ^ 4 ≤ (1 / 2) * (3 * r) ^ 4 := h2
      _ = (81 / 2) * r ^ 4 := by ring
      _ ≤ (81 / 2) * r ^ 3 := by linarith [hr43]
  have hrb' : ‖Complex.log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3)‖ ≤ (81 / 2) * r ^ 3 := by
    refine le_trans hrb ?_
    have h2 : (1 / 2) * ‖b‖ ^ 4 ≤ (1 / 2) * (3 * r) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg b) hnb 4) (by norm_num)
    calc (1 / 2) * ‖b‖ ^ 4 ≤ (1 / 2) * (3 * r) ^ 4 := h2
      _ = (81 / 2) * r ^ 4 := by ring
      _ ≤ (81 / 2) * r ^ 3 := by linarith [hr43]
  have hab4q : ‖a - b + 4 * q‖ ≤ 2 * M * r ^ 4 := by
    have h1 : a - b + 4 * q = (a + 2 * q) - (b - 2 * q) := by ring
    rw [h1]
    calc ‖(a + 2 * q) - (b - 2 * q)‖ ≤ ‖a + 2 * q‖ + ‖b - 2 * q‖ := norm_sub_le _ _
      _ ≤ M * r ^ 4 + M * r ^ 4 := by linarith
      _ = 2 * M * r ^ 4 := by ring
  have h4q : ‖a - b + 4 * q‖ ≤ 8 * r ^ 3 := by
    have h : 2 * M * r ^ 4 ≤ 8 * r ^ 3 := by nlinarith [hMle, hr43]
    linarith [hab4q, h]
  have hab : ‖a - b‖ ≤ 5 * r := by
    have h1 : ‖a - b‖ ≤ ‖a - b + 4 * q‖ + ‖4 * q‖ := by
      have h : ‖a - b‖ = ‖(a - b + 4 * q) - 4 * q‖ := by congr 1; ring
      rw [h]; exact norm_sub_le _ _
    have h2 : ‖(4 : ℂ) * q‖ = 4 * ‖q‖ := by rw [norm_mul]; norm_num
    rw [h2] at h1
    linarith [h1, hab4q, h2Mr, hr]
  have hab2 : ‖a + b‖ ≤ 2 * M * r ^ 4 := by
    have h1 : a + b = (a + 2 * q) + (b - 2 * q) := by ring
    rw [h1]
    calc ‖(a + 2 * q) + (b - 2 * q)‖ ≤ ‖a + 2 * q‖ + ‖b - 2 * q‖ := norm_add_le _ _
      _ ≤ M * r ^ 4 + M * r ^ 4 := by linarith
      _ = 2 * M * r ^ 4 := by ring
  have hsq : ‖a ^ 2 - b ^ 2‖ ≤ 40 * r ^ 3 := by
    have h1 : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [h1, norm_mul]
    have h2 : ‖a - b‖ * ‖a + b‖ ≤ (5 * r) * (2 * M * r ^ 4) :=
      mul_le_mul hab hab2 (norm_nonneg _) (by positivity)
    have h3 : (5 * r) * (2 * M * r ^ 4) ≤ 40 * r ^ 3 := by nlinarith [hr53, hr0, hM4, hM, hr4]
    linarith [h2, h3]
  have hsqsum : ‖a ^ 2 + a * b + b ^ 2‖ ≤ 27 * r ^ 2 := by
    have h2a : ‖a ^ 2‖ ≤ (3 * r) ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg a) hna 2
    have h2b : ‖b ^ 2‖ ≤ (3 * r) ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg b) hnb 2
    have h2ab : ‖a * b‖ ≤ (3 * r) * (3 * r) := by
      rw [norm_mul]; exact mul_le_mul hna hnb (norm_nonneg b) (by positivity)
    have htri : ‖a ^ 2 + a * b + b ^ 2‖ ≤ ‖a ^ 2‖ + ‖a * b‖ + ‖b ^ 2‖ := by
      have h1 : a ^ 2 + a * b + b ^ 2 = (a ^ 2 + a * b) + b ^ 2 := by ring
      rw [h1]
      have hx := norm_add_le (a ^ 2 + a * b) (b ^ 2)
      have hy := norm_add_le (a ^ 2) (a * b)
      linarith
    have h5 : ‖a ^ 2‖ + ‖a * b‖ + ‖b ^ 2‖ ≤ (3 * r) ^ 2 + (3 * r) * (3 * r) + (3 * r) ^ 2 :=
      by linarith
    have h6 : (3 * r) ^ 2 + (3 * r) * (3 * r) + (3 * r) ^ 2 = 27 * r ^ 2 := by ring
    linarith [htri, h5, h6]
  have hcube : ‖a ^ 3 - b ^ 3‖ ≤ 135 * r ^ 3 := by
    have h1 : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    rw [h1, norm_mul]
    have h2 := mul_le_mul hab hsqsum (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 5 * r)
    calc ‖a - b‖ * ‖a ^ 2 + a * b + b ^ 2‖ ≤ (5 * r) * (27 * r ^ 2) := h2
      _ = 135 * r ^ 3 := by ring
  have hS : ‖(a - a ^ 2 / 2 + a ^ 3 / 3) - (b - b ^ 2 / 2 + b ^ 3 / 3) + 4 * q‖ ≤ 73 * r ^ 3 := by
    have heq : (a - a ^ 2 / 2 + a ^ 3 / 3) - (b - b ^ 2 / 2 + b ^ 3 / 3) + 4 * q
        = (a - b + 4 * q) - (a ^ 2 - b ^ 2) / 2 + (a ^ 3 - b ^ 3) / 3 := by ring
    rw [heq]
    have h2 : ‖(a ^ 2 - b ^ 2) / 2‖ ≤ 20 * r ^ 3 := by
      rw [norm_div]; norm_num; linarith [hsq]
    have h3 : ‖(a ^ 3 - b ^ 3) / 3‖ ≤ 45 * r ^ 3 := by
      rw [norm_div]; norm_num; linarith [hcube]
    have h1 := norm_add_le ((a - b + 4 * q) - (a ^ 2 - b ^ 2) / 2) ((a ^ 3 - b ^ 3) / 3)
    have h1' := norm_sub_le (a - b + 4 * q) ((a ^ 2 - b ^ 2) / 2)
    linarith [h1, h1', h2, h3, h4q]
  have key : Complex.log (1 + a) - Complex.log (1 + b) + 4 * q
      = (Complex.log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3))
        - (Complex.log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3))
        + ((a - a ^ 2 / 2 + a ^ 3 / 3) - (b - b ^ 2 / 2 + b ^ 3 / 3) + 4 * q) := by ring
  rw [key]
  have h1 := norm_add_le ((Complex.log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3))
      - (Complex.log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3)))
      ((a - a ^ 2 / 2 + a ^ 3 / 3) - (b - b ^ 2 / 2 + b ^ 3 / 3) + 4 * q)
  have h1' := norm_sub_le (Complex.log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3))
      (Complex.log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3))
  nlinarith [h1, h1', hra', hrb', hS, pow_nonneg hr0 3]

/-! ## The main expansion -/

theorem LamSExpansion :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.LogLambda.LamS (τ : ℂ) + 16 * Work.Residues.Ept τ‖ ≤
        C * ‖Work.Residues.Ept τ‖ ^ 3 := by
  refine ⟨800, by norm_num, fun τ hτ => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖Ept τ‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr8 : r ≤ 1 / 8 := by
    rw [hr]; exact (norm_Ept_le_exp_neg_pi τ hτ).trans exp_neg_pi_le_eighth
  have ha : ‖(Work.Kernels.theta01Fun τ - 1) + 2 * Ept τ‖ ≤ 4 * r ^ 4 := by
    rw [hr]; exact theta01_sub_expansion τ hτ
  have hb : ‖(Work.Kernels.theta00Fun τ - 1) - 2 * Ept τ‖ ≤ 4 * r ^ 4 := by
    rw [hr]; exact theta00_sub_expansion τ hτ
  have hkey := log_expansion_step (a := Work.Kernels.theta01Fun τ - 1)
    (b := Work.Kernels.theta00Fun τ - 1) (q := Ept τ) (M := 4) (r := r)
    (by norm_num) (le_refl 4) hr0 (by rw [hr]) hr8 ha hb
  have hlog1 : Complex.log (1 + (Work.Kernels.theta01Fun τ - 1))
      = Complex.log (Work.Kernels.theta01Fun τ) := by congr 1; ring
  have hlog0 : Complex.log (1 + (Work.Kernels.theta00Fun τ - 1))
      = Complex.log (Work.Kernels.theta00Fun τ) := by congr 1; ring
  rw [hlog1, hlog0] at hkey
  have hLam : Work.Kernels.LogLambda.LamS (τ : ℂ) + 16 * Ept τ
      = 4 * (Complex.log (Work.Kernels.theta01Fun τ)
              - Complex.log (Work.Kernels.theta00Fun τ) + 4 * Ept τ) := by
    simp only [Work.Kernels.LogLambda.LamS, Work.Kernels.LogLambda.thetaC01,
      Work.Kernels.LogLambda.thetaC00, Work.Kernels.theta01Fun, Work.Kernels.theta00Fun]
    ring
  rw [hLam]
  have hnorm : ‖(4 : ℂ) * (Complex.log (Work.Kernels.theta01Fun τ)
        - Complex.log (Work.Kernels.theta00Fun τ) + 4 * Ept τ)‖
      = 4 * ‖Complex.log (Work.Kernels.theta01Fun τ)
        - Complex.log (Work.Kernels.theta00Fun τ) + 4 * Ept τ‖ := by
    rw [norm_mul]; norm_num
  rw [hnorm]
  calc 4 * ‖Complex.log (Work.Kernels.theta01Fun τ)
          - Complex.log (Work.Kernels.theta00Fun τ) + 4 * Ept τ‖
      ≤ 4 * (200 * r ^ 3) := by linarith [hkey]
    _ = 800 * r ^ 3 := by ring
    _ = 800 * ‖Ept τ‖ ^ 3 := by rw [hr]

end

end Work.Residues
