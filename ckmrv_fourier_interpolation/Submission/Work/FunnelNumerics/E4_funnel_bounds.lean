import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Residues.ThetaDecay

/-!
# Funnel bounds for the weight-four Eisenstein series `E₄`

Two numerical bounds for `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`, used by the funnel tail estimates:

* `‖E₄ τ‖ ≤ 3/2` for `τ` in the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}`;
* `‖E₄ z‖ ≥ 1/2` for `3 ≤ Im z`.

Both follow from the single estimate `‖E₄ τ - 1‖ ≤ 1/2` for `Im τ ≥ 2`, which is a direct
`q`-expansion estimate.  For `Im τ ≥ 2` one has `‖q‖ = e^{-2π Im τ} ≤ e^{-4π} < 1/4096`, while
the coefficients of `E₄ - 1` satisfy `‖c_{m+1}‖ = 240 σ₃(m+1) ≤ 240 (m+1)⁴ ≤ 240 · 16^m`; hence
the tail is dominated by `240 ∑_{m ≥ 0} x (16 x)^m = 240 x/(1 - 16 x) ≤ 480 x` for `x = ‖q‖`.
-/

namespace Work.FunnelNumerics

open UpperHalfPlane

noncomputable section

/-! ## Elementary estimates -/

/-- `(m + 1) ^ 4 ≤ 16 ^ m` for every `m : ℕ`. -/
lemma succ_pow_four_le_pow (m : ℕ) : ((m : ℝ) + 1) ^ 4 ≤ 16 ^ m := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    push_cast
    have hstep : (n : ℝ) + 1 + 1 ≤ 2 * ((n : ℝ) + 1) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc ((n : ℝ) + 1 + 1) ^ 4 ≤ (2 * ((n : ℝ) + 1)) ^ 4 :=
          pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1 + 1) hstep 4
      _ = 16 * ((n : ℝ) + 1) ^ 4 := by ring
      _ ≤ 16 * 16 ^ n := by linarith
      _ = 16 ^ (n + 1) := by rw [pow_succ]; ring

/-- Termwise comparison of the shifted fourth-power series with the geometric majorant. -/
lemma succ_pow_four_mul_shift_le_majorant (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    ((m : ℝ) + 1) ^ 4 * x ^ (m + 1) ≤ x * (16 * x) ^ m := by
  have h1 : ((m : ℝ) + 1) ^ 4 ≤ 16 ^ m := succ_pow_four_le_pow m
  have h2 : ((m : ℝ) + 1) ^ 4 * x ^ (m + 1) ≤ 16 ^ m * x ^ (m + 1) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have hR : x * (16 * x) ^ m = 16 ^ m * x ^ (m + 1) := by
    rw [mul_pow, pow_succ']; ring
  rw [hR]
  exact h2

/-- Summability of the shifted fourth-power geometric series for `0 ≤ x ≤ 1/4096`. -/
lemma summable_succ_pow_four_mul_shift (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4096) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ 4 * x ^ (m + 1)) := by
  have h16 : ‖(16 * x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  refine Summable.of_nonneg_of_le (fun m => by positivity)
    (fun m => succ_pow_four_mul_shift_le_majorant x hx m) ?_
  exact (summable_geometric_of_norm_lt_one h16).mul_left x

/-- `∑_{m ≥ 0} (m + 1)⁴ x^{m+1} ≤ 2 x` for `0 ≤ x ≤ 1/4096`. -/
lemma tsum_succ_pow_four_mul_shift_le (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4096) :
    ∑' m : ℕ, ((m : ℝ) + 1) ^ 4 * x ^ (m + 1) ≤ 2 * x := by
  have h16 : ‖(16 * x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hmaj : Summable (fun m : ℕ => x * (16 * x) ^ m) :=
    (summable_geometric_of_norm_lt_one h16).mul_left x
  calc ∑' m : ℕ, ((m : ℝ) + 1) ^ 4 * x ^ (m + 1)
      ≤ ∑' m : ℕ, x * (16 * x) ^ m :=
        Summable.tsum_le_tsum (fun m => succ_pow_four_mul_shift_le_majorant x hx m)
          (summable_succ_pow_four_mul_shift x hx hx1) hmaj
    _ = x * ∑' m : ℕ, (16 * x) ^ m := tsum_mul_left
    _ = x * (1 - 16 * x)⁻¹ := by rw [tsum_geometric_of_norm_lt_one h16]
    _ ≤ 2 * x := by
        have h1 : 0 < 1 - 16 * x := by linarith
        have h2 : (1 : ℝ) / 2 ≤ 1 - 16 * x := by linarith
        have hinv : (1 - 16 * x)⁻¹ ≤ 2 := by
          have h := (inv_le_inv₀ h1 (by norm_num : (0 : ℝ) < 1 / 2)).mpr h2
          simpa using h
        nlinarith [hx, hinv, h1.le]

/-! ## The `q`-parameter on the funnel -/

/-- For `Im τ ≥ 2` one has `‖q‖ ≤ e^{-4 π} < 1/4096`. -/
lemma norm_qParam_one_le (τ : ℍ) (hτ : 2 ≤ τ.im) :
    ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ≤ 1 / 4096 := by
  rw [Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
  have h12 : Real.exp (-2 * Real.pi * τ.im) ≤ Real.exp (-12) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_gt_three, hτ]
  have he12 : Real.exp (-12) = (Real.exp (-1)) ^ 12 := by
    rw [show (-12 : ℝ) = ((12 : ℕ) : ℝ) * (-1) by norm_num, Real.exp_nat_mul]
  have he1 : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact (inv_lt_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr Real.exp_one_gt_two
  calc Real.exp (-2 * Real.pi * τ.im) ≤ Real.exp (-12) := h12
    _ = (Real.exp (-1)) ^ 12 := he12
    _ ≤ (1 / 2 : ℝ) ^ 12 := le_of_lt (pow_lt_pow_left₀ he1 (Real.exp_pos (-1)).le (by norm_num))
    _ = 1 / 4096 := by norm_num

/-! ## The `q`-expansion of `E₄` -/

/-- The `(m+1)`-st `q`-expansion coefficient of `E₄` is `240 σ₃(m+1)`, of modulus `≤ 240 (m+1)⁴`. -/
lemma E4_coeff_succ_le (m : ℕ) :
    ‖(UpperHalfPlane.qExpansion 1 Work.Modular.E4).coeff (m + 1)‖ ≤ 240 * ((m : ℝ) + 1) ^ 4 := by
  have h := Work.Modular.E4_qExpansion_coeff (m + 1)
  rw [if_neg (by omega : ¬ (m + 1 = 0))] at h
  rw [h, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
  have hsig : ((ArithmeticFunction.sigma 3 (m + 1) : ℕ) : ℝ) ≤ ((m : ℝ) + 1) ^ 4 := by
    have h' : ArithmeticFunction.sigma 3 (m + 1) ≤ (m + 1) ^ 4 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 3 (m + 1)
    have h'' : (((m + 1) ^ 4 : ℕ) : ℝ) = ((m : ℝ) + 1) ^ 4 := by push_cast; ring
    rw [← h'']
    exact_mod_cast h'
  exact mul_le_mul_of_nonneg_left hsig (by norm_num)

/-- The `q`-expansion of `E₄`, isolated at the constant term. -/
lemma E4_hasSum_shift (τ : ℍ) :
    HasSum (fun m : ℕ => (UpperHalfPlane.qExpansion 1 Work.Modular.E4).coeff (m + 1) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)) (Work.Kernels.E4Fun τ - 1) := by
  have hper : Function.Periodic ((⇑ModularForm.E₄ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := (⇑ModularForm.E₄ : ℍ → ℂ)) one_pos
    hper (ModularForm.holo' ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄) τ
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Modular.E4).coeff 0 = 1 := by
    simpa using Work.Modular.E4_qExpansion_coeff 0
  have h := (hasSum_nat_add_iff' 1).mpr hs
  have h0 : (∑ i ∈ Finset.range 1, (UpperHalfPlane.qExpansion 1 Work.Modular.E4).coeff i •
      Function.Periodic.qParam 1 (τ : ℂ) ^ i) = 1 := by
    rw [Finset.sum_range_one, smul_eq_mul, pow_zero, mul_one]
    exact hc0
  rw [h0] at h
  simpa only [smul_eq_mul] using h

/-- **The basic estimate.**  For `Im τ ≥ 2` the value of `E₄` is within `1/2` of `1`. -/
theorem E4_sub_one_le (τ : ℍ) (hτ : 2 ≤ τ.im) : ‖Work.Kernels.E4Fun τ - 1‖ ≤ 1 / 2 := by
  rw [← (E4_hasSum_shift τ).tsum_eq]
  have hx : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ≤ 1 / 4096 := norm_qParam_one_le τ hτ
  have hterm : ∀ m : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Modular.E4).coeff (m + 1) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)‖
      ≤ 240 * (((m : ℝ) + 1) ^ 4 * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1)) := by
    intro m
    rw [norm_mul, norm_pow]
    have hc := E4_coeff_succ_le m
    have hxnn : (0 : ℝ) ≤ ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1) := by positivity
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Modular.E4).coeff (m + 1)‖ *
          ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1)
        ≤ (240 * ((m : ℝ) + 1) ^ 4) * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1) :=
          mul_le_mul_of_nonneg_right hc hxnn
      _ = 240 * (((m : ℝ) + 1) ^ 4 * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1)) := by ring
  have hmaj : Summable (fun m : ℕ => 240 * (((m : ℝ) + 1) ^ 4 *
      ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1))) :=
    (summable_succ_pow_four_mul_shift _ (norm_nonneg _) hx).mul_left 240
  have hsm : Summable (fun m : ℕ => ‖(UpperHalfPlane.qExpansion 1 Work.Modular.E4).coeff (m + 1) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm hmaj
  calc ‖∑' m : ℕ, (UpperHalfPlane.qExpansion 1 Work.Modular.E4).coeff (m + 1) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)‖
      ≤ ∑' m : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Modular.E4).coeff (m + 1) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)‖ := norm_tsum_le_tsum_norm hsm
    _ ≤ ∑' m : ℕ, 240 * (((m : ℝ) + 1) ^ 4 * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1)) :=
        Summable.tsum_le_tsum hterm hsm hmaj
    _ = 240 * ∑' m : ℕ, ((m : ℝ) + 1) ^ 4 * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1) :=
        tsum_mul_left
    _ ≤ 240 * (2 * ‖Function.Periodic.qParam 1 (τ : ℂ)‖) := by
        have hb := tsum_succ_pow_four_mul_shift_le ‖Function.Periodic.qParam 1 (τ : ℂ)‖
          (norm_nonneg _) hx
        linarith
    _ ≤ 1 / 2 := by
        nlinarith [hx, norm_nonneg (Function.Periodic.qParam 1 (τ : ℂ))]

/-! ## The two funnel bounds -/

theorem E4_funnel_bounds :
    (∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ → ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2) ∧
    (∀ z : UpperHalfPlane, 3 ≤ z.im → (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖) := by
  constructor
  · intro τ hτ
    have h2 : 2 ≤ τ.im := Work.Asymptotics.Funnel.im_two hτ
    have hle := E4_sub_one_le τ h2
    calc ‖Work.Kernels.E4Fun τ‖
        = ‖(Work.Kernels.E4Fun τ - 1) + 1‖ := by
          rw [show (Work.Kernels.E4Fun τ - 1) + 1 = Work.Kernels.E4Fun τ by ring]
      _ ≤ ‖Work.Kernels.E4Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 / 2 + 1 := by rw [norm_one]; linarith
      _ = 3 / 2 := by norm_num
  · intro z hz
    have h2 : 2 ≤ z.im := le_trans (by norm_num) hz
    have hle := E4_sub_one_le z h2
    have hsub : (1 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ + ‖Work.Kernels.E4Fun z - 1‖ := by
      have h := norm_sub_le (Work.Kernels.E4Fun z) (Work.Kernels.E4Fun z - 1)
      rw [show Work.Kernels.E4Fun z - (Work.Kernels.E4Fun z - 1) = 1 by ring, norm_one] at h
      exact h
    linarith

end

end Work.FunnelNumerics
