import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs

/-!
# Second-order atom identities at the cusp

This file proves `Work.Asymptotics.KhatE1.SecondOrderAtomIdentities`: the second-order cusp
expansions of the three `τ`-atoms of the CKMRV interpolation problem,

* `Δ - q + 24 q² = O(q³)`,
* `E₄ Δ - q - 216 q² = O(q³)`,
* `U + W - 2 - 48 q = O(q²)`,

where `q = qParamFun τ = e^{2πiτ}` and `IsBigOq f n` means `‖f τ‖ ≤ C ‖q τ‖ⁿ` for `Im τ ≥ 1`.

The first two come from the third-order `q`-expansions of the Eisenstein series `E₄`, `E₆`
together with the identity `1728 Δ = E₄³ - E₆²`; the third from the cusp expansion
`θ₀₀ = 1 + 2 E + O(‖E‖⁴)` (`E = e^{πiτ}`) and its translate `θ₀₁ = 1 - 2 E + O(‖E‖⁴)`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-! ## The third-order `q`-expansions of `E₄` and `E₆` -/

private lemma E4_coeff_three (m : ℕ) (hm : 3 ≤ m) :
    ‖(UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : UpperHalfPlane → ℂ)).coeff m‖
      ≤ 240 * (m : ℝ) ^ 4 := by
  have hm0 : m ≠ 0 := by omega
  rw [Work.Modular.E4_qExpansion_coeff m, if_neg hm0]
  have hσ : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m : ℝ) ^ 4 := by
    have h' : ArithmeticFunction.sigma 3 m ≤ m ^ 4 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 3 m
    exact_mod_cast h'
  rw [norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hσ (by norm_num)

private lemma E6_coeff_three (m : ℕ) (hm : 3 ≤ m) :
    ‖(UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : UpperHalfPlane → ℂ)).coeff m‖
      ≤ 504 * (m : ℝ) ^ 6 := by
  have hm0 : m ≠ 0 := by omega
  rw [Work.Modular.E6_qExpansion_coeff m, if_neg hm0]
  have hσ : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m : ℝ) ^ 6 := by
    have h' : ArithmeticFunction.sigma 5 m ≤ m ^ 6 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 5 m
    exact_mod_cast h'
  rw [norm_mul]
  have h504 : ‖(-504 : ℂ)‖ = (504 : ℝ) := by norm_num
  rw [h504, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hσ (by norm_num)

theorem E4ThirdOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ
        - 2160 * (Work.Kernels.qParamFun τ) ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.qExpansion_tail_bound (r := 3)
    (f := (⇑ModularForm.E₄ : UpperHalfPlane → ℂ))
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularForm.holo' ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄)
    240 4 (by norm_num) E4_coeff_three
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : UpperHalfPlane → ℂ)).coeff 0
      = 1 := by
    simpa using Work.Modular.E4_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : UpperHalfPlane → ℂ)).coeff 1
      = 240 := by
    rw [Work.Modular.E4_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h2 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : UpperHalfPlane → ℂ)).coeff 2
      = 2160 := by
    rw [Work.Modular.E4_qExpansion_coeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    have : ArithmeticFunction.sigma 3 2 = 9 := by decide +kernel
    rw [this]; norm_num
  have hmain := h τ hτ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2] at hmain
  simp only [pow_zero, pow_one, mul_one] at hmain
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  rw [hq] at hmain
  convert hmain using 2
  ring

theorem E6ThirdOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ
        + 16632 * (Work.Kernels.qParamFun τ) ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.qExpansion_tail_bound (r := 3)
    (f := (⇑ModularForm.E₆ : UpperHalfPlane → ℂ))
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL)
    (ModularForm.holo' ModularForm.E₆) (ModularFormClass.bdd_at_infty ModularForm.E₆)
    504 6 (by norm_num) E6_coeff_three
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : UpperHalfPlane → ℂ)).coeff 0
      = 1 := by
    simpa using Work.Modular.E6_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : UpperHalfPlane → ℂ)).coeff 1
      = -504 := by
    rw [Work.Modular.E6_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma_one]
  have h2 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : UpperHalfPlane → ℂ)).coeff 2
      = -16632 := by
    rw [Work.Modular.E6_qExpansion_coeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    have : ArithmeticFunction.sigma 5 2 = 33 := by decide +kernel
    rw [this]; norm_num
  have hmain := h τ hτ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2] at hmain
  simp only [pow_zero, pow_one, mul_one] at hmain
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  rw [hq] at hmain
  convert hmain using 2
  ring

/-! ## The algebra of `E₄³ - E₆²` at third order -/

/-- A pure algebra estimate: if `E₄ = 1 + 240q + 2160q² + e` and `E₆ = 1 - 504q - 16632q² + w`
with `‖e‖ ≤ A‖q‖³`, `‖w‖ ≤ B‖q‖³` and `‖q‖ ≤ 1`, then
`E₄³ - E₆² = 1728q - 41472q² + O(‖q‖³)`. -/
private lemma cubeSubSqThirdOrder (q e w : ℂ) (A B : ℝ)
    (he : ‖e‖ ≤ A * ‖q‖ ^ 3) (hw : ‖w‖ ≤ B * ‖q‖ ^ 3)
    (hq : ‖q‖ ≤ 1) (hA : 0 ≤ A) (_hB : 0 ≤ B) :
    ‖(1 + 240 * q + 2160 * q ^ 2 + e) ^ 3 - (1 - 504 * q - 16632 * q ^ 2 + w) ^ 2
        - (1728 * q - 41472 * q ^ 2)‖
      ≤ (2 ^ 36 + 3 * 2401 ^ 2 * A + 3 * 2401 * A ^ 2 + A ^ 3 + 2 * 17137 * B + B ^ 2)
          * ‖q‖ ^ 3 := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hP : ‖1 + (240 * q + 2160 * q ^ 2)‖ ≤ 2401 := by
    have h1 : ‖(240 : ℂ) * q‖ = 240 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h2 : ‖(2160 : ℂ) * q ^ 2‖ = 2160 * ‖q‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h3 : ‖240 * q + 2160 * q ^ 2‖ ≤ 240 * ‖q‖ + 2160 * ‖q‖ ^ 2 := by
      rw [← h1, ← h2]; exact norm_add_le _ _
    have h4 : 240 * ‖q‖ + 2160 * ‖q‖ ^ 2 ≤ 2400 := by
      have h5 : ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith
      nlinarith
    calc ‖1 + (240 * q + 2160 * q ^ 2)‖ ≤ 1 + ‖240 * q + 2160 * q ^ 2‖ := by
          simpa using norm_add_le (1 : ℂ) (240 * q + 2160 * q ^ 2)
      _ ≤ 1 + 2400 := by linarith
      _ = 2401 := by norm_num
  have hQ : ‖1 + (-504 * q - 16632 * q ^ 2)‖ ≤ 17137 := by
    have h1 : ‖(-504 : ℂ) * q‖ = 504 * ‖q‖ := by rw [norm_mul]; norm_num
    have h2 : ‖(16632 : ℂ) * q ^ 2‖ = 16632 * ‖q‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h3 : ‖-504 * q - 16632 * q ^ 2‖ ≤ 504 * ‖q‖ + 16632 * ‖q‖ ^ 2 := by
      rw [← h1, ← h2]; exact norm_sub_le _ _
    have h4 : 504 * ‖q‖ + 16632 * ‖q‖ ^ 2 ≤ 17136 := by
      have h5 : ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith
      nlinarith
    calc ‖1 + (-504 * q - 16632 * q ^ 2)‖ ≤ 1 + ‖-504 * q - 16632 * q ^ 2‖ := by
          simpa using norm_add_le (1 : ℂ) (-504 * q - 16632 * q ^ 2)
      _ ≤ 1 + 17136 := by linarith
      _ = 17137 := by norm_num
  have hq6 : ‖q‖ ^ 6 ≤ ‖q‖ ^ 3 := pow_le_pow_of_le_one hq0 hq (by norm_num)
  have hq9 : ‖q‖ ^ 9 ≤ ‖q‖ ^ 3 := pow_le_pow_of_le_one hq0 hq (by norm_num)
  have hdecomp : (1 + 240 * q + 2160 * q ^ 2 + e) ^ 3 - (1 - 504 * q - 16632 * q ^ 2 + w) ^ 2
        - (1728 * q - 41472 * q ^ 2)
      = q ^ 3 * (169344 + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3)
        + (3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e
            + 3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2 + e ^ 3)
        - (2 * (1 + (-504 * q - 16632 * q ^ 2)) * w + w ^ 2) := by ring
  rw [hdecomp]
  have t1 : ‖q ^ 3 * (169344 + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3)‖
      ≤ 2 ^ 36 * ‖q‖ ^ 3 := by
    have hR : ‖(169344 : ℂ) + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3‖
        ≤ 2 ^ 36 := by
      have h1 : ‖(110621376 : ℂ) * q‖ ≤ 110621376 := by
        rw [norm_mul, Complex.norm_ofNat]; nlinarith [norm_nonneg q, hq]
      have h2 : ‖(3359232000 : ℂ) * q ^ 2‖ ≤ 3359232000 := by
        rw [norm_mul, norm_pow, Complex.norm_ofNat]
        have : ‖q‖ ^ 2 ≤ 1 := by nlinarith
        nlinarith
      have h3 : ‖(10077696000 : ℂ) * q ^ 3‖ ≤ 10077696000 := by
        rw [norm_mul, norm_pow, Complex.norm_ofNat]
        have : ‖q‖ ^ 3 ≤ 1 := by nlinarith
        nlinarith
      have h0 : ‖(169344 : ℂ) + 110621376 * q‖ ≤ 169344 + 110621376 := by
        have := norm_add_le (169344 : ℂ) (110621376 * q)
        rw [Complex.norm_ofNat] at this
        linarith
      have ha := norm_add_le ((169344 : ℂ) + 110621376 * q) (3359232000 * q ^ 2)
      have hb := norm_add_le ((169344 : ℂ) + 110621376 * q + 3359232000 * q ^ 2)
        (10077696000 * q ^ 3)
      linarith
    rw [norm_mul, norm_pow]
    calc ‖q‖ ^ 3 * ‖(169344 : ℂ) + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3‖
        ≤ ‖q‖ ^ 3 * 2 ^ 36 := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = 2 ^ 36 * ‖q‖ ^ 3 := by ring
  have t2 : ‖3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e
        + 3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2 + e ^ 3‖
      ≤ (3 * 2401 ^ 2 * A + 3 * 2401 * A ^ 2 + A ^ 3) * ‖q‖ ^ 3 := by
    have b1 : ‖3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e‖ ≤ 3 * 2401 ^ 2 * A * ‖q‖ ^ 3 := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
      have h1 : ‖1 + (240 * q + 2160 * q ^ 2)‖ ^ 2 ≤ 2401 ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hP 2
      have hmul : ‖1 + (240 * q + 2160 * q ^ 2)‖ ^ 2 * ‖e‖
          ≤ 2401 ^ 2 * (A * ‖q‖ ^ 3) :=
        mul_le_mul h1 he (norm_nonneg e) (by positivity)
      calc 3 * ‖1 + (240 * q + 2160 * q ^ 2)‖ ^ 2 * ‖e‖
          ≤ 3 * (2401 ^ 2 * (A * ‖q‖ ^ 3)) := by linarith
        _ = 3 * 2401 ^ 2 * A * ‖q‖ ^ 3 := by ring
    have b2 : ‖3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2‖ ≤ 3 * 2401 * A ^ 2 * ‖q‖ ^ 3 := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
      have he2 : ‖e‖ ^ 2 ≤ A ^ 2 * ‖q‖ ^ 6 := by
        calc ‖e‖ ^ 2 ≤ (A * ‖q‖ ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg e) he 2
          _ = A ^ 2 * ‖q‖ ^ 6 := by ring
      have hmul : ‖1 + (240 * q + 2160 * q ^ 2)‖ * ‖e‖ ^ 2 ≤ 2401 * (A ^ 2 * ‖q‖ ^ 6) :=
        mul_le_mul hP he2 (by positivity) (by positivity)
      calc 3 * ‖1 + (240 * q + 2160 * q ^ 2)‖ * ‖e‖ ^ 2
          ≤ 3 * (2401 * (A ^ 2 * ‖q‖ ^ 6)) := by linarith
        _ = 3 * 2401 * A ^ 2 * ‖q‖ ^ 6 := by ring
        _ ≤ 3 * 2401 * A ^ 2 * ‖q‖ ^ 3 := mul_le_mul_of_nonneg_left hq6 (by positivity)
    have b3 : ‖e ^ 3‖ ≤ A ^ 3 * ‖q‖ ^ 3 := by
      rw [norm_pow]
      calc ‖e‖ ^ 3 ≤ (A * ‖q‖ ^ 3) ^ 3 := pow_le_pow_left₀ (norm_nonneg e) he 3
        _ = A ^ 3 * ‖q‖ ^ 9 := by ring
        _ ≤ A ^ 3 * ‖q‖ ^ 3 := mul_le_mul_of_nonneg_left hq9 (by positivity)
    have hsplit : ‖3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e
        + 3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2 + e ^ 3‖
        ≤ ‖3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e‖
          + ‖3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2‖ + ‖e ^ 3‖ := by
      have a := norm_add_le (3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e
        + 3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2) (e ^ 3)
      have b := norm_add_le (3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e)
        (3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2)
      linarith
    calc ‖3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e
          + 3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2 + e ^ 3‖
        ≤ ‖3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e‖
          + ‖3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2‖ + ‖e ^ 3‖ := hsplit
      _ ≤ 3 * 2401 ^ 2 * A * ‖q‖ ^ 3 + 3 * 2401 * A ^ 2 * ‖q‖ ^ 3 + A ^ 3 * ‖q‖ ^ 3 := by
          linarith
      _ = (3 * 2401 ^ 2 * A + 3 * 2401 * A ^ 2 + A ^ 3) * ‖q‖ ^ 3 := by ring
  have t3 : ‖2 * (1 + (-504 * q - 16632 * q ^ 2)) * w + w ^ 2‖
      ≤ (2 * 17137 * B + B ^ 2) * ‖q‖ ^ 3 := by
    have b1 : ‖2 * (1 + (-504 * q - 16632 * q ^ 2)) * w‖ ≤ 2 * 17137 * B * ‖q‖ ^ 3 := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
      have hmul : ‖1 + (-504 * q - 16632 * q ^ 2)‖ * ‖w‖ ≤ 17137 * (B * ‖q‖ ^ 3) :=
        mul_le_mul hQ hw (norm_nonneg w) (by positivity)
      calc 2 * ‖1 + (-504 * q - 16632 * q ^ 2)‖ * ‖w‖ ≤ 2 * (17137 * (B * ‖q‖ ^ 3)) := by
            linarith
        _ = 2 * 17137 * B * ‖q‖ ^ 3 := by ring
    have b2 : ‖w ^ 2‖ ≤ B ^ 2 * ‖q‖ ^ 3 := by
      rw [norm_pow]
      calc ‖w‖ ^ 2 ≤ (B * ‖q‖ ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hw 2
        _ = B ^ 2 * ‖q‖ ^ 6 := by ring
        _ ≤ B ^ 2 * ‖q‖ ^ 3 := mul_le_mul_of_nonneg_left hq6 (by positivity)
    have hsplit : ‖2 * (1 + (-504 * q - 16632 * q ^ 2)) * w + w ^ 2‖
        ≤ ‖2 * (1 + (-504 * q - 16632 * q ^ 2)) * w‖ + ‖w ^ 2‖ := norm_add_le _ _
    calc ‖2 * (1 + (-504 * q - 16632 * q ^ 2)) * w + w ^ 2‖
        ≤ ‖2 * (1 + (-504 * q - 16632 * q ^ 2)) * w‖ + ‖w ^ 2‖ := hsplit
      _ ≤ 2 * 17137 * B * ‖q‖ ^ 3 + B ^ 2 * ‖q‖ ^ 3 := by linarith
      _ = (2 * 17137 * B + B ^ 2) * ‖q‖ ^ 3 := by ring
  have a := norm_sub_le (q ^ 3 * (169344 + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3)
      + (3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e
          + 3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2 + e ^ 3))
    (2 * (1 + (-504 * q - 16632 * q ^ 2)) * w + w ^ 2)
  have b := norm_add_le (q ^ 3 * (169344 + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3))
    (3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e
        + 3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2 + e ^ 3)
  calc ‖q ^ 3 * (169344 + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3)
        + (3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e
            + 3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2 + e ^ 3)
        - (2 * (1 + (-504 * q - 16632 * q ^ 2)) * w + w ^ 2)‖
      ≤ ‖q ^ 3 * (169344 + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3)
          + (3 * (1 + (240 * q + 2160 * q ^ 2)) ^ 2 * e
              + 3 * (1 + (240 * q + 2160 * q ^ 2)) * e ^ 2 + e ^ 3)‖
        + ‖2 * (1 + (-504 * q - 16632 * q ^ 2)) * w + w ^ 2‖ := a
    _ ≤ (2 ^ 36 * ‖q‖ ^ 3 + (3 * 2401 ^ 2 * A + 3 * 2401 * A ^ 2 + A ^ 3) * ‖q‖ ^ 3)
        + (2 * 17137 * B + B ^ 2) * ‖q‖ ^ 3 := by linarith [b]
    _ = (2 ^ 36 + 3 * 2401 ^ 2 * A + 3 * 2401 * A ^ 2 + A ^ 3 + 2 * 17137 * B + B ^ 2)
        * ‖q‖ ^ 3 := by ring

/-! ## `Δ - q + 24 q² = O(q³)` -/

private theorem DeltaThirdOrder :
    Work.Asymptotics.IsBigOq (fun τ : UpperHalfPlane => Work.Kernels.DeltaFun τ
        - Work.Kernels.qParamFun τ + 24 * (Work.Kernels.qParamFun τ) ^ 2) 3 := by
  obtain ⟨C4, hC4, hE4⟩ := E4ThirdOrder
  obtain ⟨C6, hC6, hE6⟩ := E6ThirdOrder
  refine ⟨(2 ^ 36 + 3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3 + 2 * 17137 * C6 + C6 ^ 2)
      / 1728 + 1, by positivity, fun τ hτ => ?_⟩
  change ‖Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ
      + 24 * (Work.Kernels.qParamFun τ) ^ 2‖
    ≤ ((2 ^ 36 + 3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3 + 2 * 17137 * C6 + C6 ^ 2)
      / 1728 + 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3
  set q : ℂ := Work.Kernels.qParamFun τ with hq
  have hq1 : ‖q‖ ≤ 1 := by rw [hq]; exact Work.Asymptotics.norm_qParamFun_le_one τ hτ
  have hD : Work.Kernels.DeltaFun τ
      = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) / 1728 := by
    have h1 : Work.Kernels.DeltaFun τ = ModularForm.discriminant τ := by
      rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
    rw [h1]
    exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  have hkey : Work.Kernels.DeltaFun τ - q + 24 * q ^ 2
      = ((Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2)
          - (1728 * q - 41472 * q ^ 2)) / 1728 := by
    rw [hD]; ring
  have halg := cubeSubSqThirdOrder q (Work.Kernels.E4Fun τ - 1 - 240 * q - 2160 * q ^ 2)
    (Work.Kernels.E6Fun τ - 1 + 504 * q + 16632 * q ^ 2) C4 C6
    (by rw [hq]; exact hE4 τ hτ) (by rw [hq]; exact hE6 τ hτ) hq1 (le_of_lt hC4) (le_of_lt hC6)
  rw [show (1 + 240 * q + 2160 * q ^ 2 + (Work.Kernels.E4Fun τ - 1 - 240 * q - 2160 * q ^ 2))
      = Work.Kernels.E4Fun τ by ring,
    show (1 - 504 * q - 16632 * q ^ 2 + (Work.Kernels.E6Fun τ - 1 + 504 * q + 16632 * q ^ 2))
      = Work.Kernels.E6Fun τ by ring] at halg
  rw [hkey, norm_div, Complex.norm_ofNat]
  have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
  have hKn : (0 : ℝ) ≤ 2 ^ 36 + 3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3
      + 2 * 17137 * C6 + C6 ^ 2 := by positivity
  calc ‖(Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) - (1728 * q - 41472 * q ^ 2)‖ / 1728
      ≤ ((2 ^ 36 + 3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3 + 2 * 17137 * C6 + C6 ^ 2)
          * ‖q‖ ^ 3) / 1728 := div_le_div_of_nonneg_right halg (by norm_num)
    _ = ((2 ^ 36 + 3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3 + 2 * 17137 * C6 + C6 ^ 2)
          / 1728) * ‖q‖ ^ 3 := by ring
    _ ≤ ((2 ^ 36 + 3 * 2401 ^ 2 * C4 + 3 * 2401 * C4 ^ 2 + C4 ^ 3 + 2 * 17137 * C6 + C6 ^ 2)
          / 1728 + 1) * ‖q‖ ^ 3 := by nlinarith [h3]

/-! ## `E₄ Δ - q - 216 q² = O(q³)` -/

private theorem E4DeltaThirdOrder :
    Work.Asymptotics.IsBigOq (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ
        * Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ
        - 216 * (Work.Kernels.qParamFun τ) ^ 2) 3 := by
  obtain ⟨Ka, hKa, hΔ⟩ := DeltaThirdOrder
  obtain ⟨C4, hC4, hE4⟩ := Work.Residues.E4FunSecondOrder
  obtain ⟨Cd, hCd, hD⟩ := Work.Asymptotics.DeltaFun_upper
  refine ⟨241 * Ka + 5760 + C4 * Cd, by positivity, fun τ hτ => ?_⟩
  change ‖Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ
      - 216 * (Work.Kernels.qParamFun τ) ^ 2‖
    ≤ (241 * Ka + 5760 + C4 * Cd) * ‖Work.Kernels.qParamFun τ‖ ^ 3
  set q : ℂ := Work.Kernels.qParamFun τ with hq
  have hq1 : ‖q‖ ≤ 1 := by rw [hq]; exact Work.Asymptotics.norm_qParamFun_le_one τ hτ
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hΔb : ‖Work.Kernels.DeltaFun τ - q + 24 * q ^ 2‖ ≤ Ka * ‖q‖ ^ 3 := by
    rw [hq]; exact hΔ τ hτ
  have hE4b : ‖Work.Kernels.E4Fun τ - 1 - 240 * q‖ ≤ C4 * ‖q‖ ^ 2 := by
    rw [hq]; exact hE4 τ hτ
  have hDb : ‖Work.Kernels.DeltaFun τ‖ ≤ Cd * ‖q‖ := by rw [hq]; exact hD τ hτ
  have hkey : Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ - q - 216 * q ^ 2
      = (1 + 240 * q) * (Work.Kernels.DeltaFun τ - q + 24 * q ^ 2) - 5760 * q ^ 3
        + (Work.Kernels.E4Fun τ - 1 - 240 * q) * Work.Kernels.DeltaFun τ := by ring
  rw [hkey]
  have h1P : ‖(1 : ℂ) + 240 * q‖ ≤ 241 := by
    have h := norm_add_le (1 : ℂ) (240 * q)
    rw [norm_one] at h
    have h2 : ‖(240 : ℂ) * q‖ = 240 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
    rw [h2] at h
    linarith
  have b1 : ‖(1 + 240 * q) * (Work.Kernels.DeltaFun τ - q + 24 * q ^ 2)‖ ≤ 241 * Ka * ‖q‖ ^ 3 := by
    rw [norm_mul]
    have hmul : ‖1 + 240 * q‖ * ‖Work.Kernels.DeltaFun τ - q + 24 * q ^ 2‖
        ≤ 241 * (Ka * ‖q‖ ^ 3) :=
      mul_le_mul h1P hΔb (norm_nonneg _) (by positivity)
    calc ‖1 + 240 * q‖ * ‖Work.Kernels.DeltaFun τ - q + 24 * q ^ 2‖
        ≤ 241 * (Ka * ‖q‖ ^ 3) := hmul
      _ = 241 * Ka * ‖q‖ ^ 3 := by ring
  have b2 : ‖(5760 : ℂ) * q ^ 3‖ ≤ 5760 * ‖q‖ ^ 3 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  have b3 : ‖(Work.Kernels.E4Fun τ - 1 - 240 * q) * Work.Kernels.DeltaFun τ‖
      ≤ C4 * Cd * ‖q‖ ^ 3 := by
    rw [norm_mul]
    have hmul : ‖Work.Kernels.E4Fun τ - 1 - 240 * q‖ * ‖Work.Kernels.DeltaFun τ‖
        ≤ (C4 * ‖q‖ ^ 2) * (Cd * ‖q‖) :=
      mul_le_mul hE4b hDb (norm_nonneg _) (by positivity)
    calc ‖Work.Kernels.E4Fun τ - 1 - 240 * q‖ * ‖Work.Kernels.DeltaFun τ‖
        ≤ (C4 * ‖q‖ ^ 2) * (Cd * ‖q‖) := hmul
      _ = C4 * Cd * ‖q‖ ^ 3 := by ring
  have hA1 : ‖(1 + 240 * q) * (Work.Kernels.DeltaFun τ - q + 24 * q ^ 2) - 5760 * q ^ 3
        + (Work.Kernels.E4Fun τ - 1 - 240 * q) * Work.Kernels.DeltaFun τ‖
      ≤ ‖(1 + 240 * q) * (Work.Kernels.DeltaFun τ - q + 24 * q ^ 2) - 5760 * q ^ 3‖
        + ‖(Work.Kernels.E4Fun τ - 1 - 240 * q) * Work.Kernels.DeltaFun τ‖ :=
    norm_add_le _ _
  have hA2 : ‖(1 + 240 * q) * (Work.Kernels.DeltaFun τ - q + 24 * q ^ 2) - 5760 * q ^ 3‖
      ≤ ‖(1 + 240 * q) * (Work.Kernels.DeltaFun τ - q + 24 * q ^ 2)‖ + ‖(5760 : ℂ) * q ^ 3‖ :=
    norm_sub_le _ _
  calc ‖(1 + 240 * q) * (Work.Kernels.DeltaFun τ - q + 24 * q ^ 2) - 5760 * q ^ 3
        + (Work.Kernels.E4Fun τ - 1 - 240 * q) * Work.Kernels.DeltaFun τ‖
      ≤ ‖(1 + 240 * q) * (Work.Kernels.DeltaFun τ - q + 24 * q ^ 2) - 5760 * q ^ 3‖
        + ‖(Work.Kernels.E4Fun τ - 1 - 240 * q) * Work.Kernels.DeltaFun τ‖ := hA1
    _ ≤ (‖(1 + 240 * q) * (Work.Kernels.DeltaFun τ - q + 24 * q ^ 2)‖ + ‖(5760 : ℂ) * q ^ 3‖)
        + ‖(Work.Kernels.E4Fun τ - 1 - 240 * q) * Work.Kernels.DeltaFun τ‖ := by linarith
    _ ≤ (241 * Ka * ‖q‖ ^ 3 + 5760 * ‖q‖ ^ 3) + C4 * Cd * ‖q‖ ^ 3 := by linarith
    _ = (241 * Ka + 5760 + C4 * Cd) * ‖q‖ ^ 3 := by ring

/-! ## `U + W - 2 - 48 q = O(q²)` -/

/-- Fourth-power estimate: if `x = 2E + d` with `‖d‖ ≤ C‖E‖⁴`, `C ≥ 0` and `‖E‖ ≤ 1`, then
`(1 + x)⁴ - (1 + 8E + 24E² + 32E³)` is `O(‖E‖⁴)`. -/
private lemma quarticRem (E d : ℂ) (C : ℝ) (hC : 0 ≤ C) (hE : ‖E‖ ≤ 1) (hd : ‖d‖ ≤ C * ‖E‖ ^ 4) :
    ‖(1 + (2 * E + d)) ^ 4 - (1 + 8 * E + 24 * E ^ 2 + 32 * E ^ 3)‖
      ≤ (108 * C + 54 * C ^ 2 + 12 * C ^ 3 + C ^ 4 + 16) * ‖E‖ ^ 4 := by
  have hE0 : 0 ≤ ‖E‖ := norm_nonneg E
  have h1 : ‖E‖ ^ 5 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hE0 hE (by norm_num)
  have h2 : ‖E‖ ^ 6 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hE0 hE (by norm_num)
  have h3 : ‖E‖ ^ 7 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hE0 hE (by norm_num)
  have h4 : ‖E‖ ^ 8 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hE0 hE (by norm_num)
  have h5 : ‖E‖ ^ 9 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hE0 hE (by norm_num)
  have h6 : ‖E‖ ^ 10 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hE0 hE (by norm_num)
  have h7 : ‖E‖ ^ 12 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hE0 hE (by norm_num)
  have h8 : ‖E‖ ^ 13 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hE0 hE (by norm_num)
  have h9 : ‖E‖ ^ 16 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hE0 hE (by norm_num)
  have hd2 : ‖d‖ ^ 2 ≤ C ^ 2 * ‖E‖ ^ 8 := by
    calc ‖d‖ ^ 2 ≤ (C * ‖E‖ ^ 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg d) hd 2
      _ = C ^ 2 * ‖E‖ ^ 8 := by ring
  have hd3 : ‖d‖ ^ 3 ≤ C ^ 3 * ‖E‖ ^ 12 := by
    calc ‖d‖ ^ 3 ≤ (C * ‖E‖ ^ 4) ^ 3 := pow_le_pow_left₀ (norm_nonneg d) hd 3
      _ = C ^ 3 * ‖E‖ ^ 12 := by ring
  have hd4 : ‖d‖ ^ 4 ≤ C ^ 4 * ‖E‖ ^ 16 := by
    calc ‖d‖ ^ 4 ≤ (C * ‖E‖ ^ 4) ^ 4 := pow_le_pow_left₀ (norm_nonneg d) hd 4
      _ = C ^ 4 * ‖E‖ ^ 16 := by ring
  have hdecomp : (1 + (2 * E + d)) ^ 4 - (1 + 8 * E + 24 * E ^ 2 + 32 * E ^ 3)
      = (4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d + 24 * E * d ^ 2 + 4 * d ^ 3
          + 16 * E ^ 4 + 32 * E ^ 3 * d + 24 * E ^ 2 * d ^ 2 + 8 * E * d ^ 3 + d ^ 4) := by
    ring
  rw [hdecomp]
  have hd5 : ‖d‖ ≤ C * ‖E‖ ^ 4 := hd
  have e1 : ‖4 * d‖ ≤ 4 * C * ‖E‖ ^ 4 := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 4 * ‖d‖ ≤ 4 * (C * ‖E‖ ^ 4) := by linarith
      _ = 4 * C * ‖E‖ ^ 4 := by ring
  have e2 : ‖24 * E * d‖ ≤ 24 * C * ‖E‖ ^ 4 := by
    have hb : ‖24 * E * d‖ = 24 * ‖E‖ * ‖d‖ := by rw [norm_mul, norm_mul, Complex.norm_ofNat]
    rw [hb]
    calc 24 * ‖E‖ * ‖d‖ ≤ 24 * ‖E‖ * (C * ‖E‖ ^ 4) :=
          mul_le_mul_of_nonneg_left hd5 (by positivity)
      _ = 24 * C * ‖E‖ ^ 5 := by ring
      _ ≤ 24 * C * ‖E‖ ^ 4 := mul_le_mul_of_nonneg_left h1 (by positivity)
  have e3 : ‖6 * d ^ 2‖ ≤ 6 * C ^ 2 * ‖E‖ ^ 4 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    calc 6 * ‖d‖ ^ 2 ≤ 6 * (C ^ 2 * ‖E‖ ^ 8) := by linarith
      _ = 6 * C ^ 2 * ‖E‖ ^ 8 := by ring
      _ ≤ 6 * C ^ 2 * ‖E‖ ^ 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
  have e4 : ‖48 * E ^ 2 * d‖ ≤ 48 * C * ‖E‖ ^ 4 := by
    have hb : ‖48 * E ^ 2 * d‖ = 48 * ‖E‖ ^ 2 * ‖d‖ := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hb]
    calc 48 * ‖E‖ ^ 2 * ‖d‖ ≤ 48 * ‖E‖ ^ 2 * (C * ‖E‖ ^ 4) :=
          mul_le_mul_of_nonneg_left hd5 (by positivity)
      _ = 48 * C * ‖E‖ ^ 6 := by ring
      _ ≤ 48 * C * ‖E‖ ^ 4 := mul_le_mul_of_nonneg_left h2 (by positivity)
  have e5 : ‖24 * E * d ^ 2‖ ≤ 24 * C ^ 2 * ‖E‖ ^ 4 := by
    have hb : ‖24 * E * d ^ 2‖ = 24 * ‖E‖ * ‖d‖ ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hb]
    calc 24 * ‖E‖ * ‖d‖ ^ 2 ≤ 24 * ‖E‖ * (C ^ 2 * ‖E‖ ^ 8) :=
          mul_le_mul_of_nonneg_left hd2 (by positivity)
      _ = 24 * C ^ 2 * ‖E‖ ^ 9 := by ring
      _ ≤ 24 * C ^ 2 * ‖E‖ ^ 4 := mul_le_mul_of_nonneg_left h5 (by positivity)
  have e6 : ‖4 * d ^ 3‖ ≤ 4 * C ^ 3 * ‖E‖ ^ 4 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    calc 4 * ‖d‖ ^ 3 ≤ 4 * (C ^ 3 * ‖E‖ ^ 12) := by linarith
      _ = 4 * C ^ 3 * ‖E‖ ^ 12 := by ring
      _ ≤ 4 * C ^ 3 * ‖E‖ ^ 4 := mul_le_mul_of_nonneg_left h7 (by positivity)
  have e7 : ‖16 * E ^ 4‖ ≤ 16 * ‖E‖ ^ 4 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  have e8 : ‖32 * E ^ 3 * d‖ ≤ 32 * C * ‖E‖ ^ 4 := by
    have hb : ‖32 * E ^ 3 * d‖ = 32 * ‖E‖ ^ 3 * ‖d‖ := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hb]
    calc 32 * ‖E‖ ^ 3 * ‖d‖ ≤ 32 * ‖E‖ ^ 3 * (C * ‖E‖ ^ 4) :=
          mul_le_mul_of_nonneg_left hd5 (by positivity)
      _ = 32 * C * ‖E‖ ^ 7 := by ring
      _ ≤ 32 * C * ‖E‖ ^ 4 := mul_le_mul_of_nonneg_left h3 (by positivity)
  have e9 : ‖24 * E ^ 2 * d ^ 2‖ ≤ 24 * C ^ 2 * ‖E‖ ^ 4 := by
    have hb : ‖24 * E ^ 2 * d ^ 2‖ = 24 * ‖E‖ ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat]
    rw [hb]
    calc 24 * ‖E‖ ^ 2 * ‖d‖ ^ 2 ≤ 24 * ‖E‖ ^ 2 * (C ^ 2 * ‖E‖ ^ 8) :=
          mul_le_mul_of_nonneg_left hd2 (by positivity)
      _ = 24 * C ^ 2 * ‖E‖ ^ 10 := by ring
      _ ≤ 24 * C ^ 2 * ‖E‖ ^ 4 := mul_le_mul_of_nonneg_left h6 (by positivity)
  have e10 : ‖8 * E * d ^ 3‖ ≤ 8 * C ^ 3 * ‖E‖ ^ 4 := by
    have hb : ‖8 * E * d ^ 3‖ = 8 * ‖E‖ * ‖d‖ ^ 3 := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hb]
    calc 8 * ‖E‖ * ‖d‖ ^ 3 ≤ 8 * ‖E‖ * (C ^ 3 * ‖E‖ ^ 12) :=
          mul_le_mul_of_nonneg_left hd3 (by positivity)
      _ = 8 * C ^ 3 * ‖E‖ ^ 13 := by ring
      _ ≤ 8 * C ^ 3 * ‖E‖ ^ 4 := mul_le_mul_of_nonneg_left h8 (by positivity)
  have e11 : ‖d ^ 4‖ ≤ C ^ 4 * ‖E‖ ^ 4 := by
    rw [norm_pow]
    calc ‖d‖ ^ 4 ≤ C ^ 4 * ‖E‖ ^ 16 := hd4
      _ ≤ C ^ 4 * ‖E‖ ^ 4 := mul_le_mul_of_nonneg_left h9 (by positivity)
  have hs : ‖4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d + 24 * E * d ^ 2 + 4 * d ^ 3
        + 16 * E ^ 4 + 32 * E ^ 3 * d + 24 * E ^ 2 * d ^ 2 + 8 * E * d ^ 3 + d ^ 4‖
      ≤ ‖4 * d‖ + ‖24 * E * d‖ + ‖6 * d ^ 2‖ + ‖48 * E ^ 2 * d‖ + ‖24 * E * d ^ 2‖ + ‖4 * d ^ 3‖
        + ‖16 * E ^ 4‖ + ‖32 * E ^ 3 * d‖ + ‖24 * E ^ 2 * d ^ 2‖ + ‖8 * E * d ^ 3‖ + ‖d ^ 4‖ := by
    have a1 := norm_add_le (4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d + 24 * E * d ^ 2 + 4 * d ^ 3
        + 16 * E ^ 4 + 32 * E ^ 3 * d + 24 * E ^ 2 * d ^ 2 + 8 * E * d ^ 3) (d ^ 4)
    have a2 := norm_add_le (4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d + 24 * E * d ^ 2 + 4 * d ^ 3
        + 16 * E ^ 4 + 32 * E ^ 3 * d + 24 * E ^ 2 * d ^ 2) (8 * E * d ^ 3)
    have a3 := norm_add_le (4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d + 24 * E * d ^ 2 + 4 * d ^ 3
        + 16 * E ^ 4 + 32 * E ^ 3 * d) (24 * E ^ 2 * d ^ 2)
    have a4 := norm_add_le (4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d + 24 * E * d ^ 2 + 4 * d ^ 3
        + 16 * E ^ 4) (32 * E ^ 3 * d)
    have a5 := norm_add_le (4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d + 24 * E * d ^ 2 + 4 * d ^ 3)
      (16 * E ^ 4)
    have a6 := norm_add_le (4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d + 24 * E * d ^ 2) (4 * d ^ 3)
    have a7 := norm_add_le (4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d) (24 * E * d ^ 2)
    have a8 := norm_add_le (4 * d + 24 * E * d + 6 * d ^ 2) (48 * E ^ 2 * d)
    have a9 := norm_add_le (4 * d + 24 * E * d) (6 * d ^ 2)
    have a10 := norm_add_le (4 * d) (24 * E * d)
    linarith
  calc ‖4 * d + 24 * E * d + 6 * d ^ 2 + 48 * E ^ 2 * d + 24 * E * d ^ 2 + 4 * d ^ 3
        + 16 * E ^ 4 + 32 * E ^ 3 * d + 24 * E ^ 2 * d ^ 2 + 8 * E * d ^ 3 + d ^ 4‖
      ≤ ‖4 * d‖ + ‖24 * E * d‖ + ‖6 * d ^ 2‖ + ‖48 * E ^ 2 * d‖ + ‖24 * E * d ^ 2‖ + ‖4 * d ^ 3‖
        + ‖16 * E ^ 4‖ + ‖32 * E ^ 3 * d‖ + ‖24 * E ^ 2 * d ^ 2‖ + ‖8 * E * d ^ 3‖ + ‖d ^ 4‖ := hs
    _ ≤ 4 * C * ‖E‖ ^ 4 + 24 * C * ‖E‖ ^ 4 + 6 * C ^ 2 * ‖E‖ ^ 4 + 48 * C * ‖E‖ ^ 4
        + 24 * C ^ 2 * ‖E‖ ^ 4 + 4 * C ^ 3 * ‖E‖ ^ 4 + 16 * ‖E‖ ^ 4 + 32 * C * ‖E‖ ^ 4
        + 24 * C ^ 2 * ‖E‖ ^ 4 + 8 * C ^ 3 * ‖E‖ ^ 4 + C ^ 4 * ‖E‖ ^ 4 := by
          linarith [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
    _ = (108 * C + 54 * C ^ 2 + 12 * C ^ 3 + C ^ 4 + 16) * ‖E‖ ^ 4 := by ring

private theorem Xi2SecondOrder :
    Work.Asymptotics.IsBigOq (fun τ : UpperHalfPlane => Work.Kernels.UFun τ
        + Work.Kernels.WFun τ - 2 - 48 * Work.Kernels.qParamFun τ) 2 := by
  obtain ⟨C0, hC0, h00⟩ := Work.Residues.theta00Fun_expansion
  have h01 : ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.theta01Fun τ - 1 + 2 * Work.Residues.Ept τ‖
        ≤ C0 * ‖Work.Residues.Ept τ‖ ^ 4 := by
    intro τ hτ
    have hτ' : (1 : ℝ) ≤ (ModularGroup.T • τ).im := by
      rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.vadd_im]; exact hτ
    have h := h00 (ModularGroup.T • τ) hτ'
    rw [Work.Kernels.theta00Fun_T τ, Work.Residues.Ept_T τ, norm_neg] at h
    simpa only [mul_neg, sub_neg_eq_add] using h
  refine ⟨2 * (108 * C0 + 54 * C0 ^ 2 + 12 * C0 ^ 3 + C0 ^ 4 + 16), by positivity,
    fun τ hτ => ?_⟩
  change ‖Work.Kernels.UFun τ + Work.Kernels.WFun τ - 2
      - 48 * Work.Kernels.qParamFun τ‖
    ≤ 2 * (108 * C0 + 54 * C0 ^ 2 + 12 * C0 ^ 3 + C0 ^ 4 + 16) * ‖Work.Kernels.qParamFun τ‖ ^ 2
  set q : ℂ := Work.Kernels.qParamFun τ with hq
  set E : ℂ := Work.Residues.Ept τ with hE
  have hE1 : ‖E‖ ≤ 1 := by rw [hE]; exact le_of_lt (Work.Residues.norm_Ept_lt_one τ)
  have hqE : q = E ^ 2 := by
    rw [hq, hE, Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]
    congr 1; ring
  have h00b : ‖Work.Kernels.theta00Fun τ - 1 - 2 * E‖ ≤ C0 * ‖E‖ ^ 4 := by
    rw [hE]; exact h00 τ hτ
  have h01b : ‖Work.Kernels.theta01Fun τ - 1 + 2 * E‖ ≤ C0 * ‖E‖ ^ 4 := by
    rw [hE]; exact h01 τ hτ
  have hC0' : (0 : ℝ) ≤ C0 := le_of_lt hC0
  have hU : ‖Work.Kernels.UFun τ - (1 + 8 * E + 24 * E ^ 2 + 32 * E ^ 3)‖
      ≤ (108 * C0 + 54 * C0 ^ 2 + 12 * C0 ^ 3 + C0 ^ 4 + 16) * ‖E‖ ^ 4 := by
    have h := quarticRem E (Work.Kernels.theta00Fun τ - 1 - 2 * E) C0 hC0' hE1 h00b
    rw [show (1 + (2 * E + (Work.Kernels.theta00Fun τ - 1 - 2 * E))) ^ 4
        = Work.Kernels.UFun τ by
      rw [show Work.Kernels.UFun τ = Work.Kernels.theta00Fun τ ^ 4 from rfl]; ring] at h
    exact h
  have hW : ‖Work.Kernels.WFun τ - (1 - 8 * E + 24 * E ^ 2 - 32 * E ^ 3)‖
      ≤ (108 * C0 + 54 * C0 ^ 2 + 12 * C0 ^ 3 + C0 ^ 4 + 16) * ‖E‖ ^ 4 := by
    have hE1' : ‖-E‖ ≤ 1 := by rw [norm_neg]; exact hE1
    have h01b' : ‖Work.Kernels.theta01Fun τ - 1 + 2 * E‖ ≤ C0 * ‖-E‖ ^ 4 := by
      rw [norm_neg]; exact h01b
    have h := quarticRem (-E) (Work.Kernels.theta01Fun τ - 1 + 2 * E) C0 hC0' hE1' h01b'
    rw [show (1 + (2 * (-E) + (Work.Kernels.theta01Fun τ - 1 + 2 * E))) ^ 4
        = Work.Kernels.WFun τ by
      rw [show Work.Kernels.WFun τ = Work.Kernels.theta01Fun τ ^ 4 from rfl]; ring,
      show (1 + 8 * (-E) + 24 * (-E) ^ 2 + 32 * (-E) ^ 3) = (1 - 8 * E + 24 * E ^ 2 - 32 * E ^ 3) by
        ring,
      norm_neg] at h
    exact h
  have hkey : Work.Kernels.UFun τ + Work.Kernels.WFun τ - 2 - 48 * q
      = (Work.Kernels.UFun τ - (1 + 8 * E + 24 * E ^ 2 + 32 * E ^ 3))
        + (Work.Kernels.WFun τ - (1 - 8 * E + 24 * E ^ 2 - 32 * E ^ 3)) := by
    rw [hqE]; ring
  rw [hkey]
  have hq2 : ‖q‖ ^ 2 = ‖E‖ ^ 4 := by rw [hqE, norm_pow]; ring
  have hA : ‖(Work.Kernels.UFun τ - (1 + 8 * E + 24 * E ^ 2 + 32 * E ^ 3))
        + (Work.Kernels.WFun τ - (1 - 8 * E + 24 * E ^ 2 - 32 * E ^ 3))‖
      ≤ ‖Work.Kernels.UFun τ - (1 + 8 * E + 24 * E ^ 2 + 32 * E ^ 3)‖
        + ‖Work.Kernels.WFun τ - (1 - 8 * E + 24 * E ^ 2 - 32 * E ^ 3)‖ := norm_add_le _ _
  calc ‖(Work.Kernels.UFun τ - (1 + 8 * E + 24 * E ^ 2 + 32 * E ^ 3))
        + (Work.Kernels.WFun τ - (1 - 8 * E + 24 * E ^ 2 - 32 * E ^ 3))‖
      ≤ ‖Work.Kernels.UFun τ - (1 + 8 * E + 24 * E ^ 2 + 32 * E ^ 3)‖
        + ‖Work.Kernels.WFun τ - (1 - 8 * E + 24 * E ^ 2 - 32 * E ^ 3)‖ := hA
    _ ≤ (108 * C0 + 54 * C0 ^ 2 + 12 * C0 ^ 3 + C0 ^ 4 + 16) * ‖E‖ ^ 4
        + (108 * C0 + 54 * C0 ^ 2 + 12 * C0 ^ 3 + C0 ^ 4 + 16) * ‖E‖ ^ 4 := by linarith
    _ = 2 * (108 * C0 + 54 * C0 ^ 2 + 12 * C0 ^ 3 + C0 ^ 4 + 16) * ‖q‖ ^ 2 := by
        rw [hq2]; ring

theorem SecondOrderAtomIdentities :
    (Work.Asymptotics.IsBigOq (fun τ : UpperHalfPlane => Work.Kernels.DeltaFun τ
        - Work.Kernels.qParamFun τ + 24 * (Work.Kernels.qParamFun τ) ^ 2) 3) ∧
    (Work.Asymptotics.IsBigOq (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ
        * Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ
        - 216 * (Work.Kernels.qParamFun τ) ^ 2) 3) ∧
    (Work.Asymptotics.IsBigOq (fun τ : UpperHalfPlane => Work.Kernels.UFun τ
        + Work.Kernels.WFun τ - 2 - 48 * Work.Kernels.qParamFun τ) 2) :=
  ⟨DeltaThirdOrder, E4DeltaThirdOrder, Xi2SecondOrder⟩

end

end Work.Asymptotics.KhatE1
