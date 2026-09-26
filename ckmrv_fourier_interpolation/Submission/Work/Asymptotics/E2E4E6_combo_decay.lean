import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Rigidity.hasSum_qExpansion_cusp_decay
import Submission.Work.Modular.E2_qExpansion_coeff
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E6_qExpansion_coeff

namespace Work.Asymptotics

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- The combination `12(E₂-1) - 3(E₄-1) - 2(E₆-1)` vanishes to order two at the cusp. Its `q`-expansion is `Σ_{m ≥ 1} (12 a_m - 3 b_m - 2 c_m) q^m` where `E₂ = Σ a_m q^m`, `E₄ = Σ b_m q^m`, `E₆ = Σ c_m q^m`; the coefficients in degrees `0` and `1` vanish because the constant term is `12·0 - 3·0 - 2·0 = 0` (each `E_k - 1` vanishes at the cusp) and `12·(-24) - 3·240 - 2·(-504) = -288 - 720 + 1008 = 0` (the constants `a₁ = -24`, `b₁ = 240`, `c₁ = -504` come from `Work.Modular.E2_qExpansion_coeff`, `E4_qExpansion_coeff`, `E6_qExpansion_coeff`). Hence `‖12(E₂ τ - 1) - 3(E₄ τ - 1) - 2(E₆ τ - 1)‖ ≤ C (exp (-2 π im τ))²` for `im τ ≥ H`. This is the arithmetic input for the `d = 24` asymptotics of `K_+`. Suggested route: apply `Work.Rigidity.hasSum_qExpansion_cusp_decay` to the quotient of the combination by `q` (whose `q`-expansion again has vanishing constant term); the `HasSum` expansions are `EisensteinSeries.hasSum_qExpansion_E2` and `ModularForm.hasSum_qExpansion` for `E₄`, `E₆`. -/
theorem E2E4E6_combo_decay : ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im →
    ‖(12 : ℂ) * (Work.Kernels.E2Fun τ - 1) - (3 : ℂ) * (Work.Kernels.E4Fun τ - 1)
      - (2 : ℂ) * (Work.Kernels.E6Fun τ - 1)‖
      ≤ C * (Real.exp (-(2 * Real.pi * τ.im))) ^ 2 := by
  -- The `q`-expansion coefficients of `E₂`, `E₄`, `E₆` and of their combination.
  set a : ℕ → ℂ := fun m => (UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun).coeff m with ha
  set b : ℕ → ℂ := fun m => (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m with hb
  set c : ℕ → ℂ := fun m => (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m with hc
  set d : ℕ → ℂ := fun m => 12 * a m - 3 * b m - 2 * c m with hd
  -- The first two coefficients of each expansion.
  have ha0 : a 0 = 1 := by
    simp only [ha]; rw [Work.Modular.E2_qExpansion_coeff]; simp
  have ha1 : a 1 = -24 := by
    simp only [ha]; rw [Work.Modular.E2_qExpansion_coeff]; norm_num
  have hb0 : b 0 = 1 := by
    simp only [hb]; rw [Work.Modular.E4_qExpansion_coeff]; simp
  have hb1 : b 1 = 240 := by
    simp only [hb]; rw [Work.Modular.E4_qExpansion_coeff]; norm_num
  have hc0 : c 0 = 1 := by
    simp only [hc]; rw [Work.Modular.E6_qExpansion_coeff]; simp
  have hc1 : c 1 = -504 := by
    simp only [hc]; rw [Work.Modular.E6_qExpansion_coeff]; norm_num
  -- The constant terms of `Σ d_m q^m` and of its quotient by `q`.
  have hd0 : d 0 = 7 := by simp only [hd, ha0, hb0, hc0]; norm_num
  have hd1 : d 1 = 0 := by simp only [hd, ha1, hb1, hc1]; norm_num
  -- The `q`-expansion of `E₂`.
  have hE2 : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => a m * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (Work.Kernels.E2Fun τ) := by
    intro τ
    have h := EisensteinSeries.hasSum_qExpansion_E2 τ
    have happ : ∀ m : ℕ,
        a m = (UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun).coeff m := by
      intro m; simp only [ha]
    have haeq : ∀ m : ℕ,
        (UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun).coeff m
          = (if m = 0 then 1 else -24 * ((ArithmeticFunction.sigma 1 m : ℕ) : ℂ)) := by
      intro m; rw [Work.Modular.E2_qExpansion_coeff]
    have hq : Function.Periodic.qParam 1 (τ : ℂ)
        = Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ)) := by
      rw [Function.Periodic.qParam, Complex.ofReal_one, div_one]
    simpa [happ, haeq, hq, smul_eq_mul] using h
  -- The `q`-expansion of `E₄`.
  have hE4 : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => b m * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (Work.Kernels.E4Fun τ) := by
    intro τ
    have h := ModularForm.hasSum_qExpansion (ModularForm.E₄)
      (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods_SL τ
    have happ : ∀ m : ℕ,
        b m = (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m := by
      intro m; simp only [hb]
    have hbeq : ∀ m : ℕ,
        (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m
          = (if m = 0 then 1 else 240 * ((ArithmeticFunction.sigma 3 m : ℕ) : ℂ)) := by
      intro m; rw [Work.Modular.E4_qExpansion_coeff]
    simpa [happ, hbeq] using h
  -- The `q`-expansion of `E₆`.
  have hE6 : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (Work.Kernels.E6Fun τ) := by
    intro τ
    have h := ModularForm.hasSum_qExpansion (ModularForm.E₆)
      (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods_SL τ
    have happ : ∀ m : ℕ,
        c m = (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m := by
      intro m; simp only [hc]
    have hceq : ∀ m : ℕ,
        (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m
          = (if m = 0 then 1 else -504 * ((ArithmeticFunction.sigma 5 m : ℕ) : ℂ)) := by
      intro m; rw [Work.Modular.E6_qExpansion_coeff]
    simpa [happ, hceq] using h
  -- The `q`-expansion of the linear combination `12 E₂ - 3 E₄ - 2 E₆`.
  have hE : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => d m * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ
          - 2 * Work.Kernels.E6Fun τ) := by
    intro τ
    have h1 : HasSum (fun m : ℕ => (12 * a m) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (12 * Work.Kernels.E2Fun τ) := by
      simpa [mul_assoc] using (hE2 τ).mul_left (12 : ℂ)
    have h3 : HasSum (fun m : ℕ => (3 * b m) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (3 * Work.Kernels.E4Fun τ) := by
      simpa [mul_assoc] using (hE4 τ).mul_left (3 : ℂ)
    have h5 : HasSum (fun m : ℕ => (2 * c m) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (2 * Work.Kernels.E6Fun τ) := by
      simpa [mul_assoc] using (hE6 τ).mul_left (2 : ℂ)
    have hcomb := (h1.sub h3).sub h5
    simpa [hd, sub_mul] using hcomb
  -- Dividing by `q`, the expansion has vanishing constant term `d 1`.
  have hG : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => d (m + 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        ((12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ - 2 * Work.Kernels.E6Fun τ
            - d 0) / Function.Periodic.qParam 1 (τ : ℂ)) := by
    intro τ
    have hqp : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
    have h2 : HasSum
        (fun m : ℕ => d (m + 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1))
        ((12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ - 2 * Work.Kernels.E6Fun τ)
          - d 0) :=
      (hasSum_nat_add_iff
        (f := fun m : ℕ => d m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) 1).mpr
        (by simpa using hE τ)
    have hfun : (fun m : ℕ => d (m + 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)
          / Function.Periodic.qParam 1 (τ : ℂ))
        = fun m => d (m + 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
      funext m
      rw [pow_succ, mul_div_assoc, mul_div_cancel_right₀ _ hqp]
    simpa only [hfun] using h2.div_const (Function.Periodic.qParam 1 (τ : ℂ))
  -- The quotient is bounded at the cusp, hence the combination is `O(q²)`.
  obtain ⟨A, B, hB, hAB⟩ := Work.Rigidity.hasSum_qExpansion_cusp_decay
    (F := fun τ : UpperHalfPlane => (12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ
      - 2 * Work.Kernels.E6Fun τ - d 0) / Function.Periodic.qParam 1 (τ : ℂ))
    (c := fun m => d (m + 1)) hG
  refine ⟨A, max B 1, lt_of_lt_of_le one_pos (le_max_right B 1), fun τ hτ => ?_⟩
  have hbnd : ‖(12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ
        - 2 * Work.Kernels.E6Fun τ - d 0) / Function.Periodic.qParam 1 (τ : ℂ)‖
      ≤ B * Real.exp (-(2 * Real.pi * τ.im)) := by
    simpa [hd1] using hAB τ hτ
  have hqp : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hnorm : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [Function.Periodic.norm_qParam]
    congr 1
    rw [UpperHalfPlane.coe_im]
    ring
  have hmul : ((12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ
          - 2 * Work.Kernels.E6Fun τ - d 0) / Function.Periodic.qParam 1 (τ : ℂ))
        * Function.Periodic.qParam 1 (τ : ℂ)
      = 12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ - 2 * Work.Kernels.E6Fun τ - d 0 :=
    div_mul_cancel₀ _ hqp
  have heq : (12 : ℂ) * (Work.Kernels.E2Fun τ - 1) - 3 * (Work.Kernels.E4Fun τ - 1)
      - 2 * (Work.Kernels.E6Fun τ - 1)
      = (12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ
          - 2 * Work.Kernels.E6Fun τ) - d 0 := by
    rw [hd0]; ring
  rw [heq]
  calc ‖(12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ
          - 2 * Work.Kernels.E6Fun τ) - d 0‖
      = ‖((12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ
            - 2 * Work.Kernels.E6Fun τ - d 0) / Function.Periodic.qParam 1 (τ : ℂ))
          * Function.Periodic.qParam 1 (τ : ℂ)‖ := by rw [hmul]
    _ = ‖(12 * Work.Kernels.E2Fun τ - 3 * Work.Kernels.E4Fun τ
            - 2 * Work.Kernels.E6Fun τ - d 0) / Function.Periodic.qParam 1 (τ : ℂ)‖
          * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ := by rw [norm_mul]
    _ ≤ (B * Real.exp (-(2 * Real.pi * τ.im))) * Real.exp (-(2 * Real.pi * τ.im)) := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_right hbnd (Real.exp_nonneg _)
    _ = B * (Real.exp (-(2 * Real.pi * τ.im))) ^ 2 := by ring
    _ ≤ max B 1 * (Real.exp (-(2 * Real.pi * τ.im))) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left B 1) (sq_nonneg _)

end Work.Asymptotics
