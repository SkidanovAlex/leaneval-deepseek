import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E6_qExpansion_coeff

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold ModularForm

noncomputable section

/-!
# The three-term `q`-expansions of `E₄` and `E₆` at the cusp

`E₄ = 1 + 240 q + 2160 q² + O(q³)` and `E₆ = 1 - 504 q - 16632 q² + O(q³)` on `{1 ≤ Im τ}`,
with `240 σ₃(2) = 2160` and `-504 σ₅(2) = -16632`.  These are the `r = 3` instances of
`Work.Residues.qExpansion_tail_bound`, refining the `r = 2` statements
`Work.Residues.E4FunSecondOrder` and `Work.Residues.E6FunSecondOrder`.
-/

private lemma E4_coeff_bound3 :
    ∀ m : ℕ, 3 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff m‖
        ≤ 240 * (m : ℝ) ^ 4 := by
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hc : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff m
      = (240 : ℂ) * ((ArithmeticFunction.sigma 3 m : ℕ) : ℂ) := by
    rw [Work.Modular.E4_qExpansion_coeff m, if_neg hm0]
  have hsig : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m : ℝ) ^ 4 := by
    have h' : ArithmeticFunction.sigma 3 m ≤ m ^ 4 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 3 m
    exact_mod_cast h'
  rw [hc, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hsig (by norm_num)

private lemma E6_coeff_bound3 :
    ∀ m : ℕ, 3 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff m‖
        ≤ 504 * (m : ℝ) ^ 6 := by
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hc : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff m
      = (-504 : ℂ) * ((ArithmeticFunction.sigma 5 m : ℕ) : ℂ) := by
    rw [Work.Modular.E6_qExpansion_coeff m, if_neg hm0]
  have hsig : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m : ℝ) ^ 6 := by
    have h' : ArithmeticFunction.sigma 5 m ≤ m ^ 6 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 5 m
    exact_mod_cast h'
  rw [hc, norm_mul]
  have h504 : ‖(-504 : ℂ)‖ = (504 : ℝ) := by norm_num
  rw [h504, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hsig (by norm_num)

/-- `E₄ = 1 + 240 q + 2160 q² + O(q³)` on `{1 ≤ Im τ}`. -/
theorem e4ThreeTerm :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ
        - 2160 * Work.Kernels.qParamFun τ ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.qExpansion_tail_bound (r := 3)
    (f := (⇑ModularForm.E₄ : ℍ → ℂ))
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularForm.holo' ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄)
    240 4 (by norm_num) E4_coeff_bound3
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff 0 = 1 := by
    simpa using Work.Modular.E4_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff 1 = 240 := by
    rw [Work.Modular.E4_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h2 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff 2 = 2160 := by
    rw [Work.Modular.E4_qExpansion_coeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have hmain := h τ hτ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2] at hmain
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ := by
    simp [Work.Kernels.qParamFun, Function.Periodic.qParam]
  rw [hq] at hmain
  convert hmain using 2
  ring

/-- `E₆ = 1 - 504 q - 16632 q² + O(q³)` on `{1 ≤ Im τ}`. -/
theorem e6ThreeTerm :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ
        + 16632 * Work.Kernels.qParamFun τ ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.qExpansion_tail_bound (r := 3)
    (f := (⇑ModularForm.E₆ : ℍ → ℂ))
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL)
    (ModularForm.holo' ModularForm.E₆) (ModularFormClass.bdd_at_infty ModularForm.E₆)
    504 6 (by norm_num) E6_coeff_bound3
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff 0 = 1 := by
    simpa using Work.Modular.E6_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff 1 = -504 := by
    rw [Work.Modular.E6_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h2 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff 2 = -16632 := by
    rw [Work.Modular.E6_qExpansion_coeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have hmain := h τ hτ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2] at hmain
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ := by
    simp [Work.Kernels.qParamFun, Function.Periodic.qParam]
  rw [hq] at hmain
  convert hmain using 2
  ring

/-- **The three-term `q`-expansions of `E₄` and `E₆`.** -/
theorem EisensteinThreeTerm :
    ∃ C : ℝ, 0 < C ∧
      (∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ
          - 2160 * Work.Kernels.qParamFun τ ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3) ∧
      (∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ
          + 16632 * Work.Kernels.qParamFun τ ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3) := by
  obtain ⟨C4, hC4, h4⟩ := e4ThreeTerm
  obtain ⟨C6, hC6, h6⟩ := e6ThreeTerm
  refine ⟨max C4 C6, lt_max_of_lt_left hC4, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · refine le_trans (h4 τ hτ) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left C4 C6) (by positivity)
  · refine le_trans (h6 τ hτ) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right C4 C6) (by positivity)

end

end Work.Asymptotics.KhatE1Core
