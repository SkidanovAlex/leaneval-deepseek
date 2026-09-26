import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Modular.E4_qExpansion_coeff

namespace Work.Residues

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold ModularForm

noncomputable section

/-- The `q`-expansion coefficients of `E₄` satisfy a polynomial bound in the weight-four
case: `‖c_m‖ ≤ 240 · m⁴`.  (This is `Work.Modular.E4_qExpansion_coeff` combined with
`ArithmeticFunction.sigma_le_pow_succ`.) -/
private lemma E4_coeff_bound :
    ∀ m : ℕ, 2 ≤ m →
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

/-- `E₄ - 1 - 240 q = O(q²)` as `Im τ → ∞`: the second-order remainder of the `q`-expansion
of the weight-four Eisenstein series, written in the paper's `q`-parameter. -/
theorem E4FunSecondOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := qExpansion_tail_bound (r := 2) (f := (⇑ModularForm.E₄ : ℍ → ℂ))
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularForm.holo' ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄)
    240 4 (by norm_num) E4_coeff_bound
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff 0 = 1 := by
    simpa using Work.Modular.E4_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff 1 = 240 := by
    rw [Work.Modular.E4_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have hmain := h τ hτ
  rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1] at hmain
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ := by
    simp [Work.Kernels.qParamFun, Function.Periodic.qParam]
  rw [hq] at hmain
  convert hmain using 2
  ring

end

end Work.Residues
