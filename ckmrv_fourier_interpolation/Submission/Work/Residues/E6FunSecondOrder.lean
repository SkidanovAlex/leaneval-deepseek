import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Modular.E6_qExpansion_coeff

/-!
# The second-order expansion of `E₆` at the cusp

The weight-six Eisenstein series has `q`-expansion
`E₆(τ) = 1 - 504 σ₅(1) q - 504 ∑_{n ≥ 2} σ₅(n) qⁿ = 1 - 504 q + O(q²)`,
since `σ₅(1) = 1`.  This file records the resulting second-order bound at the cusp
`i∞` (equivalently on `{τ : 1 ≤ τ.im}`), which is the input used in the residue
computation of CKMRV, Section 5.

The proof combines

* the coefficient computation `Work.Modular.E6_qExpansion_coeff`,
* the divisor-sum bound `σ₅(m) ≤ m⁶` (`ArithmeticFunction.sigma_le_pow_succ`),
* the general tail estimate `Work.Residues.qExpansion_tail_bound` with `r = 2`.
-/

namespace Work.Residues

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold ModularForm

noncomputable section

/-- The `q`-expansion coefficients of `E₆` of index `≥ 2` grow at most like `504 m⁶`:
`‖coeff m‖ = 504 σ₅(m) ≤ 504 m⁶`.  This is the coefficient input for
`Work.Residues.qExpansion_tail_bound` in the second-order expansion of `E₆`. -/
theorem E6_qExpansion_coeff_tail (m : ℕ) (hm : 2 ≤ m) :
    ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m‖ ≤ 504 * (m : ℝ) ^ 6 := by
  rw [Work.Modular.E6_qExpansion_coeff]
  have hm0 : m ≠ 0 := by omega
  rw [if_neg hm0, norm_mul]
  have h504 : ‖(-504 : ℂ)‖ = (504 : ℝ) := by norm_num
  rw [h504, Complex.norm_natCast]
  have hσ : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m : ℝ) ^ 6 := by
    have h := ArithmeticFunction.sigma_le_pow_succ 5 m
    exact_mod_cast h
  nlinarith

/-- The second-order bound for `E₆` at the cusp: on `{τ : 1 ≤ τ.im}` the function
`E₆ - 1 + 504 q` is bounded by `C ‖q‖²`. -/
theorem E6FunSecondOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  -- `E₆` is periodic of period one, holomorphic on `ℍ` and bounded at the cusp.
  have hper : Function.Periodic (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E6Fun := ModularForm.holo' ModularForm.E₆
  have hbdd : IsBoundedAtImInfty Work.Kernels.E6Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₆
  -- Tail estimate for the `q`-expansion truncated after the linear term.
  obtain ⟨C, hC, hb⟩ :=
    Work.Residues.qExpansion_tail_bound 2 hper hhol hbdd 504 6 (by norm_num)
      (fun m hm => E6_qExpansion_coeff_tail m hm)
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h := hb τ hτ
  -- The constant and linear coefficients of the `q`-expansion of `E₆` are `1` and `-504`.
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  have hsum : (∑ m ∈ Finset.range 2,
      (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      = 1 - 504 * Function.Periodic.qParam 1 (τ : ℂ) := by
    have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 0 = 1 := by
      rw [Work.Modular.E6_qExpansion_coeff]; simp
    have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 1 = -504 := by
      rw [Work.Modular.E6_qExpansion_coeff]
      norm_num [ArithmeticFunction.sigma_one]
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
    ring
  rw [hsum, hq] at h
  rw [show Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ
      = Work.Kernels.E6Fun τ - (1 - 504 * Work.Kernels.qParamFun τ) by ring]
  exact h

end

end Work.Residues
