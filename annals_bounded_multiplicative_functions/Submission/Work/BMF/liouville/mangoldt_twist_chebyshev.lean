import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Polynomial Finset Real

/-- Crude Chebyshev bound for the twisted von Mangoldt sum:
`‖Σ_{n ≤ N} Λ(n) n^{-iu}‖ ≤ C N` for all real `u` and all real `N ≥ 1`.
Route: `‖(n:ℂ)^{-iu}‖ ≤ 1` for `n ≥ 1`, so the sum is at most `Σ_{n ≤ ⌊N⌋₊} Λ(n) = ψ(N)`, and
Mathlib's `Chebyshev.psi_le_const_mul_self` gives `ψ x ≤ (log 4 + 4) x`. -/
theorem mangoldt_twist_chebyshev :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ) (N : ℝ), 1 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 ⌊N⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖ ≤
        C * N := by
  refine ⟨Real.log 4 + 4, by positivity, ?_⟩
  intro u N hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  -- The twist has modulus one on the integers `n ≥ 1`.
  have htwist : ∀ n ∈ Finset.Icc 1 ⌊N⌋₊,
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
        = ArithmeticFunction.vonMangoldt n := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    have h : (-(Complex.I * (u : ℂ))).re = 0 := by simp
    rw [h]
    simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc ‖∑ n ∈ Finset.Icc 1 ⌊N⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊N⌋₊,
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, ArithmeticFunction.vonMangoldt n :=
        Finset.sum_congr rfl htwist
    _ ≤ Chebyshev.psi N := by
        rw [Chebyshev.psi_eq_sum_Icc]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro n hn
          simp only [Finset.mem_Icc] at hn ⊢
          omega
        · intro i _ _
          exact ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ (Real.log 4 + 4) * N := Chebyshev.psi_le_const_mul_self hN0

end Work.BMF.liouville
