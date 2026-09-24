import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.DirichletPolynomial

open Finset Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false

/-- Trivial bound: a Dirichlet polynomial of length `N` with 1-bounded coefficients
takes values of modulus at most `N + 1 ≤ 2N`.  Hence any threshold `V` realised at some
point satisfies `V ≤ 2N`. -/
theorem trivial_value_bound (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1)
    (t : ℝ) :
    ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t : ℂ))‖ ≤ 2 * (N : ℝ) := by
  have hterm : ∀ n ∈ Finset.Icc N (2 * N), ‖b n * (n : ℂ) ^ (I * (t : ℂ))‖ ≤ (1 : ℝ) := by
    intro n hn
    have hn1 : 0 < n := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1]
    have hre : (I * (t : ℂ)).re = 0 := by simp
    rw [hre, Real.rpow_zero, mul_one]
    exact hb n
  calc ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t : ℂ))‖
      ≤ ∑ n ∈ Finset.Icc N (2 * N), ‖b n * (n : ℂ) ^ (I * (t : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc N (2 * N), (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (N : ℝ) + 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
        have : 2 * N + 1 - N = N + 1 := by omega
        rw [this]
        push_cast
        ring
    _ ≤ 2 * (N : ℝ) := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith

end Commons.NumberTheory.DirichletPolynomial