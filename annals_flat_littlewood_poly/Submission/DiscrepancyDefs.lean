import Mathlib

noncomputable section
open scoped BigOperators

namespace Submission
namespace Discrepancy

/-- Euclidean inner product of two real vectors. -/
def dot {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∑ i : Fin n, a i * b i

/-- Euclidean norm of a real vector. -/
def eucl {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i : Fin n, (v i) ^ 2)

/-- Supremum of the absolute values of the coordinates of a vector. -/
def supAbs {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ i : Fin n, x = |v i|}

lemma eucl_sq {n : ℕ} (v : Fin n → ℝ) : (eucl v) ^ 2 = ∑ i : Fin n, (v i) ^ 2 := by
  rw [eucl, Real.sq_sqrt]
  exact Finset.sum_nonneg (by intro i hi; positivity)

lemma eucl_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ eucl v := by
  rw [eucl]
  positivity

lemma dot_comm {n : ℕ} (a b : Fin n → ℝ) : dot a b = dot b a := by
  simp [dot, mul_comm]

lemma dot_add_sub {n : ℕ} (x x0 y : Fin n → ℝ) : dot (fun i => x i - x0 i) y = dot x y - dot x0 y := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

end Discrepancy
end Submission
