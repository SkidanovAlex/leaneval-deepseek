import Mathlib
import Submission.RS

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace RudinShapiro

/-- The sum of the first `m` monomials of `P t`. -/
def Psum (t m : ℕ) : ℂ[X] := ∑ k ∈ Finset.range m, C ((P t).coeff k) * X ^ k

/-- The sum of the first `m` monomials of `Q t`. -/
def Qsum (t m : ℕ) : ℂ[X] := ∑ k ∈ Finset.range m, C ((Q t).coeff k) * X ^ k

@[simp] lemma Psum_zero (t : ℕ) : Psum t 0 = 0 := by simp [Psum]
@[simp] lemma Qsum_zero (t : ℕ) : Qsum t 0 = 0 := by simp [Qsum]

lemma eval_Psum (t m : ℕ) (z : ℂ) :
    (Psum t m).eval z = ∑ k ∈ Finset.range m, (P t).coeff k * z ^ k := by
  rw [Psum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp

lemma eval_Qsum (t m : ℕ) (z : ℂ) :
    (Qsum t m).eval z = ∑ k ∈ Finset.range m, (Q t).coeff k * z ^ k := by
  rw [Qsum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp

end RudinShapiro
end Submission
