import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas

open Polynomial

namespace Commons.Algebra.Polynomial

/-- Polynomial composition by a nonconstant polynomial is injective (over a ring with no zero
divisors). -/
lemma comp_injective_of_natDegree_pos {R : Type*} [Ring R] [NoZeroDivisors R]
    {q : R[X]} (hq : 0 < q.natDegree) : Function.Injective (fun p : R[X] => p.comp q) := by
  intro p₁ p₂ h
  simp only at h
  have hcomp : (p₁ - p₂).comp q = 0 := by
    rw [sub_comp, h, sub_self]
  have hzero : p₁ - p₂ = 0 := by
    rw [comp_eq_zero_iff] at hcomp
    rcases hcomp with h0 | ⟨_, hc⟩
    · exact h0
    · exfalso
      rw [hc, natDegree_C] at hq
      exact absurd hq (lt_irrefl 0)
  exact sub_eq_zero.mp hzero

end Commons.Algebra.Polynomial
