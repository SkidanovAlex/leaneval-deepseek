import Mathlib
import Submission.Work.HP.Defs

/-!
# `f_a(-x) = (-1)^d f_a(x)`

The form `f_a(x) = ⟨a, ν_{d,n}(x)⟩` attached to a coefficient vector `a`, defined in
`Submission.Work.HP.Defs`, is homogeneous of degree `d`: replacing `x` by `-x` multiplies
it by `(-1)^d`.

This is the elementary homogeneity statement used in the Mobius/duality reduction, where
one pairs the solution `x` of `f_a(x) = 0` against the antipodal point `-x` of projective
space.

The proof is the direct computation, monomial by monomial: for an exponent vector
`m : Mon d n` one has `∏ i, (-x i)^{m i} = (-1)^{∑ i, m i} ∏ i, x i^{m i} = (-1)^d ∏ i, x i^{m i}`
because `∑ i, m i = d` by definition of `Mon d n`.
-/

namespace Work.HP.MDReduction

open Finset

/-- The Veronese monomials are homogeneous of degree `d`: `ν(-x)_m = (-1)^d ν(x)_m`. -/
lemma veronese_neg (d n : ℕ) (m : Mon d n) (x : Fin (n + 1) → ℤ) :
    veronese d n (-x) m = (-1) ^ d * veronese d n x m := by
  simp only [veronese]
  rw [show (∏ i : Fin (n + 1), (-x) i ^ ((m.1 i : ℕ)))
      = ∏ i, (-1) ^ ((m.1 i : ℕ)) * x i ^ ((m.1 i : ℕ)) from
      Finset.prod_congr rfl (fun i _ => neg_pow (x i) ((m.1 i : ℕ)))]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, m.2]

/-- Homogeneity of `f_a` of degree `d`: `f_a(-x) = (-1)^d f_a(x)`. -/
theorem formEval_neg (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    formEval d n a (-x) = (-1) ^ d * formEval d n a x := by
  simp only [formEval]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [veronese_neg d n m x]
  ring

end Work.HP.MDReduction
