import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Ring.GeomSum

open Polynomial
open scoped BigOperators

namespace Commons.Algebra.Polynomial

lemma X_pow_sub_C_pow_eq_mul_sum {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    X ^ n - C (a ^ n) = (X - C a) * ∑ i ∈ Finset.range n, X ^ i * C (a ^ (n - 1 - i)) := by
  calc
    X ^ n - C (a ^ n) = (∑ i ∈ Finset.range n, X ^ i * (C a) ^ (n - 1 - i)) * (X - C a) := by
      rw [C_pow]
      exact (geom_sum₂_mul X (C a) n).symm
    _ = (X - C a) * ∑ i ∈ Finset.range n, X ^ i * C (a ^ (n - 1 - i)) := by
      rw [mul_comm]
      congr 1
      simp_rw [C_pow]

end Commons.Algebra.Polynomial