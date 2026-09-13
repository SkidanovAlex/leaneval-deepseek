import Mathlib

namespace Commons.Algebra.BigOperators

open scoped BigOperators in
theorem sum_sq_third_index_decomp_four (a : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym1 : ∀ i j k, a i j k = a i k j) (hsym2 : ∀ i j k, a i j k = a j i k) :
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, a i j k ^ 2) =
      6 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
             if i < j ∧ j < k then a i j k ^ 2 else 0)
      + 3 * (∑ i : Fin 4, ∑ j : Fin 4, if i = j then 0 else a i i j ^ 2)
      + (∑ i : Fin 4, a i i i ^ 2) := by
  have swap01 : ∀ i j k : Fin 4, j < i → a i j k = a j i k := fun i j k _ => hsym2 i j k
  have swap12 : ∀ i j k : Fin 4, k < j → a i j k = a i k j := fun i j k _ => hsym1 i j k
  simp only [Fin.sum_univ_four]
  simp
  simp (disch := decide) only [swap01, swap12]
  ring

end Commons.Algebra.BigOperators
