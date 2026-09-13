import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.unusedVariables false

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
open scoped RealInnerProductSpace in
theorem coord_minor_add_expansion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (b : OrthonormalBasis (Fin 4) ℝ E) {A M : E →L[ℝ] E}
    (hA : A.IsSymmetric) (hM : M.IsSymmetric) :
    (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (⟪(A + M) (b i), b i⟫ * ⟪(A + M) (b j), b j⟫ - ⟪(A + M) (b i), b j⟫ ^ 2) else 0)
      = (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
          (⟪A (b i), b i⟫ * ⟪A (b j), b j⟫ - ⟪A (b i), b j⟫ ^ 2) else 0)
        + (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
          (⟪M (b i), b i⟫ * ⟪M (b j), b j⟫ - ⟪M (b i), b j⟫ ^ 2) else 0)
        + (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
            (⟪A (b i), b i⟫ * ⟪M (b j), b j⟫ + ⟪M (b i), b i⟫ * ⟪A (b j), b j⟫
              - 2 * ⟪A (b i), b j⟫ * ⟪M (b i), b j⟫) else 0) := by
  -- Pointwise algebraic identity obtained by expanding `A + M`.
  have key : ∀ i j : Fin 4,
      (⟪(A + M) (b i), b i⟫ * ⟪(A + M) (b j), b j⟫ - ⟪(A + M) (b i), b j⟫ ^ 2)
        = (⟪A (b i), b i⟫ * ⟪A (b j), b j⟫ - ⟪A (b i), b j⟫ ^ 2)
          + (⟪M (b i), b i⟫ * ⟪M (b j), b j⟫ - ⟪M (b i), b j⟫ ^ 2)
          + (⟪A (b i), b i⟫ * ⟪M (b j), b j⟫ + ⟪M (b i), b i⟫ * ⟪A (b j), b j⟫
              - 2 * ⟪A (b i), b j⟫ * ⟪M (b i), b j⟫) := by
    intro i j
    simp only [add_apply, inner_add_left]
    ring
  -- Distribute the `if ... then ... else 0` over the three summands.
  have hterm : ∀ i j : Fin 4,
      (if i < j then
          (⟪(A + M) (b i), b i⟫ * ⟪(A + M) (b j), b j⟫ - ⟪(A + M) (b i), b j⟫ ^ 2) else 0)
        = (if i < j then (⟪A (b i), b i⟫ * ⟪A (b j), b j⟫ - ⟪A (b i), b j⟫ ^ 2) else 0)
          + (if i < j then (⟪M (b i), b i⟫ * ⟪M (b j), b j⟫ - ⟪M (b i), b j⟫ ^ 2) else 0)
          + (if i < j then
              (⟪A (b i), b i⟫ * ⟪M (b j), b j⟫ + ⟪M (b i), b i⟫ * ⟪A (b j), b j⟫
                - 2 * ⟪A (b i), b j⟫ * ⟪M (b i), b j⟫) else 0) := by
    intro i j
    by_cases h : i < j
    · simp only [h, if_true]
      exact key i j
    · simp only [h, if_false]
      ring
  -- Sum the pointwise identity over `i`.
  have houter : ∀ j : Fin 4,
      (∑ i : Fin 4, if i < j then
          (⟪(A + M) (b i), b i⟫ * ⟪(A + M) (b j), b j⟫ - ⟪(A + M) (b i), b j⟫ ^ 2) else 0)
        = (∑ i : Fin 4, if i < j then
            (⟪A (b i), b i⟫ * ⟪A (b j), b j⟫ - ⟪A (b i), b j⟫ ^ 2) else 0)
          + (∑ i : Fin 4, if i < j then
            (⟪M (b i), b i⟫ * ⟪M (b j), b j⟫ - ⟪M (b i), b j⟫ ^ 2) else 0)
          + (∑ i : Fin 4, if i < j then
              (⟪A (b i), b i⟫ * ⟪M (b j), b j⟫ + ⟪M (b i), b i⟫ * ⟪A (b j), b j⟫
                - 2 * ⟪A (b i), b j⟫ * ⟪M (b i), b j⟫) else 0) := by
    intro j
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hterm i j)
  -- Sum over `j` and split the resulting sum of sums.
  rw [Finset.sum_congr rfl (fun j _ => houter j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

end Commons.Analysis.Sigma2