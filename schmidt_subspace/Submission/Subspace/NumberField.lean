import Mathlib

/-!
# Coefficient field of the linear forms

First bottom-up milestone for the subspace theorem: the (finitely many)
algebraic coefficients `L i j : ℂ` lie in a common number field — an
`IntermediateField ℚ ℂ` of finite dimension over `ℚ`.
-/

open scoped BigOperators

namespace Submission.Subspace

section NumberField

variable {σ : Type*} [Fintype σ]

/-- The finitely many algebraic coefficients of `L` lie in a single number
field `K : IntermediateField ℚ ℂ` (finite-dimensional over `ℚ`). -/
theorem exists_numberField_of_algebraic_coefficients (L : σ → σ → ℂ)
    (alg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ ∀ i j, L i j ∈ K := by
  classical
  let t : σ × σ → IntermediateField ℚ ℂ := fun ij => IntermediateField.adjoin ℚ {L ij.1 ij.2}
  let K : IntermediateField ℚ ℂ := ⨆ ij ∈ (Finset.univ : Finset (σ × σ)), t ij
  refine ⟨K, ?_, ?_⟩
  · -- K is finite dimensional over ℚ
    rw [show K = ⨆ ij ∈ (Finset.univ : Finset (σ × σ)), t ij by rfl]
    apply IntermediateField.finiteDimensional_iSup_of_finset'
    intro ij hij
    -- t ij = adjoin ℚ {L ...} is finite-dimensional since L ... is algebraic
    apply IntermediateField.adjoin.finiteDimensional
    exact (isAlgebraic_iff_isIntegral (K := ℚ) (A := ℂ)).mp (alg ij.1 ij.2)
  · intro i j
    -- L i j ∈ t (i, j) ⊆ K
    have h1 : L i j ∈ t (i, j) := by
      exact IntermediateField.subset_adjoin ℚ ({L i j} : Set ℂ) (by simp)
    exact (le_biSup t (Finset.mem_univ (i, j))) h1

end NumberField

end Submission.Subspace
