import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace Commons.Analysis.InnerProductSpace

/-- Given a subspace `K₁` contained in a finite-dimensional subspace `K₂` of an inner product
space, the dimension of the intersection of the orthogonal complement of `K₁` with `K₂`
equals the difference of the dimensions. -/
theorem finrank_inf_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (V₀ W : Submodule ℝ E) (h : W ≤ V₀) :
    Module.finrank ℝ ↥(V₀ ⊓ W.orthogonal)
      = Module.finrank ℝ ↥V₀ - Module.finrank ℝ ↥W := by
  have hdim := Submodule.finrank_add_inf_finrank_orthogonal (𝕜 := ℝ) h
  rw [inf_comm] at hdim
  omega

end Commons.Analysis.InnerProductSpace