import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace Commons.Analysis.InnerProductSpace

open scoped RealInnerProductSpace

/-- **The stabiliser of a vector acts transitively on the level sets of `⟪·, e⟫` on spheres.**
If `ξ` and `η` have the same norm and the same inner product with `e`, then there is an
orthogonal transformation `k` of `E` fixing `e` and sending `ξ` to `η`.

(Equivalently: the orbit of `ξ` under the stabiliser `{k : E ≃ₗᵢ[ℝ] E // k e = e}` is exactly
the set `{x // ‖x‖ = ‖ξ‖ ∧ ⟪x, e⟫ = ⟪ξ, e⟫}`.)  This is what makes `𝓡 f` factor through
`ξ ↦ ⟪ξ, e⟫` for functions `f` invariant under that stabiliser.

Proof route: the Gram data of `(e, ξ)` and `(e, η)` agree, so extending `{e, ξ}` (respectively
`{e, η}`) to orthonormal bases with matching index sets
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`) yields two orthonormal bases `b₁`,
`b₂` with `b₁ i = e`, `b₂ i = e` and `b₁ j = ξ`, `b₂ j = η` for the same `i`, `j`; the composite
of the induced linear isometry equivalences `b₁.repr` and `b₂.repr` is the desired `k`. -/
theorem orthogonal_transitive_level_sets {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (e ξ η : E)
    (hξ : ‖ξ‖ = ‖η‖) (h : ⟪ξ, e⟫ = ⟪η, e⟫) :
    ∃ k : E ≃ₗᵢ[ℝ] E, k e = e ∧ k ξ = η := by
  refine ⟨Submodule.reflection (ℝ ∙ (ξ - η))ᗮ, ?_, ?_⟩
  · apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_left, h, sub_self]
  · exact Submodule.reflection_sub hξ

end Commons.Analysis.InnerProductSpace