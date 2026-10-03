import Mathlib

namespace Work.Rep

/-- If a continuous linear endomorphism `u` of a complex Hilbert space preserves a
subspace `K` (hypothesis `h1`) and its adjoint also preserves `K` (hypothesis `h2`),
then `u` commutes with the orthogonal projection onto `K`.

The proof is elementary: `u` furthermore maps the orthogonal complement `Kᗮ` into itself,
because for `y ∈ Kᗮ` and `k ∈ K` we have `⟪u y, k⟫ = ⟪y, u† k⟫ = 0` since `u† k ∈ K`.
Hencedecomposing `x = P x + (x - P x)` with `P = K.starProjection`, the term
`u (x - P x)` is killed by `P` while `u (P x) ∈ K` is fixed by `P`, giving
`P (u x) = u (P x)`. -/
theorem starProjection_mul_comm_of_invt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {K : Submodule ℂ E} [K.HasOrthogonalProjection] {u : E →L[ℂ] E} (h1 : ∀ x ∈ K, u x ∈ K) (h2 : ∀ x ∈ K, ContinuousLinearMap.adjoint u x ∈ K) : u * K.starProjection = K.starProjection * u := by
  -- `u` preserves the orthogonal complement of `K`
  have hmem : ∀ y ∈ Kᗮ, u y ∈ Kᗮ := by
    intro y hy
    rw [Submodule.mem_orthogonal] at hy ⊢
    intro k hk
    rw [← ContinuousLinearMap.adjoint_inner_left u y k]
    exact hy ((ContinuousLinearMap.adjoint u) k) (h2 k hk)
  apply ContinuousLinearMap.ext
  intro x
  show u (K.starProjection x) = K.starProjection (u x)
  have hP1 : K.starProjection (u (K.starProjection x)) = u (K.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr (h1 _ (Submodule.starProjection_apply_mem K x))
  have hP2 : K.starProjection (u (x - K.starProjection x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff K).mpr
      (hmem _ (Submodule.sub_starProjection_mem_orthogonal x))
  have hsplit : u x = u (K.starProjection x) + u (x - K.starProjection x) := by
    rw [← map_add, add_sub_cancel]
  rw [hsplit, map_add, hP1, hP2, add_zero]

end Work.Rep
