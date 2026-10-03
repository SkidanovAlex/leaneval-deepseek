import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

/-- Orthogonal projection commutes with a linear isometry, in the form relevant when the subspace
is sitting inside the range: if `V ≤ range Ψ`, then `Ψ⁻¹ V` is the subspace of `E` projecting onto
`V`, and projecting in `E` and then applying `Ψ` is the same as applying `Ψ` and then projecting
in `F`. -/
theorem starProjection_comap_isometry {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (Ψ : E →ₗᵢ[ℂ] F) (V : Submodule ℂ F) [V.HasOrthogonalProjection] (hV : V ≤ LinearMap.range Ψ.toLinearMap) [(V.comap Ψ.toLinearMap).HasOrthogonalProjection] (u : E) : Ψ ((V.comap Ψ.toLinearMap).starProjection u) = V.starProjection (Ψ u) := by
  -- The projection onto `V` is characterised by membership in `V` together with orthogonality of
  -- the residual; `Ψ (W.starProjection u)` has both properties for the vector `Ψ u`.
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · -- `Ψ (W.starProjection u) ∈ V` because `W.starProjection u ∈ W = V.comap Ψ`.
    exact (Submodule.mem_comap).1 (Submodule.starProjection_apply_mem _ u)
  · intro w hw
    -- Every `w ∈ V` is `Ψ x` with `x ∈ W`, since `V ≤ range Ψ`.
    rcases hV hw with ⟨x, rfl⟩
    have hxW : x ∈ V.comap Ψ.toLinearMap := hw
    -- The residual is orthogonal to `V` by isometry, from `u - W.starProjection u ∈ Wᗮ`.
    rw [← map_sub]
    change inner ℂ (Ψ (u - (V.comap Ψ.toLinearMap).starProjection u)) (Ψ x) = 0
    rw [Ψ.inner_map_map]
    exact (Submodule.mem_orthogonal' (K := V.comap Ψ.toLinearMap)
      (u - (V.comap Ψ.toLinearMap).starProjection u)).1
      (Submodule.sub_starProjection_mem_orthogonal u) x hxW

end Work.ORP311
