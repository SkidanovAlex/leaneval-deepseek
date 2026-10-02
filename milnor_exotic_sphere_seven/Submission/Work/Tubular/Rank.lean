import Submission.Work.Tubular.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The rank of the tangent and of the normal bundle

The normal bundle of a closed `8`-dimensional submanifold of `ℝ^N` has rank `N - 8`
(`Work.Tubular.finrank_normalSpace`), because the tangent space is the range of the injective
derivative (`Work.Tubular.finrank_tangentSpace`) and `module.finrank` is additive over the orthogonal
direct sum decomposition `T_x ⊕ ν_x = ℝ^N`.

This is the numerical content of item 1 of the chapter's request ("its normal bundle `ν` of rank
`k = N - 8`"), and it is what produces a point of the sphere bundle — hence a basepoint of the Thom
space — as soon as `N > 8`.
-/

open scoped Manifold ContDiff Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {N : ℕ}

/-- **The tangent space of the image of an embedding is `8`-dimensional.**  It is the range of the
Fréchet derivative, which is injective by hypothesis (`EmbeddingData.injective_mfderiv`), and the
domain `TangentSpace (𝓡 8) x` is `ℝ^8`. -/
theorem finrank_tangentSpace (E : EmbeddingData V N) (x : V.pt) :
    Module.finrank ℝ (tangentSpace E x) = 8 := by
  have hinj : Function.Injective (mfderiv (𝓡 8) 𝓘(ℝ, Euc N) E.e x) := E.injective_mfderiv x
  have h := LinearMap.finrank_range_of_inj
    (f := (mfderiv (𝓡 8) 𝓘(ℝ, Euc N) E.e x).toLinearMap) hinj
  have h2 : Module.finrank ℝ (TangentSpace (𝓡 8) x) = 8 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 8
    simp
  rw [tangentSpace]
  exact h.trans h2

/-- **The normal space of an embedding of an `8`-manifold into `ℝ^N` has dimension `N - 8`.** -/
theorem finrank_normalSpace (E : EmbeddingData V N) (x : V.pt) :
    Module.finrank ℝ (normalSpace E x) = N - 8 := by
  have h := Submodule.finrank_add_finrank_orthogonal (tangentSpace E x)
  rw [normalSpace]
  have h3 : Module.finrank ℝ (tangentSpace E x) = 8 := finrank_tangentSpace E x
  have h2 : Module.finrank ℝ (Euc N) = N := by simp [Euc]
  omega

/-- The normal space is non-trivial as soon as the codimension is positive. -/
theorem normalSpace_ne_bot (E : EmbeddingData V N) (x : V.pt) (hN : 8 < N) :
    normalSpace E x ≠ ⊥ := by
  intro h
  have := finrank_normalSpace E x
  rw [h] at this
  simp at this
  omega

/-- **A non-zero normal vector exists at every point** when the codimension is positive. -/
theorem exists_mem_normalSpace_ne_zero (E : EmbeddingData V N) (x : V.pt) (hN : 8 < N) :
    ∃ w ∈ normalSpace E x, w ≠ 0 :=
  Submodule.ne_bot_iff _ |>.1 (normalSpace_ne_bot E x hN)

/-- **The sphere bundle of the normal bundle is non-empty** as soon as the codimension is positive
and the manifold is non-empty: the normal space has positive dimension, so it contains a vector,
which can be scaled to norm `ε`.  This is what provides the basepoint of the Thom space. -/
theorem nonempty_normalSphSub (E : EmbeddingData V N) {ε : ℝ} (hε : 0 < ε) (hN : 8 < N)
    [Nonempty V.pt] : Nonempty (NormalSphSub E ε) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty V.pt)
  obtain ⟨w, hw, hw0⟩ := exists_mem_normalSpace_ne_zero E x hN
  refine ⟨⟨⟨(x, (ε / ‖w‖) • w), ?_⟩, ?_⟩⟩
  · rw [mem_normalSpace_iff]
    intro u hu
    rw [inner_smul_right, inner_eq_zero_of_mem_normalSpace hw hu, mul_zero]
  · simp only [mem_normalSphereSet, normalNorm_mk, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hε (norm_pos_iff.2 hw0))]
    field_simp

end

end Work.Tubular
