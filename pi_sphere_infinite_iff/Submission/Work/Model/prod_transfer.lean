import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# Transferring a charted-space structure from `ℝ^m × ℝ^n` to `ℝ^{m+n}`

A manifold `M` charted over the product model `ModelProd (EuclideanSpace ℝ (Fin m))
(EuclideanSpace ℝ (Fin n))` can be re-charted over `EuclideanSpace ℝ (Fin (m + n))`, because the
two model spaces are linearly isometric (hence diffeomorphic).  Pushing forward the atlas along
such an isometry preserves the smooth structure, since conjugating a `C^∞` transition map by a
diffeomorphism produces again a `C^∞` map.

This is the "model transfer" used when identifying `ℝ^m × ℝ^n` with `ℝ^{m+n}` on a smooth
manifold.
-/

namespace Work.Model

open scoped Manifold ContDiff Topology
open Set

/-- Membership in the `C^n` groupoid attached to the identity model with corners `𝓘(ℝ, E)` is
exactly smoothness of the map and of its inverse on their respective sources/targets. -/
theorem mem_contDiffGroupoid_self_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e : OpenPartialHomeomorph E E} :
    e ∈ contDiffGroupoid ∞ (𝓘(ℝ, E)) ↔
      ContDiffOn ℝ ∞ ⇑e e.source ∧ ContDiffOn ℝ ∞ ⇑e.symm e.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, preimage_id, range_id,
    inter_univ, Function.comp_id, Function.id_comp]

/-- The underlying function of the open partial homeomorphism attached to the inverse of a
homeomorphism is the inverse homeomorphism. -/
theorem homeomorph_coe_toOpenPartialHomeomorph_symm {P G : Type*} [TopologicalSpace P]
    [TopologicalSpace G] (f : P ≃ₜ G) :
    ⇑(f.toOpenPartialHomeomorph.symm) = ⇑f.symm := by
  rw [← Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.toOpenPartialHomeomorph_apply]

/-- Conjugating a `C^n` open partial homeomorphism by a homeomorphism which is smooth together with
its inverse (for instance the homeomorphism induced by a continuous linear equivalence) yields
again a `C^n` open partial homeomorphism. -/
theorem conj_mem {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : P ≃ₜ G)
    (hf : ContDiff ℝ ∞ ⇑f) (hf' : ContDiff ℝ ∞ ⇑f.symm)
    {e : OpenPartialHomeomorph P P} (he : e ∈ contDiffGroupoid ∞ (𝓘(ℝ, P))) :
    f.toOpenPartialHomeomorph.symm.trans (e.trans f.toOpenPartialHomeomorph) ∈
      contDiffGroupoid ∞ (𝓘(ℝ, G)) := by
  rw [mem_contDiffGroupoid_self_iff] at he ⊢
  obtain ⟨he1, he2⟩ := he
  -- the conjugated map, restricted to the preimage of the source of `e`, is the composition of
  -- `e` with the two smooth maps `f` and `f.symm`
  have key : ∀ (g : P → P) (s : Set P), ContDiffOn ℝ ∞ g s →
      ContDiffOn ℝ ∞ (⇑f ∘ g ∘ ⇑f.symm) (⇑f.symm ⁻¹' s) := by
    intro g s hg
    have h1 : ContDiffOn ℝ ∞ (g ∘ ⇑f.symm) (⇑f.symm ⁻¹' s) :=
      ContDiffOn.comp hg hf'.contDiffOn (fun x hx => hx)
    have h2 := ContDiff.comp_contDiffOn hf h1
    simpa [Function.comp_assoc] using h2
  have hs : (f.toOpenPartialHomeomorph.symm.trans (e.trans f.toOpenPartialHomeomorph)).source
      = ⇑f.symm ⁻¹' e.source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]
    simp only [homeomorph_coe_toOpenPartialHomeomorph_symm,
      Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_target,
      OpenPartialHomeomorph.symm_source, preimage_univ, inter_univ, univ_inter]
  have ht : (f.toOpenPartialHomeomorph.symm.trans (e.trans f.toOpenPartialHomeomorph)).target
      = ⇑f.symm ⁻¹' e.target := by
    rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_target]
    simp only [homeomorph_coe_toOpenPartialHomeomorph_symm,
      Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_target,
      OpenPartialHomeomorph.symm_target, preimage_univ, inter_univ, univ_inter]
  have hc : ⇑(f.toOpenPartialHomeomorph.symm.trans (e.trans f.toOpenPartialHomeomorph))
      = ⇑f ∘ ⇑e ∘ ⇑f.symm := by
    rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans,
      Homeomorph.toOpenPartialHomeomorph_apply, homeomorph_coe_toOpenPartialHomeomorph_symm,
      Function.comp_assoc]
  have hsy : (f.toOpenPartialHomeomorph.symm.trans (e.trans f.toOpenPartialHomeomorph)).symm
      = f.toOpenPartialHomeomorph.symm.trans (e.symm.trans f.toOpenPartialHomeomorph) := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.trans_assoc]
  simp only [hs, ht, hc, hsy]
  exact ⟨key e e.source he1, key e.symm e.target he2⟩

open scoped Manifold ContDiff Topology in
theorem prod_transfer {m n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) M]
    [IsManifold ((𝓡 m).prod (𝓡 n)) ∞ M] :
    ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin (m + n))) M,
      (letI := c; IsManifold (𝓡 (m + n)) ∞ M) := by
  -- the linear isometry (hence diffeomorphism) identifying `ℝ^m × ℝ^n` with `ℝ^{m+n}`
  let Φ : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)).symm
  let f : (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) ≃ₜ
      EuclideanSpace ℝ (Fin (m + n)) := Φ.toHomeomorph
  -- push the atlas forward along `f`
  let c : ChartedSpace (EuclideanSpace ℝ (Fin (m + n))) M :=
    { atlas := (fun φ : OpenPartialHomeomorph M
          (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) =>
          φ.trans f.toOpenPartialHomeomorph) ''
        atlas (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) M
      chartAt := fun x =>
        (chartAt (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) x).trans
          f.toOpenPartialHomeomorph
      mem_chart_source := by
        intro x
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨mem_chart_source _ x, by simp⟩
      chart_mem_atlas := fun x => ⟨chartAt _ x, chart_mem_atlas _ x, rfl⟩ }
  refine ⟨c, IsManifold.mk' (𝓡 (m + n)) ∞ M (gr := ⟨fun {e e'} he he' => ?_⟩)⟩
  rcases he with ⟨φ, hφ, rfl⟩
  rcases he' with ⟨ψ, hψ, rfl⟩
  -- a transition of the new atlas is the conjugate of a transition of the old one
  have hbase : (φ.symm ≫ₕ ψ) ∈ contDiffGroupoid ∞
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) := by
    have h := (contDiffGroupoid ∞ ((𝓡 m).prod (𝓡 n))).compatible hφ hψ
    rwa [← modelWithCornersSelf_prod] at h
  have hconj := conj_mem f Φ.contDiff Φ.symm.contDiff hbase
  have hsymm : (φ.trans f.toOpenPartialHomeomorph).symm ≫ₕ (ψ.trans f.toOpenPartialHomeomorph)
      = f.toOpenPartialHomeomorph.symm.trans
          ((φ.symm ≫ₕ ψ).trans f.toOpenPartialHomeomorph) := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    simp only [OpenPartialHomeomorph.trans_assoc]
  rw [hsymm]
  exact hconj

end Work.Model
