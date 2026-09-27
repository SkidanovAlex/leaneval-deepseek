import Mathlib

/-!
# Reflecting a smoothly embedded plane curve in the horizontal axis

If `γ : Circle → ℝ × ℝ` is a smooth embedding, then so is `x ↦ ((γ x).1, -(γ x).2)`: reflection
in the horizontal axis is a diffeomorphism of `ℝ × ℝ`, and post-composing with a diffeomorphism
preserves both halves of "smooth embedding".

The proof follows the pattern of `Work.Drive.isSmoothEmbedding_sub_const` (translating a curve):
the topological half is immediate (a homeomorphism is an embedding, and embeddings compose), while
for the immersion half we reuse the charts of `γ` and pre-compose the codomain chart with the
reflection, which is again a chart of the maximal atlas since the reflection is `C^∞` with `C^∞`
inverse (`mem_maximalAtlas_refl`).

The second statement is the same fact for a `C^∞` family of curves `γc` depending on a parameter.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Manifold

namespace Work.Drive.PolarTwist

noncomputable section

/-! ### The reflection as a linear isometry, a homeomorphism and a chart -/

private def reflMap (y : ℝ × ℝ) : ℝ × ℝ := (y.1, -y.2)

@[simp] private lemma reflMap_apply (y : ℝ × ℝ) : reflMap y = (y.1, -y.2) := rfl

@[simp] private lemma reflMap_reflMap (y : ℝ × ℝ) : reflMap (reflMap y) = y := by
  ext <;> simp [reflMap]

/-- Reflection in the horizontal axis as a continuous linear map. -/
private def reflCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-(ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] private lemma reflCLM_coe : ⇑reflCLM = reflMap := rfl

private lemma reflMap_continuous : Continuous reflMap := by
  rw [← reflCLM_coe]
  exact reflCLM.continuous

private def reflHomeo : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := reflMap
  invFun := reflMap
  left_inv := reflMap_reflMap
  right_inv := reflMap_reflMap
  continuous_toFun := reflMap_continuous
  continuous_invFun := reflMap_continuous

@[simp] private lemma reflHomeo_coe : ⇑reflHomeo = reflMap := rfl

/-- The reflection of the plane as an open partial homeomorphism of the whole plane. -/
private def reflTile : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun := reflMap
  invFun := reflMap
  source := Set.univ
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun _ _ => Set.mem_univ _
  left_inv' := fun x _ => reflMap_reflMap x
  right_inv' := fun x _ => reflMap_reflMap x
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := reflMap_continuous.continuousOn
  continuousOn_invFun := reflMap_continuous.continuousOn

@[simp] private lemma reflTile_coe : ⇑reflTile = reflMap := rfl
@[simp] private lemma reflTile_symm_coe : ⇑(reflTile.symm) = reflMap := rfl
@[simp] private lemma reflTile_source : reflTile.source = Set.univ := rfl
@[simp] private lemma reflTile_target : reflTile.target = Set.univ := rfl

/-! ### Pre-composing a chart of the maximal atlas with the reflection -/

private lemma mem_maximalAtlas_reflTile {ψ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hψ : ψ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) ∞ (ℝ × ℝ)) :
    (reflTile ≫ₕ ψ) ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) ∞ (ℝ × ℝ) := by
  have hψ' := hψ
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn] at hψ'
  obtain ⟨h1, h2⟩ := hψ'
  rw [contMDiffOn_iff_contDiffOn] at h1 h2
  have hTCD : ContDiffOn ℝ ∞ (⇑reflTile) Set.univ := by
    rw [reflTile_coe]
    exact reflCLM.contDiff.contDiffOn
  have hTsCD : ContDiffOn ℝ ∞ (⇑(reflTile.symm)) Set.univ := by
    rw [reflTile_symm_coe]
    exact reflCLM.contDiff.contDiffOn
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  constructor
  · rw [contMDiffOn_iff_contDiffOn]
    have hcomp : ContDiffOn ℝ ∞ (⇑ψ ∘ ⇑reflTile) (reflTile ⁻¹' ψ.source) :=
      h1.comp (hTCD.mono (Set.subset_univ _)) (fun _ hy => hy)
    rw [show (↑(reflTile ≫ₕ ψ) : ℝ × ℝ → ℝ × ℝ) = ⇑ψ ∘ ⇑reflTile from by
        rw [OpenPartialHomeomorph.coe_trans],
      show (reflTile ≫ₕ ψ).source = reflTile ⁻¹' ψ.source from by
        rw [OpenPartialHomeomorph.trans_source, reflTile_source, Set.univ_inter]]
    exact hcomp
  · rw [contMDiffOn_iff_contDiffOn]
    have hcomp2 : ContDiffOn ℝ ∞ (⇑(reflTile.symm) ∘ ⇑(ψ.symm)) ψ.target :=
      hTsCD.comp h2 (fun _ hy => Set.mem_univ _)
    rw [show (↑((reflTile ≫ₕ ψ).symm) : ℝ × ℝ → ℝ × ℝ) = ⇑(reflTile.symm) ∘ ⇑(ψ.symm) from by
        funext y; simp [reflTile, reflMap],
      show (reflTile ≫ₕ ψ).target = ψ.target from by
        rw [OpenPartialHomeomorph.trans_target, reflTile_target, Set.preimage_univ,
          Set.inter_univ]]
    exact hcomp2

/-! ### Reflection preserves smooth embeddings -/

private theorem isSmoothEmbedding_reflMap {δ : Circle → ℝ × ℝ}
    (hδ : Manifold.IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ δ) :
    Manifold.IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞
      (fun x : Circle => ((δ x).1, -(δ x).2)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨F, hFng, hFns, hf⟩ := hδ.isImmersion
    refine ⟨F, hFng, hFns, fun x => ?_⟩
    obtain hfx := hf x
    have hmem : (reflTile ≫ₕ hfx.codChart) ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) ∞ (ℝ × ℝ) :=
      mem_maximalAtlas_reflTile hfx.codChart_mem_maximalAtlas
    refine IsImmersionAtOfComplement.mk_of_charts
      (f := fun x : Circle => ((δ x).1, -(δ x).2)) (x := x)
      hfx.equiv hfx.domChart (reflTile ≫ₕ hfx.codChart) hfx.mem_domChart_source ?_
      hfx.domChart_mem_maximalAtlas hmem ?_ ?_
    · -- the reflected point lies in the reflected chart
      simp only [OpenPartialHomeomorph.trans_source, reflTile_source, Set.univ_inter,
        Set.mem_preimage, reflTile_coe, reflMap]
      simpa using hfx.mem_codChart_source
    · -- the domain chart maps into the reflected chart source
      intro y hy
      simp only [OpenPartialHomeomorph.trans_source, reflTile_source, Set.univ_inter,
        Set.mem_preimage, reflTile_coe, reflMap]
      simpa using hfx.source_subset_preimage_source hy
    · -- the coordinate expression of the reflected curve is that of the curve
      have hfun : ((↑((reflTile ≫ₕ hfx.codChart).extend (𝓘(ℝ, ℝ × ℝ))) : ℝ × ℝ → ℝ × ℝ) ∘
            (fun x : Circle => ((δ x).1, -(δ x).2)) ∘ (↑(hfx.domChart.extend (𝓡 1)).symm))
          = (↑(hfx.codChart.extend (𝓘(ℝ, ℝ × ℝ))) ∘ δ ∘
              ↑(hfx.domChart.extend (𝓡 1)).symm) := by
        funext u
        simp [Function.comp_def, reflTile, reflMap]
      rw [hfun]
      exact hfx.writtenInCharts
  · -- topological embedding: a homeomorphism composed with an embedding
    have hcomp : Topology.IsEmbedding (reflMap ∘ δ) :=
      (Homeomorph.isEmbedding reflHomeo).comp hδ.isEmbedding
    simpa [Function.comp_def, reflMap] using hcomp

/-! ### The target statement -/

theorem reflection_isSmoothEmbedding (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    (Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Circle => ((γ x).1, -(γ x).2))) ∧
    (∀ γc : ℝ → Circle → ℝ × ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => γc p.1 (Circle.exp p.2)) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (γc s)) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => (fun x : Circle => ((γc p.1 x).1, -(γc p.1 x).2)) (Circle.exp p.2)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Circle => ((γc s x).1, -(γc s x).2)))) := by
  refine ⟨isSmoothEmbedding_reflMap hγ, ?_⟩
  intro γc hγc hemb
  refine ⟨?_, fun s hs => isSmoothEmbedding_reflMap (hemb s hs)⟩
  have hcomp := (reflCLM.contDiff).comp hγc
  simpa [Function.comp_def, reflMap] using hcomp

end

end Work.Drive.PolarTwist
