import Mathlib

/-!
# Translating a smooth embedded plane curve is again a smooth embedding

For a smooth embedding `γ : Circle → ℝ × ℝ` and a constant `c : ℝ × ℝ`, the curve
`x ↦ γ x - c` is again a smooth embedding.  This is the statement needed to arrange that the
curve avoids the origin (as in `Work.Drive.parityCore_translate`): translation of the target is
a diffeomorphism of `ℝ × ℝ`, so it preserves the two defining properties of a smooth embedding —
being a topological embedding and being an immersion — and the two parts are handled separately.

* The topological part is immediate: `y ↦ y - c` is a homeomorphism of `ℝ × ℝ`, hence an
  embedding, and a composite of embeddings is an embedding (`Topology.IsEmbedding.comp`).

* For the immersion part, we use the chart-based definition `IsImmersionAtOfComplement`.  Given
  the charts `φ`, `ψ` (and linear equivalence `equiv`) witnessing that `γ` is an immersion at `x`,
  the pair `φ` and `ψ' := ψ ∘ (· + c)` witnesses that `γ - c` is an immersion at `x`: indeed
  `ψ' (γ x - c) = ψ (γ x)`, so the coordinate expression of `γ - c` in these charts is literally
  the coordinate expression of `γ`.  It remains to see that `ψ'` is again a chart of the maximal
  atlas, i.e. that `y ↦ ψ (y + c)` is `C^∞` with `C^∞` inverse along with `ψ`; this is
  `mem_maximalAtlas_trans_addRight`, proved below from the characterisation
  `IsManifold.mem_maximalAtlas_iff_contMDiffOn` of the maximal atlas of `ℝ × ℝ`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold

/-- Translating the argument of a chart of the maximal atlas of `ℝ × ℝ` (modelled on itself by
`modelWithCornersSelf`) produces another chart of the maximal atlas.

Concretely, `(Homeomorph.addRight c).toOpenPartialHomeomorph ≫ₕ ψ` is the partial homeomorphism
`y ↦ ψ (y + c)`, whose source is the translate of `ψ.source`.  The proof uses that, for the model
space endowed with its own model with corners, the maximal atlas is exactly the set of partial
homeomorphisms that are `C^∞` with `C^∞` inverse, so that membership reduces (via
`contMDiffOn_iff_contDiffOn`) to `ContDiffOn` statements, which are stable under composing with
the translation `y ↦ y + c` and its inverse. -/
lemma mem_maximalAtlas_trans_addRight (c : ℝ × ℝ) {ψ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hψ : ψ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) ∞ (ℝ × ℝ)) :
    (Homeomorph.toOpenPartialHomeomorph (Homeomorph.addRight c)) ≫ₕ ψ ∈
      IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) ∞ (ℝ × ℝ) := by
  let T : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    Homeomorph.toOpenPartialHomeomorph (Homeomorph.addRight c)
  change T ≫ₕ ψ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) ∞ (ℝ × ℝ)
  have hTfun : ⇑T = fun y : ℝ × ℝ => y + c := by
    funext y; simp [T, Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_addRight]
  have hTsfun : ⇑(T.symm) = fun y : ℝ × ℝ => y - c := by
    funext y
    simp [T, Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.addRight_symm,
      Homeomorph.coe_addRight, sub_eq_add_neg]
  have hTsrc : T.source = Set.univ := Homeomorph.toOpenPartialHomeomorph_source _
  have hTtgt : T.target = Set.univ := Homeomorph.toOpenPartialHomeomorph_target _
  have hψ' := hψ
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn] at hψ'
  obtain ⟨h1, h2⟩ := hψ'
  rw [contMDiffOn_iff_contDiffOn] at h1 h2
  have hTCD : ContDiffOn ℝ ∞ (⇑T) Set.univ := by
    rw [hTfun]; exact (contDiff_id.add contDiff_const).contDiffOn
  have hTsCD : ContDiffOn ℝ ∞ (⇑(T.symm)) Set.univ := by
    rw [hTsfun]; exact (contDiff_id.sub contDiff_const).contDiffOn
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  constructor
  · rw [contMDiffOn_iff_contDiffOn]
    have hcomp : ContDiffOn ℝ ∞ (⇑ψ ∘ ⇑T) (T ⁻¹' ψ.source) :=
      h1.comp (hTCD.mono (Set.subset_univ _)) (fun y hy => hy)
    rw [show (↑(T ≫ₕ ψ) : ℝ × ℝ → ℝ × ℝ) = ⇑ψ ∘ ⇑T from by funext y; simp,
      show (T ≫ₕ ψ).source = T ⁻¹' ψ.source from by
        rw [OpenPartialHomeomorph.trans_source, hTsrc, Set.univ_inter]]
    exact hcomp
  · rw [contMDiffOn_iff_contDiffOn]
    have hcomp2 : ContDiffOn ℝ ∞ (⇑(T.symm) ∘ ⇑(ψ.symm)) ψ.target :=
      hTsCD.comp h2 (fun y hy => Set.mem_univ _)
    rw [show (↑((T ≫ₕ ψ).symm) : ℝ × ℝ → ℝ × ℝ) = ⇑(T.symm) ∘ ⇑(ψ.symm) from by funext y; simp,
      show (T ≫ₕ ψ).target = ψ.target from by
        rw [OpenPartialHomeomorph.trans_target, hTtgt, Set.preimage_univ, Set.inter_univ]]
    exact hcomp2

theorem isSmoothEmbedding_sub_const (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (c : ℝ × ℝ) :
    Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => γ x - c) := by
  refine ⟨?_, ?_⟩
  · -- immersion: reuse the charts of `γ`, translating the codomain chart along the target
    obtain ⟨F, hFng, hFns, hf⟩ := hγ.isImmersion
    refine ⟨F, hFng, hFns, fun x => ?_⟩
    obtain hfx := hf x
    let T : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
      Homeomorph.toOpenPartialHomeomorph (Homeomorph.addRight c)
    have hTfun : ⇑T = fun y : ℝ × ℝ => y + c := by
      funext y; simp [T, Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_addRight]
    have hTsrc : T.source = Set.univ := Homeomorph.toOpenPartialHomeomorph_source _
    have hmem : (T ≫ₕ hfx.codChart) ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) ∞ (ℝ × ℝ) :=
      mem_maximalAtlas_trans_addRight c hfx.codChart_mem_maximalAtlas
    refine IsImmersionAtOfComplement.mk_of_charts (f := fun x => γ x - c) (x := x)
      hfx.equiv hfx.domChart (T ≫ₕ hfx.codChart) hfx.mem_domChart_source ?_
      hfx.domChart_mem_maximalAtlas hmem ?_ ?_
    · -- `γ x - c` lies in the translated chart source
      rw [OpenPartialHomeomorph.trans_source, hTsrc, Set.univ_inter, Set.mem_preimage, hTfun]
      simpa using hfx.mem_codChart_source
    · -- the domain chart maps into the translated chart source
      intro y hy
      rw [OpenPartialHomeomorph.trans_source, hTsrc, Set.univ_inter, Set.mem_preimage, hTfun]
      simpa using hfx.source_subset_preimage_source hy
    · -- the coordinate expression of `γ - c` is that of `γ`
      have hfun : ((↑((T ≫ₕ hfx.codChart).extend (𝓘(ℝ, ℝ × ℝ))) : ℝ × ℝ → ℝ × ℝ) ∘
            (fun x => γ x - c) ∘ (↑(hfx.domChart.extend (𝓡 1)).symm))
          = (↑(hfx.codChart.extend (𝓘(ℝ, ℝ × ℝ))) ∘ γ ∘ ↑(hfx.domChart.extend (𝓡 1)).symm) := by
        funext u
        simp [T, Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_addRight, sub_add_cancel]
      rw [hfun]
      exact hfx.writtenInCharts
  · -- topological embedding: compose the embedding `γ` with the translation homeomorphism
    have hsub : Topology.IsEmbedding (fun y : ℝ × ℝ => y - c) := by
      simpa [Homeomorph.coe_subRight] using Homeomorph.isEmbedding (Homeomorph.subRight c)
    have hcomp := hsub.comp hγ.isEmbedding
    simpa [Function.comp_def] using hcomp

end Work.Drive
