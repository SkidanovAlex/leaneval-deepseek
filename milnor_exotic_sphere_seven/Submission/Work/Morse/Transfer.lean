import Mathlib
import Submission.Work.Morse.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Changing the model of a smooth manifold

Reeb's theorem is proved in this workspace (`Submission.Work.Morse.reeb`) for manifolds charted over
`EuclideanSpace ℝ (Fin n)`.  The lemma `Work.Morse.reeb_general` states it for an arbitrary
finite-dimensional normed space `E` and an arbitrary boundaryless model with corners
`I : ModelWithCorners ℝ E H`; the only difference is the *model space*.

This file provides the change of model.  Given a boundaryless model `I` on `(E, H)`, a finite
dimensional normed space `E'` and a continuous linear equivalence `L : E ≃L[ℝ] E'`, the
homeomorphism

`modelHomeo I L = I.toHomeomorph.trans L.toHomeomorph : H ≃ₜ E'`

(the model with corners `I` followed by `L`) pushes the atlas of `M` forward from `H` to `E'`:

* `pushChart Φ c` — the chart `c : M → H` followed by `Φ : H ≃ₜ E'`;
* `pushChartedSpace Φ` — the charted space structure on `M` modelled on `E'` whose chart at `x` is
  `pushChart Φ (chartAt H x)`;
* `conjMap Φ g` — conjugation of a local homeomorphism `g` of `H` by `Φ`.

The main results are

* `conj_mem` — `Φ` conjugates the groupoid `contDiffGroupoid ∞ I` into the groupoid of the *self*
  model `𝓘(ℝ, E')`;
* `push_isManifold` — `M`, with the pushed forward charted space, is a `C^∞` manifold modelled on
  `(𝓘(ℝ, E'))`;
* `mem_maximalAtlas_push` — the maximal atlas is pushed forward too.

These are the ingredients of the transfers of `ContMDiff`, of `mfderiv`, and of
`HasNondegHessian`, which are proved in the companion files
`Submission.Work.Morse.{contMDiff_push, mfderiv_push, hasNondegHessian_push}`.
-/

open scoped Manifold ContDiff Topology
open Set OpenPartialHomeomorph

set_option linter.unusedSectionVars false

namespace Work.Morse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The chart obtained from a chart `c : M → H` by postcomposition with a homeomorphism
`Φ : H ≃ₜ E'`. -/
def pushChart (Φ : H ≃ₜ E') (c : OpenPartialHomeomorph M H) : OpenPartialHomeomorph M E' :=
  c.trans Φ.toOpenPartialHomeomorph

@[simp] lemma pushChart_source (Φ : H ≃ₜ E') (c : OpenPartialHomeomorph M H) :
    (pushChart Φ c).source = c.source := by
  rw [pushChart, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ]

@[simp] lemma pushChart_apply (Φ : H ≃ₜ E') (c : OpenPartialHomeomorph M H) (x : M) :
    pushChart Φ c x = Φ (c x) := by
  rw [pushChart, OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply]

/-- The charted space structure on `M` modelled on `E'` obtained by pushing the atlas of `M`
forward along `Φ : H ≃ₜ E'`. -/
@[instance_reducible] noncomputable def pushChartedSpace (Φ : H ≃ₜ E') : ChartedSpace E' M where
  atlas := pushChart Φ '' atlas H M
  chartAt := fun x => pushChart Φ (chartAt H x)
  mem_chart_source := fun x => by
    rw [pushChart, OpenPartialHomeomorph.trans_source]
    exact ⟨mem_chart_source H x, by simp⟩
  chart_mem_atlas := fun x => ⟨chartAt H x, chart_mem_atlas H x, rfl⟩

@[simp] lemma pushChartedSpace_chartAt (Φ : H ≃ₜ E') (x : M) :
    (letI : ChartedSpace E' M := pushChartedSpace Φ;
      (chartAt E' x : OpenPartialHomeomorph M E')) = pushChart Φ (chartAt H x) := rfl

@[simp] lemma pushChartedSpace_atlas (Φ : H ≃ₜ E') :
    (letI : ChartedSpace E' M := pushChartedSpace Φ; atlas E' M) = pushChart Φ '' atlas H M := rfl

/-- The homeomorphism `H ≃ₜ E'` obtained by reading the boundaryless model with corners `I` in `E`
and then applying the continuous linear equivalence `L`. -/
noncomputable def modelHomeo (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (L : E ≃L[ℝ] E') : H ≃ₜ E' :=
  I.toHomeomorph.trans L.toHomeomorph

@[simp] lemma modelHomeo_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless] (L : E ≃L[ℝ] E')
    (a : H) : modelHomeo I L a = L (I a) := by
  rw [modelHomeo, Homeomorph.trans_apply, ModelWithCorners.toHomeomorph_apply,
    ContinuousLinearEquiv.coe_toHomeomorph]

@[simp] lemma modelHomeo_symm_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (L : E ≃L[ℝ] E') (b : E') : (modelHomeo I L).symm b = I.symm (L.symm b) := by
  rw [modelHomeo, Homeomorph.symm_trans_apply, ModelWithCorners.toHomeomorph_symm_apply,
    ← ContinuousLinearEquiv.toHomeomorph_symm, ContinuousLinearEquiv.coe_toHomeomorph]

@[simp] lemma modelHomeo_coe (I : ModelWithCorners ℝ E H) [I.Boundaryless] (L : E ≃L[ℝ] E') :
    ⇑(modelHomeo I L) = fun a => L (I a) := by
  funext a; simp

/-- Conjugation of a local homeomorphism of the model space `H` by a homeomorphism `Φ : H ≃ₜ E'`. -/
def conjMap (Φ : H ≃ₜ E') (g : OpenPartialHomeomorph H H) : OpenPartialHomeomorph E' E' :=
  Φ.symm.toOpenPartialHomeomorph.trans (g.trans Φ.toOpenPartialHomeomorph)

@[simp] lemma conjMap_source (Φ : H ≃ₜ E') (g : OpenPartialHomeomorph H H) :
    (conjMap Φ g).source = Φ.symm ⁻¹' g.source := by
  ext z; simp [conjMap]

@[simp] lemma conjMap_target (Φ : H ≃ₜ E') (g : OpenPartialHomeomorph H H) :
    (conjMap Φ g).target = Φ.symm ⁻¹' g.target := by
  ext z; simp [conjMap]

@[simp] lemma conjMap_apply (Φ : H ≃ₜ E') (g : OpenPartialHomeomorph H H) (z : E') :
    conjMap Φ g z = Φ (g (Φ.symm z)) := by
  rw [conjMap, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply]
  rfl

@[simp] lemma conjMap_symm (Φ : H ≃ₜ E') (g : OpenPartialHomeomorph H H) :
    (conjMap Φ g).symm = conjMap Φ g.symm := by
  ext z <;> simp [conjMap]

/-- Membership in the groupoid of the self model on `E'` is smoothness of the map and of its
inverse on their sources/targets. -/
lemma mem_contDiffGroupoid_self_iff {e : OpenPartialHomeomorph E' E'} :
    e ∈ contDiffGroupoid ∞ (𝓘(ℝ, E')) ↔
      ContDiffOn ℝ ∞ ⇑e e.source ∧ ContDiffOn ℝ ∞ ⇑e.symm e.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, preimage_id, range_id,
    inter_univ, Function.comp_id, Function.id_comp]

/-- A boundaryless model `I` conjugates the groupoid `contDiffGroupoid ∞ I` of the model space `H`
into the groupoid of the self model on `E'`, along `modelHomeo I L`. -/
theorem conj_mem (L : E ≃L[ℝ] E') {g : OpenPartialHomeomorph H H}
    (hg : g ∈ contDiffGroupoid ∞ I) :
    conjMap (modelHomeo I L) g ∈ contDiffGroupoid ∞ (𝓘(ℝ, E')) := by
  rw [mem_contDiffGroupoid_self_iff]
  have hg' : ContDiffOn ℝ ∞ (↑I ∘ ↑g ∘ ↑I.symm) (↑I.symm ⁻¹' g.source) ∧
      ContDiffOn ℝ ∞ (↑I ∘ ↑g.symm ∘ ↑I.symm) (↑I.symm ⁻¹' g.target) := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at hg
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · have h1' : ContDiffOn ℝ ∞ (↑I ∘ ↑g ∘ ↑I.symm) (↑I.symm ⁻¹' g.source ∩ range ↑I) := h1
      rwa [ModelWithCorners.range_eq_univ I, inter_univ] at h1'
    · have h2' : ContDiffOn ℝ ∞ (↑I ∘ ↑g.symm ∘ ↑I.symm) (↑I.symm ⁻¹' g.target ∩ range ↑I) := h2
      rwa [ModelWithCorners.range_eq_univ I, inter_univ] at h2'
  obtain ⟨hg1, hg2⟩ := hg'
  constructor
  · have hfun : ⇑(conjMap (modelHomeo I L) g) = ↑L ∘ (↑I ∘ ↑g ∘ ↑I.symm) ∘ ↑L.symm := by
      funext z; simp [conjMap]
    have hsrc : (conjMap (modelHomeo I L) g).source = ↑L.symm ⁻¹' (↑I.symm ⁻¹' g.source) := by
      rw [conjMap_source]; ext z; simp
    rw [hfun, hsrc]
    exact ContDiff.comp_contDiffOn L.contDiff
      (hg1.comp (L.symm.contDiff.contDiffOn) (fun z hz => hz))
  · have hfun : ⇑(conjMap (modelHomeo I L) g).symm
        = ↑L ∘ (↑I ∘ ↑g.symm ∘ ↑I.symm) ∘ ↑L.symm := by
      rw [conjMap_symm]; funext z; simp [conjMap]
    have htgt : (conjMap (modelHomeo I L) g).target = ↑L.symm ⁻¹' (↑I.symm ⁻¹' g.target) := by
      rw [conjMap_target]; ext z; simp
    rw [hfun, htgt]
    exact ContDiff.comp_contDiffOn L.contDiff
      (hg2.comp (L.symm.contDiff.contDiffOn) (fun z hz => hz))

/-- The transition map of two pushed forward charts is the conjugation of the transition map of
the original charts. -/
lemma conjMap_pushChart (Φ : H ≃ₜ E') (c c' : OpenPartialHomeomorph M H) :
    (pushChart Φ c).symm ≫ₕ (pushChart Φ c') = conjMap Φ (c.symm ≫ₕ c') := by
  ext z <;> simp [pushChart, conjMap, OpenPartialHomeomorph.trans_assoc]

/-- `M` with the charted space structure pushed forward along `modelHomeo I L` is a `C^∞` manifold
modelled on the self model of `E'`. -/
theorem push_isManifold (L : E ≃L[ℝ] E') [IsManifold I ∞ M] :
    (letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L);
      IsManifold (𝓘(ℝ,E')) ∞ M) := by
  letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L)
  refine IsManifold.mk' (𝓘(ℝ,E')) ∞ M (gr := ⟨fun {e e'} he he' => ?_⟩)
  rcases he with ⟨c, hc, rfl⟩
  rcases he' with ⟨c', hc', rfl⟩
  rw [conjMap_pushChart]
  exact conj_mem L (StructureGroupoid.compatible_of_mem_maximalAtlas
    (StructureGroupoid.subset_maximalAtlas (contDiffGroupoid ∞ I) hc)
    (StructureGroupoid.subset_maximalAtlas (contDiffGroupoid ∞ I) hc'))

/-- The maximal atlas is pushed forward along `modelHomeo I L`. -/
theorem mem_maximalAtlas_push (L : E ≃L[ℝ] E') [IsManifold I ∞ M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    (letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L);
      pushChart (modelHomeo I L) e ∈ IsManifold.maximalAtlas (𝓘(ℝ,E')) ∞ M) := by
  letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L)
  rw [IsManifold.mem_maximalAtlas_iff] at he ⊢
  rw [mem_maximalAtlas_iff]
  intro e' he'
  rcases he' with ⟨c, hc, rfl⟩
  constructor
  · rw [conjMap_pushChart]
    exact conj_mem L (StructureGroupoid.compatible_of_mem_maximalAtlas he
      (StructureGroupoid.subset_maximalAtlas (contDiffGroupoid ∞ I) hc))
  · rw [conjMap_pushChart]
    exact conj_mem L (StructureGroupoid.compatible_of_mem_maximalAtlas
      (StructureGroupoid.subset_maximalAtlas (contDiffGroupoid ∞ I) hc) he)

/-- The extended chart at a point of `M`, in the pushed forward structure, is the extended chart
of the original structure followed by `L`. -/
lemma extChartAt_push_coe (L : E ≃L[ℝ] E') (x : M) :
    (letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L);
      ⇑(extChartAt (𝓘(ℝ,E')) x)) = fun y => L (extChartAt I x y) := by
  letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L)
  funext y
  rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, pushChartedSpace_chartAt,
    pushChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, modelHomeo_apply]
  rw [extChartAt_coe, Function.comp_apply]

/-- The inverse of the extended chart at a point of `M`, in the pushed forward structure, is the
inverse of the extended chart of the original structure, composed with `L.symm`. -/
lemma extChartAt_push_symm_coe (L : E ≃L[ℝ] E') (x : M) :
    (letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L);
      ⇑(extChartAt (𝓘(ℝ,E')) x).symm) = fun z => (extChartAt I x).symm (L.symm z) := by
  letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L)
  funext z
  rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_apply,
    pushChartedSpace_chartAt, pushChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    ← Homeomorph.symm_toOpenPartialHomeomorph, OpenPartialHomeomorph.coe_trans,
    Function.comp_apply, Homeomorph.toOpenPartialHomeomorph_apply, modelHomeo_symm_apply,
    extChartAt_coe_symm, Function.comp_apply]
  simp

/-- The chart expression of a function `f : M → ℝ` in the pushed forward structure is the chart
expression in the original structure, composed with `L.symm`. -/
lemma writtenInExtChartAt_push (L : E ≃L[ℝ] E') (x : M) (f : M → ℝ) :
    (letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L);
      writtenInExtChartAt (𝓘(ℝ,E')) 𝓘(ℝ,ℝ) x f)
      = fun z => writtenInExtChartAt I 𝓘(ℝ,ℝ) x f (L.symm z) := by
  letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L)
  funext z
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [extChartAt_push_symm_coe]

end Work.Morse
