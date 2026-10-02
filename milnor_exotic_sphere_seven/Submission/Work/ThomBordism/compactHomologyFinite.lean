import Mathlib
import Submission.Work.ThomBordism.existsFiniteGoodCover_of_c2Atlas
import Submission.Work.ThomBordism.finiteGoodCoverHomology
import Submission.Work.Cohomology.exists_capH
import Submission.Work.EmbeddedSpheres.TubeProject.StraightenAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Finitely generated singular homology of a compact smooth manifold

`Work.ThomBordism.compactHomologyFinite` : the singular homology with `ℤ` coefficients of a compact
`C^∞` manifold is a finitely generated `ℤ`-module in every degree.

The proof assembles three ingredients:

* a **finite atlas**: compactness turns the chart cover `⋃ x, (chartAt E x).source = univ` into a
  finite one; each chart is post-composed with a translation of the model space so that it is
  centred at the point it covers;
* `Work.ThomBordism.existsFiniteGoodCover_of_c2Atlas`: a finite atlas whose transition maps are `C²`
  with injective derivatives yields a finite *good* cover (all nonempty finite intersections
  contractible);
* `Work.ThomBordism.finiteGoodCoverHomology`: a finite good cover yields finitely generated singular
  homology.

The two analytic inputs (the transitions are `C²`, their derivatives injective) are consequences of
the fact that all charts used lie in the maximal atlas of the smooth structure
(`IsManifold.compatible_of_mem_maximalAtlas`), together with the chart-theoretic helpers of
`Submission/Work/EmbeddedSpheres/TubeProject/StraightenAux.lean`.
-/

open scoped ContDiff Manifold

namespace Work.ThomBordism

section Transitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

/-- The image of the common domain of two charts is contained in the source of the transition map
between them. -/
theorem image_inter_subset_trans_source (ψ χ : OpenPartialHomeomorph X E) :
    ψ '' (ψ.source ∩ χ.source) ⊆ (ψ.symm ≫ₕ χ).source := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := hu
  rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
  refine ⟨ψ.map_source hx.1, ?_⟩
  rw [ψ.left_inv hx.1]
  exact hx.2

/-- The transition map between two charts of the maximal atlas is `C^n`. -/
theorem contDiffOn_transition_of_mem_maximalAtlas {n : ℕ∞ω}
    {ψ χ : OpenPartialHomeomorph X E}
    (hψ : ψ ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) n X)
    (hχ : χ ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) n X) :
    ContDiffOn ℝ n (fun u => χ (ψ.symm u)) (ψ '' (ψ.source ∩ χ.source)) := by
  have hθ : ψ.symm ≫ₕ χ ∈ contDiffGroupoid n (𝓘(ℝ, E)) :=
    IsManifold.compatible_of_mem_maximalAtlas hψ hχ
  have h1 : ContDiffOn ℝ n (↑(ψ.symm ≫ₕ χ) : E → E) (ψ.symm ≫ₕ χ).source :=
    contMDiffOn_iff_contDiffOn.mp (contMDiffOn_of_mem_contDiffGroupoid hθ)
  refine (h1.mono (image_inter_subset_trans_source ψ χ)).congr (fun u _ => ?_)
  rw [OpenPartialHomeomorph.trans_apply]

/-- The derivative of the transition map between two charts of the maximal atlas is injective. -/
theorem injective_fderiv_transition_of_mem_maximalAtlas {n : ℕ∞ω} (hn : n ≠ 0)
    {ψ χ : OpenPartialHomeomorph X E}
    (hψ : ψ ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) n X)
    (hχ : χ ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) n X)
    {u : E} (hu : u ∈ ψ '' (ψ.source ∩ χ.source)) :
    Function.Injective (fderiv ℝ (fun v => χ (ψ.symm v)) u) := by
  have hθ : ψ.symm ≫ₕ χ ∈ contDiffGroupoid n (𝓘(ℝ, E)) :=
    IsManifold.compatible_of_mem_maximalAtlas hψ hχ
  have hθ' : ψ.symm ≫ₕ χ ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) n E :=
    (Work.EmbeddedSpheres.TubeProject.mem_maximalAtlas_modelWithCornersSelf n _).mpr hθ
  have hus : u ∈ (ψ.symm ≫ₕ χ).source := image_inter_subset_trans_source ψ χ hu
  have h := Work.EmbeddedSpheres.TubeProject.injective_fderiv_of_mem_maximalAtlas_self n hn
    (ψ.symm ≫ₕ χ) hθ' hus
  have hfun : (↑(ψ.symm ≫ₕ χ) : E → E) = fun v => χ (ψ.symm v) := by
    funext v
    rw [OpenPartialHomeomorph.trans_apply]
  rwa [hfun] at h

end Transitions

/-- **A compact `C^∞` manifold has finitely generated singular homology in every degree.** -/
theorem compactHomologyFinite {n k : ℕ} (X : Type) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ENat) : WithTop ENat) X]
    [CompactSpace X] [T2Space X] :
    Module.Finite ℤ ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homology k) := by
  classical
  haveI hman : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (∞ : ℕ∞ω) X :=
    inferInstance
  -- ## 1. A finite cover by chart sources
  have hcover :
      (⋃ x : X, (chartAt (EuclideanSpace ℝ (Fin n)) x).source) = Set.univ :=
    iUnion_source_chartAt _ _
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source)
    (by rw [hcover])
  -- ## 2. The finite atlas, with each chart translated to be centred at its base point
  let y : Fin s.card → X := fun k => (s.equivFin.symm k : {x // x ∈ s}).1
  let c : Fin s.card → EuclideanSpace ℝ (Fin n) :=
    fun k => chartAt (EuclideanSpace ℝ (Fin n)) (y k) (y k)
  let ψ : Fin s.card → OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)) :=
    fun k => (chartAt (EuclideanSpace ℝ (Fin n)) (y k)).trans
      (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c k))
  have hy_def : ∀ k : Fin s.card, y k = (s.equivFin.symm k : {x // x ∈ s}).1 := fun k => rfl
  have hc_def : ∀ k : Fin s.card, c k = chartAt (EuclideanSpace ℝ (Fin n)) (y k) (y k) :=
    fun k => rfl
  have hψ_def : ∀ k : Fin s.card,
      ψ k = (chartAt (EuclideanSpace ℝ (Fin n)) (y k)).trans
        (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c k)) := fun k => rfl
  -- ## 3. Every chart lies in the maximal atlas of the smooth structure
  have hψmem : ∀ k : Fin s.card, ψ k ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (∞ : ℕ∞ω) X := by
    intro k
    exact Work.EmbeddedSpheres.TubeProject.trans_mem_maximalAtlas_of_mem_groupoid
      (e := chartAt (EuclideanSpace ℝ (Fin n)) (y k))
      (f := Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c k))
      (IsManifold.chart_mem_maximalAtlas (I :=
        modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (n := (∞ : ℕ∞ω)) (y k))
      (Work.EmbeddedSpheres.TubeProject.subRight_mem_contDiffGroupoid (∞ : ℕ∞ω) (c k))
  -- ## 4. The charts cover `X`, and each is centred at `y k`
  have hψcov : (⋃ k : Fin s.card, (ψ k).source) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ (⋃ i ∈ s, (chartAt (EuclideanSpace ℝ (Fin n)) i).source) :=
      hs (Set.mem_univ x)
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    refine Set.mem_iUnion.mpr ⟨s.equivFin ⟨i, hi⟩, ?_⟩
    have hyi : y (s.equivFin ⟨i, hi⟩) = i := by
      simp only [hy_def, Equiv.symm_apply_apply]
    simp only [hψ_def, hyi, OpenPartialHomeomorph.trans_source,
      Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph_source, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_univ, and_true]
    exact hxi
  have hy0 : ∀ k : Fin s.card, y k ∈ (ψ k).source ∧ ψ k (y k) = 0 := by
    intro k
    refine ⟨?_, ?_⟩
    · simp only [hψ_def, OpenPartialHomeomorph.trans_source,
        Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph_source, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_univ, and_true]
      exact mem_chart_source _ _
    · simp only [hψ_def, OpenPartialHomeomorph.trans_apply,
        Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph_apply]
      simp only [hc_def]
      abel
  -- ## 5. The analytic inputs for `existsFiniteGoodCover_of_c2Atlas`
  have hC2 : ∀ i j : Fin s.card,
      ContDiffOn ℝ 2
        (fun u : EuclideanSpace ℝ (Fin n) => ψ j ((ψ i).symm u))
        (ψ i '' ((ψ i).source ∩ (ψ j).source)) := by
    intro i j
    exact (contDiffOn_transition_of_mem_maximalAtlas (n := (∞ : ℕ∞ω))
      (hψmem i) (hψmem j)).of_le ENat.LEInfty.out
  have hinj : ∀ i j : Fin s.card, ∀ u ∈ ψ i '' ((ψ i).source ∩ (ψ j).source),
      Function.Injective
        (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => ψ j ((ψ i).symm v)) u) := by
    intro i j u hu
    exact injective_fderiv_transition_of_mem_maximalAtlas (n := (∞ : ℕ∞ω)) (by decide)
      (hψmem i) (hψmem j) hu
  -- ## 6. Assemble
  obtain ⟨m, U, hUopen, hUcov, hUgood⟩ :=
    existsFiniteGoodCover_of_c2Atlas X ψ hψcov y hy0 hC2 hinj
  exact finiteGoodCoverHomology m U hUopen hUcov hUgood k

end Work.ThomBordism
