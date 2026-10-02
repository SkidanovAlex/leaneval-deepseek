import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.Grassmann.Torsion.goodCoverSubordinate
import Submission.Work.TangentClasses.Bundle
import Submission.Work.ThomBordism.compactHomologyFinite

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped ContDiff Manifold
open Set Metric

namespace Work.ThomBordism

/-!
# A finite good cover subordinate to the chart cover of a real bundle

`Work.ThomBordism.goodCoverRealBundle` produces, for a real bundle `Z` over a closed smooth
`8`-manifold `V`, a finite open cover of the base all of whose nonempty finite intersections are
contractible and each of whose members lies inside a coordinate chart of `Z`.

The proof is the standard "shrink a finite atlas so that it refines the given cover" argument,
combined with `Work.ThomBordism.Grassmann.Torsion.goodCoverSubordinate` (a finite `C²` atlas
yields a finite good cover subordinate to any family containing the chart sources).

* `finiteGoodCover_subordinate_of_charted` is the geometric statement in the general form
  (a compact smooth manifold modelled on `EuclideanSpace ℝ (Fin n)`);
* the two private lemmas `contDiffOn_transition_restrOpen` and
  `injective_fderiv_transition_restrOpen` transfer the two analytic inputs (`C²` transitions and
  injective derivatives) from an atlas to the atlas restricted to an open family — this is an
  immediate consequence of `OpenPartialHomeomorph.coe_restrOpen`.
-/

section RestrOpenTransfer

/-- Restricting the charts of a family to an open family preserves the `C²`-ness of the
transitions. -/
private lemma contDiffOn_transition_restrOpen
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {m : ℕ} (Φ : Fin m → OpenPartialHomeomorph X E) (t : Fin m → Set X) (ht : ∀ i, IsOpen (t i))
    (hC2 : ∀ i j, ContDiffOn ℝ 2 (fun u => Φ j ((Φ i).symm u))
      ((Φ i) '' ((Φ i).source ∩ (Φ j).source))) :
    ∀ i j, ContDiffOn ℝ 2
      (fun u => (Φ j).restrOpen (t j) (ht j) (((Φ i).restrOpen (t i) (ht i)).symm u))
      ((Φ i).restrOpen (t i) (ht i) ''
        (((Φ i).restrOpen (t i) (ht i)).source ∩ ((Φ j).restrOpen (t j) (ht j)).source)) := by
  intro i j
  have hfun : (fun u => (Φ j).restrOpen (t j) (ht j) (((Φ i).restrOpen (t i) (ht i)).symm u))
      = fun u => Φ j ((Φ i).symm u) := by
    funext u
    simp only [OpenPartialHomeomorph.coe_restrOpen, OpenPartialHomeomorph.coe_restrOpen_symm]
  rw [hfun]
  refine (hC2 i j).mono ?_
  rintro u ⟨x, hx, rfl⟩
  exact ⟨x, ⟨hx.1.1, hx.2.1⟩, by simp only [OpenPartialHomeomorph.coe_restrOpen]⟩

/-- Restricting the charts of a family to an open family preserves the injectivity of the
derivatives of the transitions. -/
private lemma injective_fderiv_transition_restrOpen
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {m : ℕ} (Φ : Fin m → OpenPartialHomeomorph X E) (t : Fin m → Set X) (ht : ∀ i, IsOpen (t i))
    (hinj : ∀ i j, ∀ u ∈ (Φ i) '' ((Φ i).source ∩ (Φ j).source),
      Function.Injective (fderiv ℝ (fun v => Φ j ((Φ i).symm v)) u)) :
    ∀ i j, ∀ u ∈ (Φ i).restrOpen (t i) (ht i) ''
        (((Φ i).restrOpen (t i) (ht i)).source ∩ ((Φ j).restrOpen (t j) (ht j)).source),
      Function.Injective (fderiv ℝ
        (fun v => (Φ j).restrOpen (t j) (ht j) (((Φ i).restrOpen (t i) (ht i)).symm v)) u) := by
  intro i j u hu
  have hfun : (fun v => (Φ j).restrOpen (t j) (ht j) (((Φ i).restrOpen (t i) (ht i)).symm v))
      = fun v => Φ j ((Φ i).symm v) := by
    funext v
    simp only [OpenPartialHomeomorph.coe_restrOpen, OpenPartialHomeomorph.coe_restrOpen_symm]
  rw [hfun]
  obtain ⟨x, hx, rfl⟩ := hu
  exact hinj i j _ ⟨x, ⟨hx.1.1, hx.2.1⟩, by simp only [OpenPartialHomeomorph.coe_restrOpen]⟩

end RestrOpenTransfer

/-- **A finite good cover subordinate to an open cover of a compact smooth manifold.**  For a
compact `T2` smooth manifold modelled on `EuclideanSpace ℝ (Fin n)` and any open cover `O` of it,
there is a finite open cover all of whose nonempty finite intersections are contractible and every
member of which is contained in some `O i`. -/
theorem finiteGoodCover_subordinate_of_charted
    {n : ℕ} (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    {ι : Type*} (O : ι → Set X) (hOopen : ∀ i, IsOpen (O i)) (hOcov : ⋃ i, O i = univ) :
    ∃ (m : ℕ) (U : Fin m → Set X) (r : Fin m → ι),
      (∀ i, IsOpen (U i)) ∧ (⋃ i, U i) = Set.univ ∧
      (∀ S : Finset (Fin m), S.Nonempty → (⋂ i ∈ S, U i).Nonempty →
        ContractibleSpace ↥(⋂ i ∈ S, U i)) ∧
      (∀ i, U i ⊆ O (r i)) := by
  classical
  -- choose, for every point, a chart of the manifold whose source is inside some `O i`
  have hex : ∀ x : X, ∃ i : ι, x ∈ O i := by
    intro x
    have hx : x ∈ ⋃ i, O i := by rw [hOcov]; exact mem_univ x
    simpa only [Set.mem_iUnion] using hx
  let jdx : X → ι := fun x => Classical.choose (hex x)
  have hjdx : ∀ x, x ∈ O (jdx x) := fun x => Classical.choose_spec (hex x)
  let O' : X → Set X := fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∩ O (jdx x)
  have hO'open : ∀ x, IsOpen (O' x) :=
    fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.inter (hOopen (jdx x))
  have hO'cov : univ ⊆ ⋃ x, O' x := by
    intro x _
    rw [Set.mem_iUnion]
    exact ⟨x, mem_chart_source _ x, hjdx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O' hO'open hO'cov
  -- a finite atlas centred at the chosen points, restricted to be subordinate to `O`
  let y : Fin s.card → X := fun k => (s.equivFin.symm k).1
  let c : Fin s.card → EuclideanSpace ℝ (Fin n) := fun k => chartAt _ (y k) (y k)
  let Φ : Fin s.card → OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)) := fun k =>
    (chartAt _ (y k)).trans (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c k))
  let t : Fin s.card → Set X := fun k => O (jdx (y k))
  have ht : ∀ k, IsOpen (t k) := fun k => hOopen _
  let Ψ : Fin s.card → OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)) := fun k =>
    (Φ k).restrOpen (t k) (ht k)
  have hΦsource : ∀ k, (Φ k).source = (chartAt (EuclideanSpace ℝ (Fin n)) (y k)).source := by
    intro k
    simp only [Φ, OpenPartialHomeomorph.trans_source,
      Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph_source, Set.preimage_univ,
      Set.inter_univ]
  have hΦapply : ∀ k, Φ k (y k) = 0 := by
    intro k
    simp only [Φ, OpenPartialHomeomorph.trans_apply,
      Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph_apply, c, sub_self]
  have hΨsource : ∀ k, (Ψ k).source = (chartAt (EuclideanSpace ℝ (Fin n)) (y k)).source ∩ t k := by
    intro k
    simp only [Ψ, OpenPartialHomeomorph.restrOpen_source, hΦsource k]
  have hΨapply : ∀ k, Ψ k (y k) = 0 := by
    intro k
    simp only [Ψ, OpenPartialHomeomorph.coe_restrOpen, hΦapply k]
  have hΨmem_src : ∀ k, y k ∈ (Ψ k).source := by
    intro k
    rw [hΨsource k]
    exact ⟨mem_chart_source _ (y k), hjdx (y k)⟩
  have hΨcov : (⋃ k, (Ψ k).source) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    have hz : z ∈ ⋃ i ∈ s, O' i := hs (mem_univ z)
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    have hyi : y (s.equivFin ⟨i, hi⟩) = i := by
      simp only [y]; rw [Equiv.symm_apply_apply]
    refine Set.mem_iUnion.mpr ⟨s.equivFin ⟨i, hi⟩, ?_⟩
    simp only [hΨsource, hyi, t]
    exact hzi
  -- the two analytic inputs, transported from the atlas to the restricted family
  have hΦmem : ∀ k, Φ k ∈ IsManifold.maximalAtlas (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (∞ : ℕ∞ω) X := by
    intro k
    exact Work.EmbeddedSpheres.TubeProject.trans_mem_maximalAtlas_of_mem_groupoid
      (e := chartAt (EuclideanSpace ℝ (Fin n)) (y k))
      (f := Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c k))
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := (∞ : ℕ∞ω)) (y k))
      (Work.EmbeddedSpheres.TubeProject.subRight_mem_contDiffGroupoid (∞ : ℕ∞ω) (c k))
  have hC2Φ : ∀ i j, ContDiffOn ℝ 2 (fun u => Φ j ((Φ i).symm u))
      ((Φ i) '' ((Φ i).source ∩ (Φ j).source)) := by
    intro i j
    exact (contDiffOn_transition_of_mem_maximalAtlas (n := (∞ : ℕ∞ω))
      (hΦmem i) (hΦmem j)).of_le ENat.LEInfty.out
  have hinjΦ : ∀ i j, ∀ u ∈ (Φ i) '' ((Φ i).source ∩ (Φ j).source),
      Function.Injective (fderiv ℝ (fun v => Φ j ((Φ i).symm v)) u) := by
    intro i j u hu
    exact injective_fderiv_transition_of_mem_maximalAtlas (n := (∞ : ℕ∞ω)) (by decide)
      (hΦmem i) (hΦmem j) hu
  have hC2 : ∀ i j, ContDiffOn ℝ 2 (fun u => Ψ j ((Ψ i).symm u))
      ((Ψ i) '' ((Ψ i).source ∩ (Ψ j).source)) :=
    contDiffOn_transition_restrOpen Φ t ht hC2Φ
  have hinj : ∀ i j, ∀ u ∈ (Ψ i) '' ((Ψ i).source ∩ (Ψ j).source),
      Function.Injective (fderiv ℝ (fun v => Ψ j ((Ψ i).symm v)) u) :=
    injective_fderiv_transition_restrOpen Φ t ht hinjΦ
  -- assemble through the finite good cover subordinate to the `t k`
  have hxΨ : ∀ i, y i ∈ (Ψ i).source ∧ Ψ i (y i) = 0 :=
    fun i => ⟨hΨmem_src i, hΨapply i⟩
  have hW : ∀ i, (Ψ i).source ⊆ t i := by
    intro i; rw [hΨsource i]; exact Set.inter_subset_right
  obtain ⟨m', U, r, h1, h2, h3, h4⟩ :=
    Work.ThomBordism.Grassmann.Torsion.goodCoverSubordinate X Ψ hΨcov y hxΨ hC2 hinj t hW
  exact ⟨m', U, fun i => jdx (y (r i)), h1, h2, h3, fun i => h4 i⟩

/-- **A finite good cover subordinate to the coordinate charts of a real bundle over `Man8`.**
Every real bundle over a closed smooth `8`-manifold admits a finite open cover of its base all of
whose nonempty finite intersections are contractible and each of whose members is contained in a
coordinate chart of the bundle. -/
theorem goodCoverRealBundle {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type}
    (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) :
    ∃ (m : ℕ) (U : Fin m → Set V.pt) (r : Fin m → ι),
      (∀ i, IsOpen (U i)) ∧ (⋃ i, U i) = Set.univ ∧
      (∀ S : Finset (Fin m), S.Nonempty → (⋂ i ∈ S, U i).Nonempty →
        ContractibleSpace ↥(⋂ i ∈ S, U i)) ∧
      (∀ i, U i ⊆ Z.baseSet (r i)) := by
  classical
  obtain ⟨m, U, r, h1, h2, h3, h4⟩ :=
    finiteGoodCover_subordinate_of_charted (n := 8) V.pt (fun i => Z.baseSet i)
      (fun i => Z.isOpen_baseSet i) (by
        rw [Set.eq_univ_iff_forall]
        intro x
        rw [Set.mem_iUnion]
        exact ⟨Z.indexAt x, Z.mem_baseSet_at x⟩)
  exact ⟨m, U, r, h1, h2, h3, h4⟩

end Work.ThomBordism
