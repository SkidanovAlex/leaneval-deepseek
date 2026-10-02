import Mathlib
import Submission.Work.ThomBordism.Grassmann.GoodCover.Defs
import Submission.Work.ThomBordism.Grassmann.Torsion.goodCoverSubordinate
import Submission.Work.ThomBordism.Grassmann.Torsion.annulusFiniteness

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open scoped Topology Manifold ContDiff

namespace Work.ThomBordism.Grassmann.GoodCover

open Work.ThomBordism.Grassmann.Torsion

/-- **A finite good cover of the oriented Grassmannian, subordinate to the chart cells.**

There is a finite family of open sets `U i` covering `G̃r_k(ℝ^{k+m})` such that every *nonempty*
finite intersection `⋂ i ∈ S, U i` is contractible and each `U i` lies in a single chart cell
`baseSet (r i)`.

Route (do not reinvent): `Work.ThomBordism.Grassmann.Torsion.goodCoverSubordinate` (proved)
already produces exactly this from a finite `C²` atlas with injective derivatives together with a
family `W` with `(ψ i).source ⊆ W i`; take `W i := baseSet (r i)`.  The instantiation for the
oriented Grassmannian is carried out *inline* inside the proof of
`Work.ThomBordism.Grassmann.Torsion.annSetHomologyFinite` (in
`Submission/Work/ThomBordism/Grassmann/Torsion/annulusFiniteness.lean`, section "The finite good
cover of the Grassmannian"): a finite subcover of the `chartAt`-charts, translated by
`Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph` so that the reference point maps
to `0`, with `hC2` from `Work.ThomBordism.contDiffOn_transition_of_mem_maximalAtlas` and `hinj`
from `Work.ThomBordism.injective_fderiv_transition_of_mem_maximalAtlas`.  Repackage that
construction into this standalone theorem (the extra conjunct `1 ≤ m'` is free: `OG k m` is
nonempty, so the finite subcover is nonempty). -/
theorem grassmannGoodCover (k m : ℕ) :
    ∃ (m' : ℕ) (_ : 1 ≤ m') (U : Fin m' → Set (OG k m)) (r : Fin m' → ChartIdx k m),
      (∀ i, IsOpen (U i)) ∧ (⋃ i, U i) = Set.univ ∧
      (∀ S : Finset (Fin m'), S.Nonempty → (⋂ i ∈ S, U i).Nonempty →
        ContractibleSpace ↥(⋂ i ∈ S, U i)) ∧
      (∀ i, U i ⊆ (tautologicalBundle k m).baseSet (r i)) := by
  classical
  -- ## 1. A finite chart cover of `OG k m`
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun y : OG k m => (chartAt (EuclideanSpace ℝ (Fin (k * m))) y).source)
    (fun y => (chartAt (EuclideanSpace ℝ (Fin (k * m))) y).open_source)
    (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
  let y : Fin s.card → OG k m := fun j => (s.equivFin.symm j : OG k m)
  let c : Fin s.card → EuclideanSpace ℝ (Fin (k * m)) :=
    fun j => chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j) (y j)
  let ψ : Fin s.card → OpenPartialHomeomorph (OG k m) (EuclideanSpace ℝ (Fin (k * m))) :=
    fun j => (chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).trans
      (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))
  let W : Fin s.card → Set (OG k m) :=
    fun j => (tautologicalBundle k m).baseSet (chartIdxAt (y j))
  -- ## 2. Every chart lies in the maximal atlas of the smooth structure
  have hψmem : ∀ j : Fin s.card, ψ j ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k * m)))) (∞ : ℕ∞ω) (OG k m) := by
    intro j
    exact Work.EmbeddedSpheres.TubeProject.trans_mem_maximalAtlas_of_mem_groupoid
      (e := chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j))
      (f := Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))
      (IsManifold.chart_mem_maximalAtlas
        (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k * m))))
        (n := (∞ : ℕ∞ω)) (y j))
      (Work.EmbeddedSpheres.TubeProject.subRight_mem_contDiffGroupoid (∞ : ℕ∞ω) (c j))
  -- ## 3. The charts cover `OG k m`, and each is centred at `y j`
  have hψcov : (⋃ j : Fin s.card, (ψ j).source) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ (⋃ i ∈ s, (chartAt (EuclideanSpace ℝ (Fin (k * m))) i).source) :=
      hs (Set.mem_univ x)
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    refine Set.mem_iUnion.mpr ⟨s.equivFin ⟨i, hi⟩, ?_⟩
    have hyi : y (s.equivFin ⟨i, hi⟩) = i := by
      simp only [y]; rw [Equiv.symm_apply_apply]
    have hz' : x ∈ ((chartAt (EuclideanSpace ℝ (Fin (k * m))) (y (s.equivFin ⟨i, hi⟩))).trans
        (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph
          (c (s.equivFin ⟨i, hi⟩)))).source := by
      rw [OpenPartialHomeomorph.trans_source, hyi]
      exact ⟨hxi, Set.mem_univ _⟩
    exact hz'
  have hy0 : ∀ j : Fin s.card, y j ∈ (ψ j).source ∧ ψ j (y j) = 0 := by
    intro j
    constructor
    · have hz : y j ∈ ((chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).trans
          (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))).source := by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨mem_chart_source _ _, Set.mem_univ _⟩
      exact hz
    · have hz : ((chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).trans
          (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))) (y j) = 0 := by
        rw [OpenPartialHomeomorph.trans_apply,
          Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph_apply]
        exact sub_self _
      exact hz
  -- ## 4. Each chart source lies in the chart cell of its index
  have hWsub : ∀ j : Fin s.card, (ψ j).source ⊆ W j := by
    intro j z hz
    have h1 : z ∈ (chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).source := by
      have hz' : z ∈ ((chartAt (EuclideanSpace ℝ (Fin (k * m))) (y j)).trans
          (Work.EmbeddedSpheres.TubeProject.subRightOpenPartialHomeomorph (c j))).source := hz
      rw [OpenPartialHomeomorph.trans_source] at hz'
      exact hz'.1
    exact chart_source_subset (chartIdxAt (y j)) (chartSignAt (y j)) h1
  -- ## 5. The transition maps are `C²` with injective derivative
  have hC2 : ∀ i j : Fin s.card,
      ContDiffOn ℝ 2 (fun u : EuclideanSpace ℝ (Fin (k * m)) => ψ j ((ψ i).symm u))
        (ψ i '' ((ψ i).source ∩ (ψ j).source)) := by
    intro i j
    exact (Work.ThomBordism.contDiffOn_transition_of_mem_maximalAtlas (n := (∞ : ℕ∞ω))
      (hψmem i) (hψmem j)).of_le ENat.LEInfty.out
  have hinj : ∀ i j : Fin s.card, ∀ u ∈ ψ i '' ((ψ i).source ∩ (ψ j).source),
      Function.Injective
        (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin (k * m)) => ψ j ((ψ i).symm v)) u) := by
    intro i j u hu
    exact Work.ThomBordism.injective_fderiv_transition_of_mem_maximalAtlas (n := (∞ : ℕ∞ω))
      (by decide) (hψmem i) (hψmem j) hu
  -- ## 6. The good cover subordinate to the chart cells
  obtain ⟨m', U, r, hUopen, hUcov, hUgood, hUsub⟩ :=
    goodCoverSubordinate (OG k m) ψ hψcov y hy0 hC2 hinj W hWsub
  -- ## 7. The cover is nonempty, because `OG k m` is
  have hm' : 1 ≤ m' := by
    rcases Nat.eq_zero_or_pos m' with h0 | hpos
    · exfalso
      have hx : (Classical.arbitrary (OG k m)) ∈ (⋃ i : Fin m', U i) := by
        rw [hUcov]; trivial
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
      have hm'i : (i : ℕ) < m' := i.isLt
      omega
    · exact hpos
  exact ⟨m', hm', U, fun i => chartIdxAt (y (r i)), hUopen, hUcov, hUgood,
    fun i => hUsub i⟩

end Work.ThomBordism.Grassmann.GoodCover
