import Mathlib
import Submission.Work.Serre.Wedge.Defs
import Submission.Work.Serre.Wedge.Geom
import Submission.Work.Serre.Wedge.LES
import Submission.Work.Serre.Wedge.Cell
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Cohomology.localHomology
import Submission.Work.Serre.sigmaRelHomologyIso

set_option synthInstance.maxHeartbeats 400000


/-!
# The homology of the wedge of spheres in degree `n+2`

`Work.Serre.Wedge.wedgeHomology`: the `(n+2)`-nd singular homology of the wedge `wX n ι` of `ι`
copies of `S^{n+2}` is the direct sum `∐_{ι} ℤ`.

The proof uses the two-element open cover `{wOuter, wV}` of the wedge:

* `H_{n+2}(X) ≅ H_{n+2}(X, wOuter)` — the long exact sequence of the pair `(X, wOuter)` and the
  vanishing of the homology of `wOuter` in positive degrees (the outer part deformation retracts
  onto the base point: `Work.Serre.CellStep.compressRel_cellU`);
* excision along the cover `{wOuter, wV}` yields `H_{n+2}(X, wOuter) ≅ H_{n+2}(wV, wV ∩ wOuter)`,
  and `wV` is the union of the open cells, i.e. the disjoint union of `ι` open `(n+2)`-disks
  (`Work.Serre.Wedge.covHomeo`), while `wV ∩ wOuter` is the disjoint union of the corresponding
  shells;
* additivity of relative homology over a disjoint union
  (`Work.Serre.sigmaRelHomologyIso`) and the per-cell computation
  `Work.Serre.Wedge.cellShellImgHomology` finish the job.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option maxHeartbeats 8000000

namespace Work.Serre.Wedge

noncomputable section

/-! ## The cover homeomorphism -/

/-- The map from the disjoint union of the open cells to the wedge. -/
def covFun (n : ℕ) (ι : Type) :
    (Σ i : ι, ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i)) → wX n ι :=
  fun p => (p.2 : wX n ι)

theorem covInducing (n : ℕ) (ι : Type) : Topology.IsInducing (covFun n ι) := by
  rw [inducing_sigma]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · exact Topology.IsEmbedding.subtypeVal.isInducing
  · refine ⟨Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i,
      Work.RatHurewicz.isOpen_cellInterior (n := n) (Y := PUnit) (ι := ι) (f := wF n ι) i, ?_⟩
    intro x
    constructor
    · intro hx
      by_contra hne
      exact Set.disjoint_left.mp
        (Work.RatHurewicz.disjoint_cellInterior (f := wF n ι) x.1 i hne) x.2.2 hx
    · intro hx
      rw [← hx]
      exact x.2.2

theorem covInjective (n : ℕ) (ι : Type) : Function.Injective (covFun n ι) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have hxy : (x : wX n ι) = (y : wX n ι) := h
  have hij : i = j := by
    by_contra hne
    exact Set.disjoint_left.mp
      (Work.RatHurewicz.disjoint_cellInterior (f := wF n ι) i j hne) x.2 (hxy.symm ▸ y.2)
  subst hij
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hxy))

theorem covEmbedding (n : ℕ) (ι : Type) : Topology.IsEmbedding (covFun n ι) :=
  ⟨covInducing n ι, covInjective n ι⟩

theorem covRange (n : ℕ) (ι : Type) : Set.range (covFun n ι) = wV n ι := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact Set.mem_iUnion.mpr ⟨p.1, p.2.2⟩
  · intro hz
    rw [wV, Set.mem_iUnion] at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨⟨i, ⟨z, hi⟩⟩, rfl⟩

/-- **The union of the open cells of the wedge is homeomorphic to their disjoint union.** -/
noncomputable def covHomeo (n : ℕ) (ι : Type) :
    (Σ i : ι, ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i)) ≃ₜ ↥(wV n ι) :=
  (covEmbedding n ι).toHomeomorph.trans (Homeomorph.setCongr (covRange n ι))

/-- The coercion of `Homeomorph.setCongr` is the identity on the ambient type. -/
theorem setCongr_apply_coe {α : Type*} [TopologicalSpace α] {s t : Set α} (h : s = t)
    (x : ↥s) : ((Homeomorph.setCongr h x : ↥t) : α) = x := rfl

theorem covHomeo_apply (n : ℕ) (ι : Type)
    (p : Σ i : ι, ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i)) :
    ((covHomeo n ι p : ↥(wV n ι)) : wX n ι) = (p.2 : wX n ι) := by
  have h := Topology.IsEmbedding.toHomeomorph_apply_coe (covEmbedding n ι) p
  simp only [covHomeo, Homeomorph.trans_apply]
  have h2 : ((Homeomorph.setCongr (covRange n ι)
      ((covEmbedding n ι).toHomeomorph p) : ↥(wV n ι)) : wX n ι)
      = ((covEmbedding n ι).toHomeomorph p : ↥(Set.range (covFun n ι))).1 := rfl
  rw [h2, h]
  rfl

/-- Inside the `i`-th open cell, the trace of the shell is the image of the model shell. -/
theorem mem_cellShellImg_iff (n : ℕ) (ι : Type) {i : ι} {z : wX n ι}
    (hz : z ∈ Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) :
    z ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1 ↔
      z ∈ Work.Serre.cellImg (wF n ι) i (Work.Serre.cellShellSet n (1/2) 1) := by
  constructor
  · intro h
    obtain ⟨j, y, hy, hjy⟩ := Set.mem_iUnion.mp h
    by_cases hji : j = i
    · subst hji
      exact ⟨y, hy, hjy⟩
    · exfalso
      have hyin : y ∈ Work.RatHurewicz.cellInner n :=
        Work.Serre.cellShellSet_subset_cellInner (le_refl 1) hy
      have hzj : z ∈ Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) j :=
        ⟨y, hyin, hjy⟩
      have hzi : z ∈ Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i := hz
      exact Set.disjoint_left.mp
        (Work.RatHurewicz.disjoint_cellInterior (f := wF n ι) j i hji) hzj hzi
  · rintro ⟨y, hy, hjy⟩
    exact Set.mem_iUnion.mpr ⟨i, y, hy, hjy⟩

/-- Inside the `i`-th open cell, the complement of the small closed balls is the image of the
model shell. -/
theorem mem_cellU_iff (n : ℕ) (ι : Type) {i : ι} {z : wX n ι}
    (hz : z ∈ Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) :
    z ∈ wOuter n ι ↔
      z ∈ Work.Serre.cellImg (wF n ι) i (Work.Serre.cellShellSet n (1/2) 1) := by
  obtain ⟨x, hx, hxz⟩ := hz
  rw [← hxz]
  constructor
  · intro h
    rw [wOuter, Work.Serre.cellU, Set.mem_compl_iff] at h
    rw [Work.Serre.CellStep.cellMap_mem_cellBallImg_iff (wF n ι) (by norm_num) i x] at h
    exact ⟨x, Work.Serre.mem_cellShellSet.mpr ⟨not_le.mp h, hx⟩, rfl⟩
  · rintro ⟨y, hy, hjy⟩
    rw [wOuter, Work.Serre.cellU, Set.mem_compl_iff]
    rw [Work.Serre.CellStep.cellMap_mem_cellBallImg_iff (wF n ι) (by norm_num) i x]
    have hyin : y ∈ Work.RatHurewicz.cellInner n :=
      Work.Serre.cellShellSet_subset_cellInner (le_refl 1) hy
    have hyx : (⟨y, hyin⟩ : ↥(Work.RatHurewicz.cellInner n)) = ⟨x, hx⟩ :=
      Work.RatHurewicz.cellMap_injective_cellInner (f := wF n ι) i
        (by simpa using hjy)
    have hyxs : y = x := congrArg Subtype.val hyx
    rw [← hyxs]
    exact not_le.mpr (Work.Serre.mem_cellShellSet.mp hy).1

theorem covHomeo_mem (n : ℕ) (ι : Type)
    (p : Σ i : ι, ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i)) :
    ((covHomeo n ι p : ↥(wV n ι)) : wX n ι) ∈ wOuter n ι ↔
      (p.2 : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1 := by
  rw [covHomeo_apply]
  exact (mem_cellU_iff n ι p.2.2).trans (mem_cellShellImg_iff n ι p.2.2).symm

/-! ## The relative homology of `wV` modulo the shell -/

theorem wedgeRelHomology (n : ℕ) (ι : Type) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of ↥(wV n ι))
      {z : ↥(wV n ι) | (z : wX n ι) ∈ wOuter n ι}).homology (n+2) ≅
      ∐ fun _ : ι => ModuleCat.of ℤ ℤ) := by
  have he : ∀ z : ↥(wV n ι),
      z ∈ {z : ↥(wV n ι) | (z : wX n ι) ∈ wOuter n ι} ↔
        (covHomeo n ι).symm z ∈
          {p : Σ i : ι, ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
            (p.2 : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1} := by
    intro z
    have h := covHomeo_mem n ι ((covHomeo n ι).symm z)
    rwa [Homeomorph.apply_symm_apply] at h
  obtain ⟨e1⟩ := Work.Cohomology.relChains_homeomorph (↥(wV n ι))
    (Σ i : ι, ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i))
    {z : ↥(wV n ι) | (z : wX n ι) ∈ wOuter n ι}
    {p : Σ i : ι, ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
      (p.2 : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1}
    (covHomeo n ι).symm he (n+2)
  obtain ⟨e2⟩ := Work.Serre.sigmaRelHomologyIso
    (fun i : ι => ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i))
    (fun i => {z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
      (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1}) (n+2)
  have e3 : ModuleCat.of ℤ (DirectSum ι fun i => ↑((Work.Cohomology.relChains
      (TopCat.of ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i))
      {z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
        (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1}).homology (n+2)))
      ≅ (∐ fun _ : ι => ModuleCat.of ℤ ℤ) :=
    (Classical.choice (Work.Serre.coprod_directSum_iso (fun i => (Work.Cohomology.relChains
      (TopCat.of ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i))
      {z : ↥(Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) |
        (z : wX n ι) ∈ Work.Serre.cellShellImg (wF n ι) (1/2) 1}).homology (n+2)))).symm
      ≪≫ Limits.Sigma.mapIso (fun i => Classical.choice (cellShellImgHomology n ι i))
  exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

/-! ## The homology of the wedge -/

theorem wedgeHomology (n : ℕ) (ι : Type) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of (wX n ι))).homology (n+2) ≅
      ∐ fun _ : ι => ModuleCat.of ℤ ℤ) := by
  haveI h1 : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(wOuter n ι))).homology (n+2)) :=
    isZero_homology_wOuter n ι (n+2) (by omega)
  haveI h2 : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(wOuter n ι))).homology (n+1)) :=
    isZero_homology_wOuter n ι (n+1) (by omega)
  haveI hiso1 : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of (wX n ι)) (wOuter n ι))) (n+2)) :=
    isIso_homologyMap_rel_of_isZero (TopCat.of (wX n ι)) (wOuter n ι) (n+1) h1 h2
  haveI hiso2 : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of (wX n ι)) (wV n ι) (wOuter n ι)) (n+2)) :=
    Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (wX n ι)) (wV n ι) (wOuter n ι)
      (isOpen_wV n ι) (isOpen_wOuter n ι) (by rw [Set.union_comm]; exact wOuter_union_wV n ι) (n+2)
  obtain ⟨e3⟩ := wedgeRelHomology n ι
  exact ⟨(asIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of (wX n ι)) (wOuter n ι))) (n+2)))
    ≪≫ (asIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of (wX n ι)) (wV n ι) (wOuter n ι)) (n+2))).symm
    ≪≫ e3⟩

end

end Work.Serre.Wedge
