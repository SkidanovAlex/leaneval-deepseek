import Mathlib
import Submission.Work.Serre.serreC0Defs
import Submission.Work.Serre.serreC0Cover
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.RatHurewicz.AttachPush.Defs

/-!
# The wedge of spheres as a cell attachment: vocabulary

For `n : ℕ` and an index type `ι`, the space

  `Work.Serre.Wedge.wX n ι = Work.RatHurewicz.attachCells n PUnit ι (fun _ => const _ unit)`

is `PUnit` with `ι` many `(n+2)`-cells glued on along the *constant* maps, i.e. the wedge
`⋁_ι S^{n+2}` of `ι` copies of the `(n+2)`-sphere.

This module fixes the notation and the elementary point-set facts about the two open sets

* `wU n ι` — the complement of the set of cell centres ("outer part"), and
* `wV n ι` — the union of the open cells ("inner part"),

used to compute the singular homology of `wX n ι` in degree `n+2`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.Wedge

noncomputable section

/-- The constant attaching family `ι → C(S^{n+1}, PUnit)`. -/
def wF (n : ℕ) (ι : Type) : ι → C(Work.RatHurewicz.cellSphere n, PUnit) :=
  fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) PUnit.unit

/-- **The wedge of `ι` copies of `S^{n+2}`**, as the cell attachment of `ι` many `(n+2)`-cells to
a point along the constant attaching maps. -/
abbrev wX (n : ℕ) (ι : Type) : Type :=
  Work.RatHurewicz.attachCells n PUnit ι (wF n ι)

/-- The base point of the wedge. -/
def wB (n : ℕ) (ι : Type) : wX n ι :=
  Work.RatHurewicz.attachIncl n PUnit ι (wF n ι) PUnit.unit

/-- The centre of the `i`-th cell. -/
def wC (n : ℕ) (ι : Type) (i : ι) : wX n ι :=
  Work.RatHurewicz.cellOrigin n PUnit ι (wF n ι) i

/-- The union of the open cells. -/
def wV (n : ℕ) (ι : Type) : Set (wX n ι) :=
  ⋃ i, Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i

/-- The complement of the cell centres. -/
def wU (n : ℕ) (ι : Type) : Set (wX n ι) :=
  (Work.RatHurewicz.cellCentres n PUnit ι (wF n ι))ᶜ

/-! ## Elementary point-set facts -/

theorem isOpen_wU (n : ℕ) (ι : Type) : IsOpen (wU n ι) :=
  (Work.RatHurewicz.isClosed_cellCentres n PUnit ι (wF n ι)).isOpen_compl

theorem isOpen_wV (n : ℕ) (ι : Type) : IsOpen (wV n ι) :=
  isOpen_iUnion fun i => Work.RatHurewicz.isOpen_cellInterior (n := n) (Y := PUnit)
    (ι := ι) (f := wF n ι) i

/-- The range of `attachIncl` is the single point `wB`. -/
theorem range_attachIncl_wF (n : ℕ) (ι : Type) :
    Set.range (Work.RatHurewicz.attachIncl n PUnit ι (wF n ι)) = {wB n ι} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    refine Set.mem_singleton_iff.mpr ?_
    show Work.RatHurewicz.attachIncl n PUnit ι (wF n ι) y
      = Work.RatHurewicz.attachIncl n PUnit ι (wF n ι) PUnit.unit
    exact congrArg (fun t : PUnit => Work.RatHurewicz.attachIncl n PUnit ι (wF n ι) t)
      (Subsingleton.elim y PUnit.unit)
  · intro hz
    exact ⟨PUnit.unit, (Set.mem_singleton_iff.mp hz).symm⟩

theorem wV_compl (n : ℕ) (ι : Type) : (wV n ι)ᶜ = {wB n ι} := by
  rw [wV, ← Work.RatHurewicz.range_attachIncl_eq_compl_iUnion_cellInterior (n := n) (Y := PUnit)
    (ι := ι) (f := wF n ι), range_attachIncl_wF]

theorem wB_mem_wV_compl (n : ℕ) (ι : Type) : wB n ι ∉ wV n ι := by
  rw [← Set.mem_compl_iff, wV_compl]
  exact Set.mem_singleton _

theorem wB_mem_wU (n : ℕ) (ι : Type) : wB n ι ∈ wU n ι := by
  rw [wU, Work.RatHurewicz.cellCentres, Set.mem_compl_iff, Set.mem_range]
  rintro ⟨i, hi⟩
  exact Work.RatHurewicz.cellOrigin_notMem_range_attachIncl (n := n) (Y := PUnit) (ι := ι)
    (f := wF n ι) i ⟨PUnit.unit, hi.symm⟩

theorem wU_union_wV (n : ℕ) (ι : Type) : wU n ι ∪ wV n ι = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro z
  by_cases hz : z ∈ wV n ι
  · exact Or.inr hz
  · refine Or.inl ?_
    have h1 : z ∈ Set.range (Work.RatHurewicz.attachIncl n PUnit ι (wF n ι)) := by
      rw [Work.RatHurewicz.range_attachIncl_eq_compl_iUnion_cellInterior]
      exact hz
    rw [range_attachIncl_wF] at h1
    rw [wU, Work.RatHurewicz.cellCentres, Set.mem_compl_iff, Set.mem_range]
    rintro ⟨i, hi⟩
    exact Work.RatHurewicz.cellOrigin_notMem_range_attachIncl (n := n) (Y := PUnit) (ι := ι)
      (f := wF n ι) i ⟨PUnit.unit, by
        have h2 : z = wB n ι := Set.mem_singleton_iff.mp h1
        rw [hi, h2]
        rfl⟩

/-- Inside the interior of the `i`-th cell, the complement of the cell centres is exactly the
complement of the centre of that cell. -/
theorem mem_wU_iff_ne_centre_of_mem_cellInterior {n : ℕ} {ι : Type} {i : ι}
    {z : wX n ι} (hz : z ∈ Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i) :
    z ∈ wU n ι ↔ z ≠ wC n ι i := by
  constructor
  · intro hzU h
    rw [wU, Work.RatHurewicz.cellCentres] at hzU
    exact hzU ⟨i, h.symm⟩
  · intro h
    rw [wU, Work.RatHurewicz.cellCentres]
    rintro ⟨j, hj⟩
    have hji : j = i := by
      by_contra hij
      refine Set.disjoint_left.mp
        (Work.RatHurewicz.disjoint_cellInterior (n := n) (Y := PUnit) (ι := ι) (f := wF n ι)
          j i hij) (Work.RatHurewicz.cellOrigin_mem_cellInterior (n := n) (Y := PUnit)
            (ι := ι) (f := wF n ι) j) ?_
      rw [hj]
      exact hz
    exact h (by rw [hji] at hj; exact hj.symm)

theorem wU_inter_wV (n : ℕ) (ι : Type) :
    wU n ι ∩ wV n ι
      = wV n ι \ {z : wX n ι | ∃ i, z = wC n ι i} := by
  ext z
  constructor
  · rintro ⟨hzU, hzV⟩
    refine ⟨hzV, ?_⟩
    rintro ⟨i, hi⟩
    have hzi : z ∈ Work.RatHurewicz.cellInterior n PUnit ι (wF n ι) i := by
      rw [hi]
      exact Work.RatHurewicz.cellOrigin_mem_cellInterior (n := n) (Y := PUnit) (ι := ι) (f := wF n ι) i
    exact (mem_wU_iff_ne_centre_of_mem_cellInterior (i := i) hzi).mp hzU hi
  · rintro ⟨hzV, hz⟩
    refine ⟨?_, hzV⟩
    rw [wV, Set.mem_iUnion] at hzV
    obtain ⟨i, hzi⟩ := hzV
    exact (mem_wU_iff_ne_centre_of_mem_cellInterior (i := i) hzi).mpr (fun h => hz ⟨i, h⟩)

end

end Work.Serre.Wedge
