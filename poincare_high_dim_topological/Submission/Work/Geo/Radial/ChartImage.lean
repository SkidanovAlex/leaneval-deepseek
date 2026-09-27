import Mathlib
import Submission.Work.Geo.Radial.Basic

/-!
# The chart image and the chart inverse

Vocabulary shared by the radial/chart arguments: `chartImage c = c.toFun '' openCube 1` is the
open subspace of `M` that a cube chart `PL.CubeChart n M` parametrises, and `chartInv c` is a
choice-based inverse of `c.toFun` on it (with the junk value `0` off the image).

The two non-elementary facts about them (`isOpen_image_of_subset`, `continuousOn_chartInv`) are
proved in files of the same directory.
-/

open Set Metric
open scoped Topology

namespace Work.Geo.Radial

/-- The image of the unit open cube under a cube chart: the chart neighbourhood of `M`. -/
def chartImage {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M) : Set M :=
  c.toFun '' PL.openCube 1

theorem mem_chartImage {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M)
    {p : M} : p ∈ chartImage c ↔ ∃ y : PL.E n, y ∈ PL.openCube 1 ∧ c.toFun y = p := Iff.rfl

/-- A choice-based inverse of the chart map, defined on the chart image (value `0` off it). -/
noncomputable def chartInv {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) : M → PL.E n := by
  classical
  exact fun p => if h : p ∈ chartImage c then Classical.choose h else 0

theorem chartInv_mem {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M) {p : M}
    (hp : p ∈ chartImage c) : chartInv c p ∈ PL.openCube (n := n) 1 := by
  rw [chartInv]
  rw [dite_eq_left hp]
  exact (Classical.choose_spec hp).1

theorem chartInv_toFun {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M) {p : M}
    (hp : p ∈ chartImage c) : c.toFun (chartInv c p) = p := by
  rw [chartInv]
  rw [dite_eq_left hp]
  exact (Classical.choose_spec hp).2

theorem chartInv_of_notMem {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M)
    {p : M} (hp : p ∉ chartImage c) : chartInv c p = 0 := by
  rw [chartInv]
  exact dite_eq_right hp

/-- `c.toFun` is injective on the open unit cube (it is an embedding there). -/
theorem toFun_injOn_openCube {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M) :
    Set.InjOn c.toFun (PL.openCube (n := n) 1) := by
  intro y hy z hz h
  have h' : (PL.openCube (n := n) 1).domRestrict c.toFun ⟨y, hy⟩ =
      (PL.openCube (n := n) 1).domRestrict c.toFun ⟨z, hz⟩ := h
  exact congrArg Subtype.val (c.emb.toIsEmbedding.injective h')

theorem chartInv_apply {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M)
    {y : PL.E n} (hy : y ∈ PL.openCube (n := n) 1) : chartInv c (c.toFun y) = y := by
  have hmem : c.toFun y ∈ chartImage c := ⟨y, hy, rfl⟩
  exact toFun_injOn_openCube c (chartInv_mem c hmem) hy (chartInv_toFun c hmem)

theorem isOpen_chartImage {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M) :
    IsOpen (chartImage c) := by
  have h : c.toFun '' PL.openCube (n := n) 1 =
      Set.range ((PL.openCube (n := n) 1).domRestrict c.toFun) :=
    (Set.range_domRestrict _ _).symm
  rw [chartImage, h]
  exact c.emb.isOpen_range

/-- The chart map sends compact subsets of the unit cube to compact subsets of `M`. -/
theorem isCompact_image_of_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {V : Set (PL.E n)} (hV : IsCompact V)
    (hVs : V ⊆ PL.openCube (n := n) 1) : IsCompact (c.toFun '' V) :=
  hV.image_of_continuousOn (c.cont.mono hVs)

theorem isCompact_image_closedCube {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) (β : ℝ) (hβ : β < 1) :
    IsCompact (c.toFun '' PL.closedCube (n := n) β) :=
  isCompact_image_of_subset c (by simpa using isCompact_ccubeAround (0 : PL.E n) β)
    (fun y hy i => lt_of_le_of_lt (hy i) hβ)

theorem image_mono_chart {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M)
    {A B : Set (PL.E n)} (h : A ⊆ B) : c.toFun '' A ⊆ c.toFun '' B := Set.image_mono h

end Work.Geo.Radial
