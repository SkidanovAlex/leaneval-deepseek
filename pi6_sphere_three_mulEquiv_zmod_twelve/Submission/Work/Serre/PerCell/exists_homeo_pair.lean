import Mathlib
import Submission.Work.Serre.PerCell.Defs
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGeom

/-!
# The per-cell homeomorphism pair over the open half-ball

For the `i`-th attached `(n+2)`-cell of `Z = attachCells n Y ι f`, the characteristic map
`cellMap i` carries the open model ball `dOpen n (1/2)` homeomorphically onto the open half-ball
`csrOpenBall n Y ι f i`, and the puncture at the origin to the puncture at the centre `csrCentre`.
This file records that homeomorphism `csrOpenBallHomeo` together with the induced homeomorphism
`csrPullbackHomeo` of the pullbacks along any map `q : E → Z` — a homeomorphism *of pairs*
`(q⁻¹o, q⁻¹(o∖{c})) ≃ₜ (π⁻¹O, π⁻¹(O∖{0}))` over the model fibration `π = modelFibration`.

The main statement is `Work.Serre.PerCell.exists_homeo_pair`.
-/

set_option maxHeartbeats 800000

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.PerCell

noncomputable section

/-! ## The model coordinate of a point of the open half-ball -/

/-- A chosen continuous section of the characteristic map over the interior of the `i`-th cell. -/
noncomputable def csrSection (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    C(↥(Work.RatHurewicz.cellInterior n Y ι f i), ↥(Work.RatHurewicz.cellInner n)) :=
  Classical.choose (Work.RatHurewicz.cellInterior_section (f := f) i)

/-- The defining property of the chosen section. -/
theorem csrSection_spec (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (y : ↥(Work.RatHurewicz.cellInterior n Y ι f i)) :
    Work.RatHurewicz.cellMap n Y ι f i
      ((csrSection n Y ι f i y : ↥(Work.RatHurewicz.cellInner n)) :
        Work.RatHurewicz.cellDisk n) =
      (y : Work.RatHurewicz.attachCells n Y ι f) :=
  Classical.choose_spec (Work.RatHurewicz.cellInterior_section (f := f) i) y

/-- The open half-ball is contained in the interior of its cell. -/
theorem csrOpenBall_subset_cellInterior (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    csrOpenBall n Y ι f i ⊆ Work.RatHurewicz.cellInterior n Y ι f i := by
  rintro z ⟨a, ha, rfl⟩
  have ha' : ‖(a : Work.RatHurewicz.CellVec n)‖ < 1 / 2 := ha
  exact ⟨a, by show ‖(a : Work.RatHurewicz.CellVec n)‖ < 1; linarith, rfl⟩

/-- The point of the cell interior lying under a point of the open half-ball. -/
def csrToInterior (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) :
    ↥(Work.RatHurewicz.cellInterior n Y ι f i) :=
  ⟨z.1, csrOpenBall_subset_cellInterior n Y ι f i z.2⟩

/-- The model-cell coordinate of a point of the open half-ball: the inverse of `cellMap i` there. -/
noncomputable def csrFromBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) : Work.RatHurewicz.cellDisk n :=
  ((csrSection n Y ι f i (csrToInterior n Y ι f i z) :
    ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n)

/-- `cellMap i` turns the coordinate `csrFromBall i z` back into `z`. -/
theorem cellMap_csrFromBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) :
    Work.RatHurewicz.cellMap n Y ι f i (csrFromBall n Y ι f i z)
      = (z : Work.RatHurewicz.attachCells n Y ι f) :=
  csrSection_spec n Y ι f i (csrToInterior n Y ι f i z)

/-- The coordinate `csrFromBall i z` lies in the open model ball of radius `1/2`. -/
theorem csrFromBall_mem (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) : csrFromBall n Y ι f i z ∈ dOpen n (1/2) := by
  obtain ⟨a, ha, haz⟩ := z.2
  have h1 : (csrSection n Y ι f i (csrToInterior n Y ι f i z) :
        ↥(Work.RatHurewicz.cellInner n)) =
      (⟨a, by
        have ha' : ‖(a : Work.RatHurewicz.CellVec n)‖ < 1 / 2 := ha
        show ‖(a : Work.RatHurewicz.CellVec n)‖ < 1
        linarith⟩ :
        ↥(Work.RatHurewicz.cellInner n)) := by
    apply Work.RatHurewicz.cellMap_injective_cellInner (f := f) i
    show Work.RatHurewicz.cellMap n Y ι f i
        ((csrSection n Y ι f i (csrToInterior n Y ι f i z) :
          ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n) =
      Work.RatHurewicz.cellMap n Y ι f i a
    rw [csrSection_spec]
    exact haz.symm
  show ((csrSection n Y ι f i (csrToInterior n Y ι f i z) :
    ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n) ∈ dOpen n (1/2)
  rw [congrArg Subtype.val h1]
  exact ha

/-- The coordinate `csrFromBall i z` lies in the open model cell. -/
theorem csrFromBall_mem_cellInner (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) :
    csrFromBall n Y ι f i z ∈ Work.RatHurewicz.cellInner n := by
  have h : ‖(csrFromBall n Y ι f i z : Work.RatHurewicz.CellVec n)‖ < 1 / 2 :=
    csrFromBall_mem n Y ι f i z
  show ‖(csrFromBall n Y ι f i z : Work.RatHurewicz.CellVec n)‖ < 1
  linarith

/-- The centre of the model cell lies in the open model cell. -/
theorem cellDiskCentre_mem_cellInner (n : ℕ) :
    Work.RatHurewicz.cellDiskCentre n ∈ Work.RatHurewicz.cellInner n := by
  show ‖((Work.RatHurewicz.cellDiskCentre n : Work.RatHurewicz.cellDisk n) :
    Work.RatHurewicz.CellVec n)‖ < 1
  rw [Work.RatHurewicz.cellDiskCentre_coe]
  simp

/-- **Uniqueness of the model coordinate**: `csrFromBall i z` is the unique point of the open model
ball mapped to `z` by the characteristic map. -/
theorem csrFromBall_eq_of_cellMap_eq (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    {u : Work.RatHurewicz.cellDisk n} (hu : u ∈ Work.RatHurewicz.cellInner n)
    (z : ↥(csrOpenBall n Y ι f i))
    (hz : Work.RatHurewicz.cellMap n Y ι f i u = (z : Work.RatHurewicz.attachCells n Y ι f)) :
    csrFromBall n Y ι f i z = u := by
  have h := cellMap_csrFromBall n Y ι f i z
  have he : Work.RatHurewicz.cellMap n Y ι f i (csrFromBall n Y ι f i z)
      = Work.RatHurewicz.cellMap n Y ι f i u := h.trans hz.symm
  have h2 : (⟨csrFromBall n Y ι f i z, csrFromBall_mem_cellInner n Y ι f i z⟩ :
      ↥(Work.RatHurewicz.cellInner n)) = ⟨u, hu⟩ := by
    apply Work.RatHurewicz.cellMap_injective_cellInner (f := f) i
    exact he
  exact congrArg Subtype.val h2

/-! ## The homeomorphism of the open half-ball with the open model ball -/

/-- **The open half-ball of a cell is the open model ball**: the inverse of the characteristic
map, restricted to the half-ball of radius `1/2`. -/
noncomputable def csrOpenBallHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    ↥(csrOpenBall n Y ι f i) ≃ₜ ↥(dOpen n (1/2)) where
  toFun z := ⟨csrFromBall n Y ι f i z, csrFromBall_mem n Y ι f i z⟩
  invFun x := ⟨Work.RatHurewicz.cellMap n Y ι f i x.1, x.1, x.2, rfl⟩
  left_inv z := Subtype.ext (cellMap_csrFromBall n Y ι f i z)
  right_inv x := by
    apply Subtype.ext
    exact csrFromBall_eq_of_cellMap_eq n Y ι f i
      (u := x.1)
      (by
        have hx : ‖(x.1 : Work.RatHurewicz.CellVec n)‖ < 1 / 2 := x.2
        show ‖(x.1 : Work.RatHurewicz.CellVec n)‖ < 1
        linarith)
      ⟨Work.RatHurewicz.cellMap n Y ι f i x.1, x.1, x.2, rfl⟩ rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp ((csrSection n Y ι f i).continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (Work.RatHurewicz.cellMap n Y ι f i).continuous.comp continuous_subtype_val

@[simp] theorem csrOpenBallHomeo_apply_disk (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) :
    ((csrOpenBallHomeo n Y ι f i z : ↥(dOpen n (1/2))) : Work.RatHurewicz.cellDisk n)
      = csrFromBall n Y ι f i z := rfl

/-- The homeomorphism turns the characteristic map back into the point. -/
theorem cellMap_csrOpenBallHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) :
    Work.RatHurewicz.cellMap n Y ι f i
      ((csrOpenBallHomeo n Y ι f i z : ↥(dOpen n (1/2))) : Work.RatHurewicz.cellDisk n)
      = (z : Work.RatHurewicz.attachCells n Y ι f) :=
  cellMap_csrFromBall n Y ι f i z

/-- The model centre is the point over the cell centre. -/
theorem csrFromBall_eq_centre_iff (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (x : ↥(csrOpenBall n Y ι f i)) :
    (x : Work.RatHurewicz.attachCells n Y ι f) = csrCentre n Y ι f i ↔
      (csrFromBall n Y ι f i x : Work.RatHurewicz.CellVec n) = 0 := by
  constructor
  · intro h
    have h1 : csrFromBall n Y ι f i x = Work.RatHurewicz.cellDiskCentre n := by
      apply csrFromBall_eq_of_cellMap_eq n Y ι f i (u := Work.RatHurewicz.cellDiskCentre n)
        (cellDiskCentre_mem_cellInner n) x
      rw [h]
      rfl
    rw [h1, Work.RatHurewicz.cellDiskCentre_coe]
  · intro h
    have h1 : csrFromBall n Y ι f i x = Work.RatHurewicz.cellDiskCentre n := by
      apply Subtype.ext
      rw [Work.RatHurewicz.cellDiskCentre_coe]
      exact h
    rw [← cellMap_csrFromBall n Y ι f i x, h1]
    rfl

/-- **The pair of the open half-ball is the pair of the open model ball**: the homeomorphism
carries the puncture at the centre of the cell to the puncture at the origin. -/
theorem csrOpenBallHomeo_punct (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (x : ↥(csrOpenBall n Y ι f i)) :
    (x : Work.RatHurewicz.attachCells n Y ι f) ∈
        (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}) ↔
      ((csrOpenBallHomeo n Y ι f i x : ↥(dOpen n (1/2))) :
        Work.RatHurewicz.cellDisk n) ∈ dPunct n (1/2) := by
  have hL : (x : Work.RatHurewicz.attachCells n Y ι f) ∈
      (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}) ↔
        (x : Work.RatHurewicz.attachCells n Y ι f) ≠ csrCentre n Y ι f i := by
    rw [Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hR : ((csrOpenBallHomeo n Y ι f i x : ↥(dOpen n (1/2))) :
        Work.RatHurewicz.cellDisk n) ∈ dPunct n (1/2) ↔
      (csrFromBall n Y ι f i x : Work.RatHurewicz.CellVec n) ≠ 0 := by
    rw [mem_dPunct]
    exact ⟨fun h => h.2, fun h => ⟨(csrOpenBallHomeo n Y ι f i x).2, h⟩⟩
  rw [hL, hR]
  exact not_congr (csrFromBall_eq_centre_iff n Y ι f i x)

/-! ## The pullback of the model fibration over the open half-ball -/

/-- A point of the pullback of `q` along the characteristic map over a point of the open half-ball,
together with its model coordinate. -/
noncomputable def csrPullFun (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι)
    (x : ↥(q ⁻¹' csrOpenBall n Y ι f i)) :
    Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i) :=
  ⟨(x.1, ((csrOpenBallHomeo n Y ι f i ⟨q x.1, x.2⟩ : ↥(dOpen n (1/2))) :
      Work.RatHurewicz.cellDisk n)),
    (cellMap_csrFromBall n Y ι f i ⟨q x.1, x.2⟩).symm⟩

theorem csrPullFun_apply (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι)
    (x : ↥(q ⁻¹' csrOpenBall n Y ι f i)) :
    (csrPullFun n Y ι f q i x).1.1 = x.1 := rfl

theorem csrPullFun_apply_snd (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι)
    (x : ↥(q ⁻¹' csrOpenBall n Y ι f i)) :
    (csrPullFun n Y ι f q i x).1.2 =
      ((csrOpenBallHomeo n Y ι f i ⟨q x.1, x.2⟩ : ↥(dOpen n (1/2))) :
        Work.RatHurewicz.cellDisk n) := rfl

/-- **The homeomorphism of pairs over the pullback**: the pullback of `q` along the characteristic
map over the open half-ball is the open model ball of the model fibration `π = modelFibration`. -/
noncomputable def csrPullbackHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    ↥(q ⁻¹' csrOpenBall n Y ι f i) ≃ₜ
      ↥((modelFibration n Y ι f q i) ⁻¹' (dOpen n (1/2))) where
  toFun x := ⟨csrPullFun n Y ι f q i x,
    (csrOpenBallHomeo n Y ι f i ⟨q x.1, x.2⟩).2⟩
  invFun y := ⟨y.1.1.1, by
    show q y.1.1.1 ∈ csrOpenBall n Y ι f i
    have hy : y.1.1.2 ∈ dOpen n (1/2) := y.2
    rw [y.1.2]
    exact ⟨y.1.1.2, hy, rfl⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext rfl ?_
    have hy : y.1.1.2 ∈ dOpen n (1/2) := y.2
    have hmem : q y.1.1.1 ∈ csrOpenBall n Y ι f i := by
      show q y.1.1.1 ∈ csrOpenBall n Y ι f i
      rw [y.1.2]
      exact ⟨y.1.1.2, hy, rfl⟩
    have hu : y.1.1.2 ∈ Work.RatHurewicz.cellInner n := by
      have h2 : ‖(y.1.1.2 : Work.RatHurewicz.CellVec n)‖ < 1 / 2 := y.2
      show ‖(y.1.1.2 : Work.RatHurewicz.CellVec n)‖ < 1
      linarith
    have hz : Work.RatHurewicz.cellMap n Y ι f i y.1.1.2 =
        (⟨q y.1.1.1, hmem⟩ : ↥(csrOpenBall n Y ι f i)) := y.1.2.symm
    exact csrFromBall_eq_of_cellMap_eq n Y ι f i hu ⟨q y.1.1.1, hmem⟩ hz
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact continuous_subtype_val
    · exact continuous_subtype_val.comp ((csrOpenBallHomeo n Y ι f i).continuous.comp
        (Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) _))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)

/-- **The pullback homeomorphism is a homeomorphism of pairs** over `(o, o∖{c})`. -/
theorem csrPullbackHomeo_punct (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι)
    (x : ↥(q ⁻¹' csrOpenBall n Y ι f i)) :
    (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}) ↔
      ((csrPullbackHomeo n Y ι f q i x :
          Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)) :
        Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)) ∈
        (modelFibration n Y ι f q i) ⁻¹' (dPunct n (1/2)) := by
  show q (x : E) ∈ (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}) ↔
    ((csrOpenBallHomeo n Y ι f i ⟨q (x : E), x.2⟩ : ↥(dOpen n (1/2))) :
      Work.RatHurewicz.cellDisk n) ∈ dPunct n (1/2)
  exact csrOpenBallHomeo_punct n Y ι f i ⟨q (x : E), x.2⟩

/-- **The per-cell homeomorphism pair over the open half-ball.**

The open half-ball `o` of the `i`-th attached cell is the open model ball `dOpen n (1/2)` under the
inverse of the characteristic map (`Ψ = csrOpenBallHomeo`), and the pullback of any map `q : E → Z`
over `o` is correspondingly the pullback of the model fibration over `dOpen n (1/2)`
(`Φ = csrPullbackHomeo`).  The two homeomorphisms are compatible with the punctures (at the centre
`csrCentre` resp. at the origin `0`), with the model fibration, and with the first projection. -/
theorem exists_homeo_pair (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    ∃ (Ψ : ↥(Work.Serre.csrOpenBall n Y ι f i) ≃ₜ ↥(Work.Serre.dOpen n (1/2)))
      (Φ : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i) ≃ₜ
        ↥((Work.Serre.PerCell.modelFibration n Y ι f q i) ⁻¹'
          (Work.Serre.dOpen n (1/2)))),
      (∀ x : ↥(Work.Serre.csrOpenBall n Y ι f i),
        (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})
          ↔ (Ψ x : Work.RatHurewicz.cellDisk n) ∈ Work.Serre.dPunct n (1/2)) ∧
      (∀ x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i),
        (x : E) ∈ q ⁻¹' (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})
          ↔ (Φ x : Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)) ∈
              (Work.Serre.PerCell.modelFibration n Y ι f q i) ⁻¹' (Work.Serre.dPunct n (1/2))) ∧
      (∀ x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i),
        ((Work.Serre.PerCell.modelFibration n Y ι f q i) (Φ x) :
            Work.RatHurewicz.cellDisk n)
          = (Ψ ⟨q (x : E), x.2⟩ : Work.RatHurewicz.cellDisk n)) ∧
      (∀ x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i),
        ((Φ x : Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)) :
            Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)).1.1 = (x : E)) := by
  classical
  refine ⟨csrOpenBallHomeo n Y ι f i, csrPullbackHomeo n Y ι f q i, ?_, ?_, ?_, ?_⟩
  · intro x
    exact csrOpenBallHomeo_punct n Y ι f i x
  · intro x
    exact csrPullbackHomeo_punct n Y ι f q i x
  · intro x
    rfl
  · intro x
    rfl

end

end Work.Serre.PerCell
