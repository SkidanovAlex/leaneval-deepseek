import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.Csr.ballPairHomology
import Submission.Work.Cohomology.relChainsHomeomorphCompat

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The base side of the per-cell computation

The pair `(o, o ∖ {c})` of the open half-ball about the centre of the `i`-th attached `(n+2)`-cell
and its punctured version is the pair of the `(n+2)`-disc with its boundary sphere: `cellMap i`
carries the open model ball `dOpen n (1/2)` homeomorphically onto `o` and the puncture at the origin
to the puncture at `c`.  Hence

  `H_{n+2}(o, o ∖ {c};ℤ) ≅ ℤ`  and  `H_m(o, o ∖ {c};ℤ) = 0` for `m ≠ n+2`,

transported from `Work.Serre.Csr.ballPairHomology` (the pair of the Euclidean ball with its punctured
version).
-/

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.Csr

noncomputable section

/-! ## The interior coordinates of the open half-ball -/

/-- A chosen continuous section of `cellMap i` over the interior of the `i`-th cell. -/
noncomputable def cellSection (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    C(↥(Work.RatHurewicz.cellInterior n Y ι f i), ↥(Work.RatHurewicz.cellInner n)) :=
  Classical.choose (Work.RatHurewicz.cellInterior_section (f := f) i)

/-- The defining property of the chosen section. -/
theorem cellSection_spec (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (y : ↥(Work.RatHurewicz.cellInterior n Y ι f i)) :
    Work.RatHurewicz.cellMap n Y ι f i
      ((cellSection n Y ι f i y : ↥(Work.RatHurewicz.cellInner n)) :
        Work.RatHurewicz.cellDisk n) = (y : Work.RatHurewicz.attachCells n Y ι f) :=
  Classical.choose_spec (Work.RatHurewicz.cellInterior_section (f := f) i) y

/-- The open half-ball is contained in the interior of its cell. -/
theorem csrOpenBall_subset_cellInterior (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    csrOpenBall n Y ι f i ⊆ Work.RatHurewicz.cellInterior n Y ι f i := by
  rintro z ⟨a, ha, rfl⟩
  exact ⟨a, Work.RatHurewicz.mem_cellInner_of_norm_lt (lt_trans ha (by norm_num)), rfl⟩

/-- The point of the cell interior lying under a point of the open half-ball. -/
def toInterior (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) :
    ↥(Work.RatHurewicz.cellInterior n Y ι f i) :=
  ⟨z.1, csrOpenBall_subset_cellInterior n Y ι f i z.2⟩

/-- Continuity of the interior coordinate map. -/
theorem continuous_toInterior (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Continuous (toInterior n Y ι f i) :=
  Continuous.subtype_mk
    (f := fun z : ↥(csrOpenBall n Y ι f i) => (z.1 : Work.RatHurewicz.attachCells n Y ι f))
    (by fun_prop) _

/-- The model-cell coordinate of a point of the open half-ball: the inverse of `cellMap i` there. -/
noncomputable def fromBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) : Work.RatHurewicz.cellDisk n :=
  ((cellSection n Y ι f i (toInterior n Y ι f i z) :
    ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n)

/-- `cellMap i` turns the coordinate `fromBall i z` back into `z`. -/
theorem cellMap_fromBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) :
    Work.RatHurewicz.cellMap n Y ι f i (fromBall n Y ι f i z)
      = (z : Work.RatHurewicz.attachCells n Y ι f) :=
  cellSection_spec n Y ι f i (toInterior n Y ι f i z)

/-- The coordinate `fromBall i z` lies in the open model ball of radius `1/2`. -/
theorem fromBall_mem (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) : fromBall n Y ι f i z ∈ dOpen n (1/2) := by
  obtain ⟨a, ha, haz⟩ := z.2
  have key : (⟨a, Work.RatHurewicz.mem_cellInner_of_norm_lt (lt_trans ha (by norm_num))⟩ :
      ↥(Work.RatHurewicz.cellInner n)) =
      cellSection n Y ι f i (toInterior n Y ι f i z) := by
    apply Work.RatHurewicz.cellMap_injective_cellInner (f := f) i
    show Work.RatHurewicz.cellMap n Y ι f i a =
      Work.RatHurewicz.cellMap n Y ι f i ((cellSection n Y ι f i (toInterior n Y ι f i z) :
        ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n)
    rw [cellSection_spec]
    exact haz
  show ((cellSection n Y ι f i (toInterior n Y ι f i z) :
    ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n) ∈ dOpen n (1/2)
  rw [← congrArg Subtype.val key]
  exact ha

/-- The coordinate `fromBall i z` lies in the open model cell. -/
theorem fromBall_mem_cellInner (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι)
    (z : ↥(csrOpenBall n Y ι f i)) : fromBall n Y ι f i z ∈ Work.RatHurewicz.cellInner n :=
  Work.RatHurewicz.mem_cellInner_of_norm_lt
    (lt_trans (fromBall_mem n Y ι f i z) (by norm_num))

/-- Continuity of the inverse model-cell coordinate. -/
theorem continuous_fromBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Continuous (fun z : ↥(csrOpenBall n Y ι f i) => fromBall n Y ι f i z) :=
  continuous_subtype_val.comp
    ((cellSection n Y ι f i).continuous.comp (continuous_toInterior n Y ι f i))

/-- The point of the open half-ball above a point of the open model ball. -/
def toBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) (x : ↥(dOpen n (1/2))) :
    ↥(csrOpenBall n Y ι f i) :=
  ⟨Work.RatHurewicz.cellMap n Y ι f i x.1, x.1, x.2, rfl⟩

/-- `toBall` is the inverse of `fromBall` on the open model ball. -/
theorem fromBall_toBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) (x : ↥(dOpen n (1/2))) :
    fromBall n Y ι f i (toBall n Y ι f i x) = x.1 := by
  have key : (⟨fromBall n Y ι f i (toBall n Y ι f i x),
        fromBall_mem_cellInner n Y ι f i (toBall n Y ι f i x)⟩ :
        ↥(Work.RatHurewicz.cellInner n)) =
      (⟨x.1, Work.RatHurewicz.mem_cellInner_of_norm_lt
        (lt_trans x.2 (by norm_num))⟩ : ↥(Work.RatHurewicz.cellInner n)) := by
    apply Work.RatHurewicz.cellMap_injective_cellInner (f := f) i
    show Work.RatHurewicz.cellMap n Y ι f i (fromBall n Y ι f i (toBall n Y ι f i x)) =
      Work.RatHurewicz.cellMap n Y ι f i x.1
    rw [cellMap_fromBall]
    rfl
  exact congrArg Subtype.val key

/-! ## The homeomorphisms with the model ball -/

/-- **The homeomorphism of the open model ball with the open half-ball of a cell.** -/
def cellOpenHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    ↥(dOpen n (1/2)) ≃ₜ ↥(csrOpenBall n Y ι f i) where
  toFun := toBall n Y ι f i
  invFun := fun z => ⟨fromBall n Y ι f i z, fromBall_mem n Y ι f i z⟩
  left_inv x := Subtype.ext (fromBall_toBall n Y ι f i x)
  right_inv z := Subtype.ext (cellMap_fromBall n Y ι f i z)
  continuous_toFun := by
    refine Continuous.subtype_mk
      (f := fun x : ↥(dOpen n (1/2)) => Work.RatHurewicz.cellMap n Y ι f i x.1) ?_ _
    exact (Work.RatHurewicz.cellMap n Y ι f i).continuous.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk
      (f := fun z : ↥(csrOpenBall n Y ι f i) => fromBall n Y ι f i z) ?_ _
    show Continuous fun z : ↥(csrOpenBall n Y ι f i) =>
      ((cellSection n Y ι f i (toInterior n Y ι f i z) :
        ↥(Work.RatHurewicz.cellInner n)) : Work.RatHurewicz.cellDisk n)
    exact continuous_subtype_val.comp
      ((cellSection n Y ι f i).continuous.comp (continuous_toInterior n Y ι f i))

/-- **The homeomorphism of the open model ball with the Euclidean ball of radius `1/2`.** -/
def openBallHomeo (n : ℕ) :
    ↥(dOpen n (1/2)) ≃ₜ Metric.ball (0 : Work.RatHurewicz.CellVec n) (1/2) where
  toFun x := ⟨(x.1 : Work.RatHurewicz.CellVec n), by
    have hx : ‖(x.1 : Work.RatHurewicz.CellVec n)‖ < 1/2 := x.2
    rw [Metric.mem_ball]
    simpa [dist_eq_norm] using hx⟩
  invFun z := ⟨⟨z.1, by
      have hz : ‖(z.1 : Work.RatHurewicz.CellVec n)‖ < 1/2 := by
        have h := (Metric.mem_ball.mp z.2 : dist (z.1 : Work.RatHurewicz.CellVec n) 0 < 1/2)
        simpa [dist_eq_norm] using h
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm] using le_of_lt (lt_trans hz (by norm_num))⟩, by
    show ‖(z.1 : Work.RatHurewicz.CellVec n)‖ < 1/2
    have h := (Metric.mem_ball.mp z.2 : dist (z.1 : Work.RatHurewicz.CellVec n) 0 < 1/2)
    simpa [dist_eq_norm] using h⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv z := Subtype.ext rfl
  continuous_toFun := (by fun_prop)
  continuous_invFun := (by fun_prop)

/-! ## The two pair isomorphisms -/

/-- **The pair of the open model ball is the pair of the Euclidean ball** (punctured at the
origin); consequently their relative chain complexes agree. -/
theorem dOpenPairIso (n : ℕ) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(dOpen n (1/2)))
        {x : ↥(dOpen n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dPunct n (1/2)}).homology m)
      ≅ ((Work.Cohomology.relChains
        (TopCat.of (Metric.ball (0 : Work.RatHurewicz.CellVec n) (1/2)))
        {z : Metric.ball (0 : Work.RatHurewicz.CellVec n) (1/2) |
          (z : Work.RatHurewicz.CellVec n) ≠ 0}).homology m)) := by
  refine Work.Cohomology.relChainsHomeomorphCompat _ _ _ _ (openBallHomeo n) ?_ m
  intro x
  show ((x : Work.RatHurewicz.cellDisk n) ∈ dOpen n (1/2) ∧
      ((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n) ≠ 0) ↔
    ((openBallHomeo n x : Metric.ball (0 : Work.RatHurewicz.CellVec n) (1/2)) :
      Work.RatHurewicz.CellVec n) ≠ 0
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

/-- **The pair of the open model ball is the pair of the open half-ball of a cell** (punctured at
the origin, resp. its centre); consequently their relative chain complexes agree. -/
theorem cellOpenPairIsoAux (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(dOpen n (1/2)))
        {x : ↥(dOpen n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dPunct n (1/2)}).homology m)
      ≅ ((Work.Cohomology.relChains (TopCat.of ↥(csrOpenBall n Y ι f i))
        {x : ↥(csrOpenBall n Y ι f i) |
          (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}}).homology m)) := by
  refine Work.Cohomology.relChainsHomeomorphCompat _ _ _ _ (cellOpenHomeo n Y ι f i) ?_ m
  intro x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨(toBall n Y ι f i x).2, ?_⟩
    intro hc
    have hc' : Work.RatHurewicz.cellMap n Y ι f i x.1 =
        Work.RatHurewicz.cellMap n Y ι f i (Work.RatHurewicz.cellDiskCentre n) := hc
    have hcancel : (x.1 : Work.RatHurewicz.cellDisk n) = Work.RatHurewicz.cellDiskCentre n :=
      congrArg Subtype.val (Work.RatHurewicz.cellMap_injective_cellInner (f := f) i (by
        show (fun y : ↥(Work.RatHurewicz.cellInner n) =>
            Work.RatHurewicz.cellMap n Y ι f i (y : Work.RatHurewicz.cellDisk n))
          ⟨x.1, Work.RatHurewicz.mem_cellInner_of_norm_lt (lt_trans x.2 (by norm_num))⟩ =
          (fun y : ↥(Work.RatHurewicz.cellInner n) =>
            Work.RatHurewicz.cellMap n Y ι f i (y : Work.RatHurewicz.cellDisk n))
          ⟨Work.RatHurewicz.cellDiskCentre n,
            Work.RatHurewicz.mem_cellInner_of_norm_lt (by
              rw [Work.RatHurewicz.cellDiskCentre_coe]; norm_num)⟩
        exact hc'))
    exact h.2 (by rw [hcancel]; rfl)
  · refine ⟨x.2, ?_⟩
    intro hx0
    have hx : (x.1 : Work.RatHurewicz.cellDisk n) = Work.RatHurewicz.cellDiskCentre n :=
      Subtype.ext hx0
    refine h.2 ?_
    change Work.RatHurewicz.cellMap n Y ι f i x.1 = csrCentre n Y ι f i
    rw [hx]
    rfl

/-- **The pair of the open half-ball of a cell is the pair of the open model ball** (punctured at
the origin); consequently their relative chain complexes agree. -/
theorem cellOpenPairIso (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(csrOpenBall n Y ι f i))
        {x : ↥(csrOpenBall n Y ι f i) |
          (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}}).homology m)
      ≅ ((Work.Cohomology.relChains (TopCat.of ↥(dOpen n (1/2)))
        {x : ↥(dOpen n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dPunct n (1/2)}).homology m)) := by
  obtain ⟨e⟩ := cellOpenPairIsoAux n Y ι f i m
  exact ⟨e.symm⟩

/-- **The base side of the per-cell computation.**  The relative singular homology over `ℤ` of the
pair `(o, o ∖ {c})` is `ℤ` in degree `n+2` and vanishes in every other degree. -/
theorem csrTargetPair (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    (∀ m : ℕ, m ≠ n+2 → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of ↥(csrOpenBall n Y ι f i))
        {x : ↥(csrOpenBall n Y ι f i) |
          (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}}).homology m)) ∧
    Nonempty ((Work.Cohomology.relChains (TopCat.of ↥(csrOpenBall n Y ι f i))
        {x : ↥(csrOpenBall n Y ι f i) |
          (x : Work.RatHurewicz.attachCells n Y ι f) ∈
            csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}}).homology (n+2)
      ≅ ModuleCat.of ℤ ℤ) := by
  have hball := ballPairHomology (n+2) (by omega) (1/2 : ℝ) (by norm_num)
  refine ⟨fun m hm => ?_, ?_⟩
  · obtain ⟨e1⟩ := dOpenPairIso n m
    obtain ⟨e2⟩ := cellOpenPairIso n Y ι f i m
    exact (hball.1 m hm).of_iso (e2 ≪≫ e1)
  · obtain ⟨e1⟩ := dOpenPairIso n (n+2)
    obtain ⟨e2⟩ := cellOpenPairIso n Y ι f i (n+2)
    obtain ⟨e3⟩ := hball.2
    exact ⟨e2 ≪≫ e1 ≪≫ e3⟩

end

end Work.Serre.Csr
