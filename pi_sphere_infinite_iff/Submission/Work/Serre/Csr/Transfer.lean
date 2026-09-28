import Mathlib
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.Csr.Target
import Submission.Work.Cohomology.relChainsHomeomorphCompat

/-!
# The transfer from the model disc to the open half-ball

The projection `(e, y) ↦ e` of the pullback of `q` along the characteristic map of the `i`-th cell
is a homeomorphism from the preimage of the open model ball `dOpen n (1/2)` onto the preimage in `E`
of the open half-ball `csrOpenBall i`, and it carries the preimage of the punctured model ball onto
the preimage of the punctured half-ball.  Hence the relative singular homology of the two pairs
agrees in every degree.
-/

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.Csr

noncomputable section

/-- **The transfer homeomorphism.**  The first projection of the pullback of `q` along `cellMap i`
carries the preimage of the open model ball homeomorphically onto the preimage of the open half-ball
`csrOpenBall i`. -/
noncomputable def transferHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    ↥(pPre f q i (dOpen n (1/2))) ≃ₜ ↥(q ⁻¹' (csrOpenBall n Y ι f i)) where
  toFun x := ⟨x.1.1.1, by
    have hx : (x.1.1.2 : Work.RatHurewicz.cellDisk n) ∈ dOpen n (1/2) := x.2
    show q x.1.1.1 ∈ csrOpenBall n Y ι f i
    rw [x.1.2]
    exact ⟨x.1.1.2, hx, rfl⟩⟩
  invFun y := ⟨⟨(y.1, fromBall n Y ι f i ⟨q y.1, y.2⟩),
      (cellMap_fromBall n Y ι f i ⟨q y.1, y.2⟩).symm⟩,
    fromBall_mem n Y ι f i ⟨q y.1, y.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hcell : (⟨fromBall n Y ι f i ⟨q x.1.1.1, by
            have hx : (x.1.1.2 : Work.RatHurewicz.cellDisk n) ∈ dOpen n (1/2) := x.2
            show q x.1.1.1 ∈ csrOpenBall n Y ι f i
            rw [x.1.2]
            exact ⟨x.1.1.2, hx, rfl⟩⟩,
          fromBall_mem_cellInner n Y ι f i _⟩ : ↥(Work.RatHurewicz.cellInner n)) =
          (⟨x.1.1.2, Work.RatHurewicz.mem_cellInner_of_norm_lt
            (lt_trans (show (x.1.1.2 : Work.RatHurewicz.cellDisk n) ∈ dOpen n (1/2) from x.2)
              (by norm_num))⟩ : ↥(Work.RatHurewicz.cellInner n)) := by
        apply Work.RatHurewicz.cellMap_injective_cellInner (f := f) i
        show Work.RatHurewicz.cellMap n Y ι f i (fromBall n Y ι f i ⟨q x.1.1.1, by
            have hx : (x.1.1.2 : Work.RatHurewicz.cellDisk n) ∈ dOpen n (1/2) := x.2
            show q x.1.1.1 ∈ csrOpenBall n Y ι f i
            rw [x.1.2]
            exact ⟨x.1.1.2, hx, rfl⟩⟩) =
          Work.RatHurewicz.cellMap n Y ι f i x.1.1.2
        rw [cellMap_fromBall]
        exact x.1.2
      exact congrArg Subtype.val hcell
  right_inv y := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (f := fun x : ↥(pPre f q i (dOpen n (1/2))) =>
      x.1.1.1) ?_ _
    fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk (f := fun y : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) =>
      (⟨(y.1, fromBall n Y ι f i ⟨q y.1, y.2⟩),
        (cellMap_fromBall n Y ι f i ⟨q y.1, y.2⟩).symm⟩ : csrPull f q i)) ?_ _
    refine Continuous.subtype_mk (f := fun y : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) =>
      (y.1, fromBall n Y ι f i ⟨q y.1, y.2⟩)) ?_ _
    refine Continuous.prodMk (by fun_prop) ?_
    exact (continuous_fromBall n Y ι f i).comp
      (Continuous.subtype_mk (f := fun y : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) => q y.1)
        (by fun_prop) _)

/-- **The pair correspondence of the transfer homeomorphism.** -/
theorem transferPair_mem (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι)
    (x : ↥(pPre f q i (dOpen n (1/2)))) :
    ((x : csrPull f q i) ∈ pPre f q i (dPunct n (1/2))) ↔
      (((transferHomeo n Y ι f q i x : ↥(q ⁻¹' (csrOpenBall n Y ι f i))) : E) ∈
        q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})) := by
  have hx : (x.1.1.2 : Work.RatHurewicz.cellDisk n) ∈ dOpen n (1/2) := x.2
  constructor
  · intro h
    refine ⟨⟨x.1.1.2, hx, x.1.2.symm⟩, ?_⟩
    intro hc
    have hq : q x.1.1.1 =
        Work.RatHurewicz.cellMap n Y ι f i (Work.RatHurewicz.cellDiskCentre n) := hc
    have hcellMap : Work.RatHurewicz.cellMap n Y ι f i x.1.1.2 =
        Work.RatHurewicz.cellMap n Y ι f i (Work.RatHurewicz.cellDiskCentre n) :=
      x.1.2.symm.trans hq
    have hcell : (⟨x.1.1.2, Work.RatHurewicz.mem_cellInner_of_norm_lt
          (lt_trans hx (by norm_num))⟩ : ↥(Work.RatHurewicz.cellInner n)) =
        ⟨Work.RatHurewicz.cellDiskCentre n,
          Work.RatHurewicz.mem_cellInner_of_norm_lt (by
            rw [Work.RatHurewicz.cellDiskCentre_coe]; norm_num)⟩ := by
      apply Work.RatHurewicz.cellMap_injective_cellInner (f := f) i
      show Work.RatHurewicz.cellMap n Y ι f i x.1.1.2 =
        Work.RatHurewicz.cellMap n Y ι f i (Work.RatHurewicz.cellDiskCentre n)
      exact hcellMap
    exact h.2 (congrArg (fun y : ↥(Work.RatHurewicz.cellInner n) =>
      (y : Work.RatHurewicz.CellVec n)) hcell)
  · intro h
    refine ⟨hx, ?_⟩
    intro hx0
    have hxeq : (x.1.1.2 : Work.RatHurewicz.cellDisk n) = Work.RatHurewicz.cellDiskCentre n :=
      Subtype.ext hx0
    refine h.2 ?_
    change q x.1.1.1 = csrCentre n Y ι f i
    rw [x.1.2]
    exact congrArg (fun y : Work.RatHurewicz.cellDisk n =>
      Work.RatHurewicz.cellMap n Y ι f i y) hxeq

/-- **The transfer of the per-cell computation to the open half-ball.**  The relative singular
homology over `ℤ` of the preimage of the model pair `(dOpen n (1/2), dPunct n (1/2))` agrees with
that of the preimage in `E` of the pair `(csrOpenBall i, csrOpenBall i ∖ {csrCentre i})`. -/
theorem csrTransferPair (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains
        (TopCat.of ↥(pPre f q i (dOpen n (1/2))))
        {x : ↥(pPre f q i (dOpen n (1/2))) |
          (x : csrPull f q i) ∈
            pPre f q i (dPunct n (1/2))}).homology m)
      ≅ ((Work.Cohomology.relChains
        (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i)))
        {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) |
          (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}).homology m)) :=
  ⟨(Work.Cohomology.relChainsHomeomorphCompat _ _ _ _ (transferHomeo n Y ι f q i)
    (fun x => transferPair_mem n Y ι f q i x) m).some⟩

end

end Work.Serre.Csr
