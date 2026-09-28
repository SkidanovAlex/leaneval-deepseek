import Mathlib
import Submission.Work.Serre.CellStep.Model
import Submission.Work.Serre.CellStep.Piece
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.CellStep.ModelReduction
import Submission.Work.Serre.CellStep.csModelIso
import Submission.Work.Serre.cubeRelIso
import Submission.Work.Serre.cubeDiskHomeo

set_option synthInstance.maxHeartbeats 400000


set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.CellStep

noncomputable section

open Work.RatHurewicz

variable {n : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}

/-! ## The point-set input: the shell inside the open cell

For a point `y` of the open model cell, the image `χ_α y` of the `α`-th characteristic map lies in
the piece relative part `cellShellImg f (3/4) 1` **iff** `y` lies in the model shell
`csSh = {3/4 < ‖y‖ < 1}`.  The point is that the open cells are disjoint (`cls_inner_inj`). -/
theorem cellMap_mem_pieceRelSet_iff (f : ι → C(cellSphere n, Γ)) (α : ι) {y : cellDisk n}
    (hy : y ∈ Work.Serre.csB (n := n)) :
    cellMap n Γ ι f α y ∈ Work.Serre.pieceRelSet n Γ ι f α ↔ y ∈ Work.Serre.csSh (n := n) := by
  constructor
  · intro h
    obtain ⟨i, x, hx, hxy⟩ := (Work.Serre.mem_cellShellImg f).mp h
    have hrel : Relation.EqvGen (attachRel n Γ ι f) (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n))
        (Sum.inr (⟨α, y⟩ : Σ _ : ι, cellDisk n)) :=
      Quotient.exact (show (Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n)) :
          attachCells n Γ ι f) =
          Quotient.mk'' (Sum.inr (⟨α, y⟩ : Σ _ : ι, cellDisk n)) from hxy)
    have hxIn : x ∈ cellInner n := (mem_cellShellSet.mp hx).2
    obtain ⟨-, h2⟩ := Work.Serre.AttachCompress.cls_inner_inj f hxIn hy
      (Work.RatHurewicz.AttachRange.eqvGen_le_cls n Γ ι f hrel)
    exact h2 ▸ hx
  · intro hy'
    exact (Work.Serre.mem_cellShellImg f).mpr ⟨α, y, hy', rfl⟩

/-! ## The continuous section of the characteristic map over the open cell -/

/-- The continuous section of `cellMap α` over the open cell `pieceSet α` (a homeomorphism onto
`csB`). -/
def cpSec (f : ι → C(cellSphere n, Γ)) (α : ι) :
    C(↥(Work.Serre.pieceSet n Γ ι f α), ↥(Work.Serre.csB (n := n))) :=
  Classical.choose (cellInterior_section (n := n) (Y := Γ) (ι := ι) (f := f) α)

theorem cpSec_spec (f : ι → C(cellSphere n, Γ)) (α : ι)
    (y : ↥(Work.Serre.pieceSet n Γ ι f α)) :
    cellMap n Γ ι f α ((cpSec f α y : ↥(Work.Serre.csB (n := n))) : cellDisk n) =
      (y : attachCells n Γ ι f) :=
  Classical.choose_spec (cellInterior_section (n := n) (Y := Γ) (ι := ι) (f := f) α) y

/-! ## The projection of the piece pair and the two presentations -/

/-- The projection `q⁻¹(piece α) → piece α`. -/
def cpProj (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    TopCat.of ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α) ⟶
      TopCat.of ↥(Work.Serre.pieceSet n Γ ι f α) :=
  TopCat.ofHom ⟨fun x => ⟨q x.1, x.2⟩,
    Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun x => x.2)⟩

/-- The relative part of the source of the per-cell map. -/
abbrev cpSrcRel (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) : Set ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α) :=
  {x | (x : X) ∈ q ⁻¹' Work.Serre.pieceRelSet n Γ ι f α}

/-- The relative part of the target of the per-cell map. -/
abbrev cpTarRel (f : ι → C(cellSphere n, Γ)) (α : ι) :
    Set ↥(Work.Serre.pieceSet n Γ ι f α) :=
  {x | (x : attachCells n Γ ι f) ∈ Work.Serre.pieceRelSet n Γ ι f α}

/-- The projection maps the source relative part into the target relative part. -/
theorem cpProj_mem (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    ∀ x : ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α),
      x ∈ cpSrcRel f α q → cpProj f α q x ∈ cpTarRel f α := by
  intro x hx
  show q x.1 ∈ Work.Serre.pieceRelSet n Γ ι f α
  exact hx

/-- **The per-cell map in the `Work.StemsB.relChainsMapOf` presentation.** -/
theorem cellPieceMap_eq_stems (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    Work.Serre.cellPieceMap n Γ ι f α q
      = Work.StemsB.relChainsMapOf (cpProj f α q) (cpSrcRel f α q) (cpTarRel f α)
          (cpProj_mem f α q) := by
  rw [Work.Serre.cellPieceMap, stems_eq_cohom]
  exact relChainsMapOf_congrStems _ _ _ _

/-! ## The two homeomorphisms of pairs -/

/-- The homeomorphism `↥(piece α) ≃ₜ ↥csB` induced by the characteristic map. -/
def cpBaseFun (f : ι → C(cellSphere n, Γ)) (α : ι) :
    ↥(Work.Serre.pieceSet n Γ ι f α) → ↥(Work.Serre.csB (n := n)) :=
  fun y => cpSec f α y

theorem cpBaseFun_apply (f : ι → C(cellSphere n, Γ)) (α : ι)
    (y : ↥(Work.Serre.pieceSet n Γ ι f α)) :
    cpBaseFun f α y = cpSec f α y := rfl

/-- The inverse of `cpBaseFun`, given by the characteristic map. -/
def cpBaseInv (f : ι → C(cellSphere n, Γ)) (α : ι) :
    ↥(Work.Serre.csB (n := n)) → ↥(Work.Serre.pieceSet n Γ ι f α) :=
  fun y => ⟨cellMap n Γ ι f α (y : cellDisk n), by
    refine ⟨(y : cellDisk n), ?_, rfl⟩
    exact y.2⟩

theorem cpBaseInv_apply (f : ι → C(cellSphere n, Γ)) (α : ι)
    (y : ↥(Work.Serre.csB (n := n))) :
    (cpBaseInv f α y : ↥(Work.Serre.pieceSet n Γ ι f α)) =
      ⟨cellMap n Γ ι f α (y : cellDisk n), by
        refine ⟨(y : cellDisk n), ?_, rfl⟩
        exact y.2⟩ := rfl

theorem cpBaseFun_leftInv (f : ι → C(cellSphere n, Γ)) (α : ι) :
    Function.LeftInverse (cpBaseInv f α) (cpBaseFun f α) := by
  intro y
  rw [cpBaseInv_apply, cpBaseFun_apply]
  exact Subtype.ext (cpSec_spec f α y)

theorem cpBaseFun_rightInv (f : ι → C(cellSphere n, Γ)) (α : ι) :
    Function.RightInverse (cpBaseInv f α) (cpBaseFun f α) := by
  intro y
  apply Work.RatHurewicz.cellMap_injective_cellInner (n := n) (Y := Γ) (ι := ι) (f := f) α
  show cellMap n Γ ι f α ((cpSec f α (cpBaseInv f α y) : ↥(Work.Serre.csB (n := n))) : cellDisk n)
    = cellMap n Γ ι f α ((y : ↥(Work.Serre.csB (n := n))) : cellDisk n)
  rw [cpSec_spec f α (cpBaseInv f α y), cpBaseInv_apply f α y]

theorem continuous_cpBaseFun (f : ι → C(cellSphere n, Γ)) (α : ι) :
    Continuous (cpBaseFun f α) :=
  (cpSec f α).continuous

theorem continuous_cpBaseInv (f : ι → C(cellSphere n, Γ)) (α : ι) :
    Continuous (cpBaseInv f α) :=
  Continuous.subtype_mk
    ((cellMap n Γ ι f α).continuous.comp continuous_subtype_val) _

/-- The homeomorphism `↥(piece α) ≃ₜ ↥csB` induced by the characteristic map. -/
def cpBaseHomeo (f : ι → C(cellSphere n, Γ)) (α : ι) :
    ↥(Work.Serre.pieceSet n Γ ι f α) ≃ₜ ↥(Work.Serre.csB (n := n)) where
  toFun := cpBaseFun f α
  invFun := cpBaseInv f α
  left_inv := cpBaseFun_leftInv f α
  right_inv := cpBaseFun_rightInv f α
  continuous_toFun := continuous_cpBaseFun f α
  continuous_invFun := continuous_cpBaseInv f α

/-- The value of the base homeomorphism. -/
theorem cpBaseHomeo_apply (f : ι → C(cellSphere n, Γ)) (α : ι)
    (y : ↥(Work.Serre.pieceSet n Γ ι f α)) :
    cpBaseHomeo f α y = cpSec f α y := rfl

/-! ### The total space -/

/-- The forward map of the total-space homeomorphism: `x ↦ (x, s(q x))`. -/
def cpTotalFun (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α) →
      ↥(Tp q (cellMap n Γ ι f α) (Work.Serre.csB (n := n))) :=
  fun x => ⟨⟨(x.1, (cpSec f α ⟨q x.1, x.2⟩ : ↥(Work.Serre.csB (n := n)))),
      (cpSec_spec f α ⟨q x.1, x.2⟩).symm⟩, (cpSec f α ⟨q x.1, x.2⟩).2⟩

theorem cpTotalFun_apply (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) (x : ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α)) :
    (cpTotalFun f α q x : Work.StemsB.Pullback q (cellMap n Γ ι f α)) =
      ⟨(x.1, (cpSec f α ⟨q x.1, x.2⟩ : ↥(Work.Serre.csB (n := n)))),
        (cpSec_spec f α ⟨q x.1, x.2⟩).symm⟩ := rfl

theorem cpTotalFun_snd (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) (x : ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α)) :
    Work.StemsB.pullbackSnd q (cellMap n Γ ι f α) (cpTotalFun f α q x) =
      ((cpSec f α ⟨q x.1, x.2⟩ : ↥(Work.Serre.csB (n := n))) : cellDisk n) := rfl

/-- The backward map of the total-space homeomorphism: `(x, y) ↦ x`. -/
def cpTotalInv (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    ↥(Tp q (cellMap n Γ ι f α) (Work.Serre.csB (n := n))) →
      ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α) :=
  fun u => ⟨u.1.1.1, by
    refine ⟨u.1.1.2, ?_, ?_⟩
    · exact u.2
    · exact (u.1.2).symm⟩

theorem cpTotalInv_apply (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) (u : ↥(Tp q (cellMap n Γ ι f α) (Work.Serre.csB (n := n)))) :
    (cpTotalInv f α q u : X) = u.1.1.1 := rfl

theorem cpTotalFun_leftInv (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    Function.LeftInverse (cpTotalInv f α q) (cpTotalFun f α q) := by
  intro x
  apply Subtype.ext
  rfl

theorem cpTotalFun_rightInv (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    Function.RightInverse (cpTotalInv f α q) (cpTotalFun f α q) := by
  intro u
  have hmem : q u.1.1.1 ∈ Work.Serre.pieceSet n Γ ι f α := by
    refine ⟨u.1.1.2, ?_, ?_⟩
    · exact u.2
    · exact (u.1.2).symm
  have hmem2 : u.1.1.2 ∈ Work.Serre.csB (n := n) := u.2
  have hkey : cpSec f α ⟨q u.1.1.1, hmem⟩ = (⟨u.1.1.2, hmem2⟩ : ↥(Work.Serre.csB (n := n))) := by
    apply Work.RatHurewicz.cellMap_injective_cellInner (n := n) (Y := Γ) (ι := ι) (f := f) α
    show cellMap n Γ ι f α
        ((cpSec f α ⟨q u.1.1.1, hmem⟩ : ↥(Work.Serre.csB (n := n))) : cellDisk n) =
      cellMap n Γ ι f α u.1.1.2
    rw [cpSec_spec f α ⟨q u.1.1.1, hmem⟩]
    show q u.1.1.1 = cellMap n Γ ι f α u.1.1.2
    exact u.1.2
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val hkey

theorem continuous_cpSecComp (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type}
    [TopologicalSpace X] (q : C(X, attachCells n Γ ι f)) :
    Continuous fun x : ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α) =>
      ((cpSec f α ⟨q x.1, x.2⟩ : ↥(Work.Serre.csB (n := n))) : cellDisk n) :=
  (continuous_subtype_val (p := fun z : cellDisk n => z ∈ Work.Serre.csB (n := n))).comp
    ((cpSec f α).continuous.comp
      (Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun x => x.2)))

theorem continuous_cpTotalFun (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type}
    [TopologicalSpace X] (q : C(X, attachCells n Γ ι f)) :
    Continuous (cpTotalFun f α q) := by
  have hpair : Continuous fun x : ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α) =>
      (⟨(x.1, (cpSec f α ⟨q x.1, x.2⟩ : ↥(Work.Serre.csB (n := n)))),
        (cpSec_spec f α ⟨q x.1, x.2⟩).symm⟩ : Work.StemsB.Pullback q (cellMap n Γ ι f α)) :=
    Continuous.subtype_mk (Continuous.prodMk continuous_subtype_val (continuous_cpSecComp f α q))
      (fun x => (cpSec_spec f α ⟨q x.1, x.2⟩).symm)
  exact Continuous.subtype_mk hpair (fun x => (cpSec f α ⟨q x.1, x.2⟩).2)

theorem continuous_cpTotalInv (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type}
    [TopologicalSpace X] (q : C(X, attachCells n Γ ι f)) :
    Continuous (cpTotalInv f α q) :=
  Continuous.subtype_mk
    (continuous_fst.comp (continuous_subtype_val.comp
      (continuous_subtype_val (p := fun z : Work.StemsB.Pullback q (cellMap n Γ ι f α) =>
        z ∈ Tp q (cellMap n Γ ι f α) (Work.Serre.csB (n := n)))))) _

/-- The total-space homeomorphism `↥(q⁻¹ piece α) ≃ₜ ↥(Tp q (cellMap α) csB)`. -/
def cpTotalHomeo (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α) ≃ₜ
      ↥(Tp q (cellMap n Γ ι f α) (Work.Serre.csB (n := n))) where
  toFun := cpTotalFun f α q
  invFun := cpTotalInv f α q
  left_inv := cpTotalFun_leftInv f α q
  right_inv := cpTotalFun_rightInv f α q
  continuous_toFun := continuous_cpTotalFun f α q
  continuous_invFun := continuous_cpTotalInv f α q

/-- The second component of the total homeomorphism. -/
theorem cpTotalHomeo_snd (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) (x : ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α)) :
    Work.StemsB.pullbackSnd q (cellMap n Γ ι f α) (cpTotalHomeo f α q x) =
      ((cpSec f α ⟨q x.1, x.2⟩ : ↥(Work.Serre.csB (n := n))) : cellDisk n) :=
  cpTotalFun_snd f α q x

/-! ### The two homeomorphisms of pairs -/

/-- The relative part of the total side corresponds to the relative part of the source. -/
theorem cpTotalHomeo_relIff (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    ∀ x : ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α),
      x ∈ cpSrcRel f α q ↔ cpTotalHomeo f α q x ∈ SrcRel q (cellMap n Γ ι f α) := by
  intro x
  rw [show (cpTotalHomeo f α q x ∈ SrcRel q (cellMap n Γ ι f α)) ↔
      Work.StemsB.pullbackSnd q (cellMap n Γ ι f α) (cpTotalHomeo f α q x) ∈
        Work.Serre.csSh (n := n) from Iff.rfl, cpTotalHomeo_snd]
  rw [show (x ∈ cpSrcRel f α q) ↔ q x.1 ∈ Work.Serre.pieceRelSet n Γ ι f α from Iff.rfl]
  have h1 := cellMap_mem_pieceRelSet_iff f α (cpSec f α ⟨q x.1, x.2⟩).2
  rw [show cellMap n Γ ι f α
      ((cpSec f α ⟨q x.1, x.2⟩ : ↥(Work.Serre.csB (n := n))) : cellDisk n) = q x.1
    from cpSec_spec f α ⟨q x.1, x.2⟩] at h1
  exact h1

/-- The relative part of the target corresponds to the model shell in `csB`. -/
theorem cpBaseHomeo_relIff (f : ι → C(cellSphere n, Γ)) (α : ι) :
    ∀ y : ↥(Work.Serre.pieceSet n Γ ι f α),
      y ∈ cpTarRel f α ↔ cpBaseHomeo f α y ∈ TrSh n := by
  intro y
  rw [cpBaseHomeo_apply]
  rw [show (cpSec f α y ∈ TrSh n) ↔
      ((cpSec f α y : ↥(Work.Serre.csB (n := n))) : cellDisk n) ∈ Work.Serre.csSh (n := n)
    from Iff.rfl]
  rw [show (y ∈ cpTarRel f α) ↔ (y : attachCells n Γ ι f) ∈
      Work.Serre.pieceRelSet n Γ ι f α from Iff.rfl]
  have h1 := cellMap_mem_pieceRelSet_iff f α (cpSec f α y).2
  rw [show cellMap n Γ ι f α ((cpSec f α y : ↥(Work.Serre.csB (n := n))) : cellDisk n) = ↑y
    from cpSec_spec f α y] at h1
  exact h1

noncomputable abbrev cpSrcRelMap (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type}
    [TopologicalSpace X] (q : C(X, attachCells n Γ ι f)) :
    Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α))
        (cpSrcRel f α q) ⟶
      Work.Cohomology.relChains (TopCat.of ↥(Tp q (cellMap n Γ ι f α) (Work.Serre.csB (n := n))))
        (SrcRel q (cellMap n Γ ι f α)) :=
  Work.StemsB.relChainsMapOf
    (Work.StemsB.sphHomeoHom (X := TopCat.of ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α))
      (Y := TopCat.of ↥(Tp q (cellMap n Γ ι f α) (Work.Serre.csB (n := n))))
      (cpTotalHomeo f α q))
    (cpSrcRel f α q) (SrcRel q (cellMap n Γ ι f α))
    (Work.StemsB.homeoPairMem (cpTotalHomeo_relIff f α q))

noncomputable abbrev cpTarRelMap (f : ι → C(cellSphere n, Γ)) (α : ι) :
    Work.Cohomology.relChains (TopCat.of ↥(Work.Serre.pieceSet n Γ ι f α)) (cpTarRel f α) ⟶
      Work.Cohomology.relChains (TopCat.of ↥(Work.Serre.csB (n := n))) (TrSh n) :=
  Work.StemsB.relChainsMapOf
    (Work.StemsB.sphHomeoHom (X := TopCat.of ↥(Work.Serre.pieceSet n Γ ι f α))
      (Y := TopCat.of ↥(Work.Serre.csB (n := n))) (cpBaseHomeo f α))
    (cpTarRel f α) (TrSh n) (Work.StemsB.homeoPairMem (cpBaseHomeo_relIff f α))

/-- The two homeomorphisms of pairs intertwine the per-cell projection with the model projection. -/
theorem cpSquare (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    Work.StemsB.sphHomeoHom (X := TopCat.of ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α))
        (Y := TopCat.of ↥(Tp q (cellMap n Γ ι f α) (Work.Serre.csB (n := n))))
        (cpTotalHomeo f α q) ≫ projB q (cellMap n Γ ι f α)
      = cpProj f α q
        ≫ Work.StemsB.sphHomeoHom (X := TopCat.of ↥(Work.Serre.pieceSet n Γ ι f α))
            (Y := TopCat.of ↥(Work.Serre.csB (n := n))) (cpBaseHomeo f α) := by
  apply TopCat.ext
  intro x
  exact Subtype.ext rfl

/-! ## The transfer -/

/-- **The per-cell statement.**  The per-cell map of pairs is an isomorphism on integral homology
in degrees `< (n+2) + φ`; it is the model statement `csModelIso` transported along the
homeomorphisms of pairs given by the cell chart. -/
theorem cellPieceIso (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells n Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (φ : ℕ)
    (hfib : ∀ y : Work.RatHurewicz.attachCells n Γ ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.attachCells n Γ ι f,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre q y))
        (ModuleCat.of ℤ ℤ)))
    (i : ℕ) (hi : i < (n + 2) + φ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.cellPieceMap n Γ ι f α q) i) := by
  haveI hhIso : CategoryTheory.IsIso (cpSrcRelMap f α q) := by
    unfold cpSrcRelMap
    exact Work.StemsB.isIso_relChainsMapOf_homeomorph
      (X := TopCat.of ↥(q ⁻¹' Work.Serre.pieceSet n Γ ι f α))
      (Y := TopCat.of ↥(Tp q (cellMap n Γ ι f α) (Work.Serre.csB (n := n))))
      (cpTotalHomeo f α q) (cpSrcRel f α q) (SrcRel q (cellMap n Γ ι f α))
      (cpTotalHomeo_relIff f α q)
  haveI hgIso : CategoryTheory.IsIso (cpTarRelMap f α) := by
    unfold cpTarRelMap
    exact Work.StemsB.isIso_relChainsMapOf_homeomorph
      (X := TopCat.of ↥(Work.Serre.pieceSet n Γ ι f α))
      (Y := TopCat.of ↥(Work.Serre.csB (n := n))) (cpBaseHomeo f α) (cpTarRel f α) (TrSh n)
      (cpBaseHomeo_relIff f α)
  have hh : CategoryTheory.IsIso (HomologicalComplex.homologyMap (cpSrcRelMap f α q) i) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i)
      (cpSrcRelMap f α q)
  have hg : CategoryTheory.IsIso (HomologicalComplex.homologyMap (cpTarRelMap f α) i) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i)
      (cpTarRelMap f α)
  have hsq : cpSrcRelMap f α q ≫ (Work.Serre.csModelMap n q (cellMap n Γ ι f α))
      = (Work.Serre.cellPieceMap n Γ ι f α q) ≫ cpTarRelMap f α := by
    unfold cpSrcRelMap cpTarRelMap
    rw [csModelMap_eq_stems, cellPieceMap_eq_stems, relChainsMapOfStems_comp,
      relChainsMapOfStems_comp]
    exact relChainsMapOfStems_congr' (cpSquare f α q)
  refine (isIso_homologyMap_iff_of_square (cpSrcRelMap f α q) (cpTarRelMap f α)
    (Work.Serre.cellPieceMap n Γ ι f α q)
    (Work.Serre.csModelMap n q (cellMap n Γ ι f α)) hsq i hh hg).mpr ?_
  exact csModelIso n q hq (cellMap n Γ ι f α) φ
    (fun y j hj1 hj2 => hfib (cellMap n Γ ι f α y) j hj1 hj2)
    (fun y => h0 (cellMap n Γ ι f α y)) i hi

end

end Work.Serre.CellStep
