import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.DiscPair.cylPairDefs
import Submission.Work.RatHurewicz.AttachCells

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two maps of the cell comparison `TM(D)` of the cellular step

This module only *defines* the maps that occur in the cell comparison of
`Work.Serre.thomCylCellStep` (see `Submission/Work/Serre/CWMODEL_CVN_NOTES.md`), with names that do
not clash with the copies in `Submission/Work/Serre/CellImageEq.lean` (which is not imported here
because it still contains `sorry`s):

* `Work.Serre.cellCupPsi r N D ι f q U` — the geometric cup map
  `z ↦ (cylRetract q)^*(relToAbs z) ⌣ U` from `H^D(Γ',S)` to `H^{D+r+1}(M,A)`;
* `Work.Serre.cellCupForget r N D ι f q` — the forget map
  `H^{D+r+1}(M,A₂) → H^{D+r+1}(M,A)`;

where `Γ' = attachCells (D-2) Γ ι f`, `S = range (attachIncl …)`, `M = cyl q`,
`A = range (cylIncl q)` and `A₂ = (cylRetract q)⁻¹S ∪ A` (`DiscPair.cylPairA₂`).

The *cell comparison* is `range (cellCupPsi … U) = range (cellCupForget …)`; its two halves are the
two inclusions.  See `CWMODEL_CVN_NOTES.md` §2 for the (provable) upper half and §3--§5 for the
lower half (the cellwise non-vanishing of `U`).
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The relative part `S = range (attachIncl …)` of the base pair. -/
abbrev cellCupS (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) :
    Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f) :=
  Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)

/-- The restriction `H^*(M,A) → H^*(A₂,A)` of the pair `A ⊆ A₂ ⊆ M`. -/
abbrev cellCupRestr (r N D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)) ⟶
      Work.Thom.RelCoh ℚ (r + 1)
        ↥(Work.Serre.DiscPair.cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (Set.range (Work.Serre.DiscPair.cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) :=
  (Work.Thom.relCohMap
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(Work.Serre.DiscPair.cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
        Work.Serre.cyl q))
    (Set.range (Work.Serre.DiscPair.cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))
    (Set.range (Work.Serre.cylIncl q))
    (fun x hx => by obtain ⟨y, rfl⟩ := hx; exact ⟨y, rfl⟩) ℚ (r + 1))

/-- The cup map `z ↦ (cylRetract q)^*(relToAbs z) ⌣ U` of the cell comparison. -/
abbrev cellCupPsi (r N D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q))) :
    Work.Thom.RelCoh ℚ D (Work.RatHurewicz.attachCells (D - 2) Γ ι f)
        (cellCupS D Γ ι f) →
      Work.Thom.RelCoh ℚ (D + r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)) :=
  fun z =>
    ((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) D (r + 1)).flip U)
      ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ D).hom
        ((Work.Thom.relToAbs ℚ (cellCupS D Γ ι f) D).hom z))

/-- The forget map `H^{D+r+1}(M,A₂) → H^{D+r+1}(M,A)` of the pair `A ⊆ A₂`. -/
abbrev cellCupForget (r N D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    Work.Thom.RelCoh ℚ (D + r + 1) (Work.Serre.cyl q)
        (Work.Serre.DiscPair.cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) →
      Work.Thom.RelCoh ℚ (D + r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)) :=
  fun w =>
    (Work.Thom.relCohMap (ContinuousMap.id (Work.Serre.cyl q))
      (Set.range (Work.Serre.cylIncl q))
      (Work.Serre.DiscPair.cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (fun x hx => Or.inr hx) ℚ (D + r + 1)).hom w

end

end Work.Serre
