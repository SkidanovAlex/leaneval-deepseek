import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.Serre.OneCell.Defs
import Submission.Work.Serre.OneCell.OneCellGeom
import Submission.Work.Serre.OneCell.Halves
import Submission.Work.Serre.csrDefs
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sharp rational `1`-cell step: vocabulary

`Z = Work.Serre.attachOneCells Y ι f` is `Y` with the intervals `D¹ = [-1,1]` attached along the
maps `f : ι → C(S⁰, Y)` (the workspace's `Work.RatHurewicz.attachCells` only attaches cells of
dimension `≥ 2`, so the `1`-dimensional case is a separate construction, in
`Submission/Work/Serre/E3aDefs.lean`).

The sharp rational `1`-cell step (`Work.Serre.B1Rel.oneCellStepSharp`) is the analogue, for cells of
dimension `1`, of the general sharp rational cell step `Work.Serre.cellStepSharp`: for a Serre
fibration `q : E → Z` whose fibres are rationally acyclic in degrees `0 < j < φ` and rationally
connected, the map of pairs `(E, q⁻¹Y) → (Z, Y)` is an isomorphism on rational homology in degrees
`< 1 + φ` and surjective in degree `1 + φ`.

The structure of the proof follows the general case (`Submission/Work/Serre/CsrSharp/`, which
mirrors `Submission/Work/Serre/SPC/One/`): one compresses the complement of the cell centres onto
the old part, excises the open cover by the open cells and their complement, decomposes the union of
the open cells into a coproduct of single open cells, computes each piece by Serre's `E2(d)`
computation over the cube, and glues back.

This file fixes the vocabulary of that proof:

* `tgtRelOne`, `tgtOne` — the target pair `(oᵢ, oᵢ ∖ {cᵢ})` of the `i`-th piece, `oᵢ` the open
  `i`-th cell and `cᵢ` its centre;
* `srcRelOne`, `srcOne` — the source pair `(q⁻¹'oᵢ, q⁻¹'(oᵢ ∖ {cᵢ}))`;
* `perCellMapOne` — the per-cell comparison `(q⁻¹'oᵢ, q⁻¹'(oᵢ∖{cᵢ})) → (oᵢ, oᵢ∖{cᵢ})`;
* `midUMapOne` — the comparison over the union of the open cells,
  `(q⁻¹'U, q⁻¹'V) → (U, V)` with `U = ⋃ᵢ oᵢ` and `V = Z ∖ {centres}`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.B1Rel

noncomputable section

/-- The relative part of the target pair of the `i`-th piece: the punctured open `i`-th cell. -/
def tgtRelOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) (i : ι) :
    Set ↥(Work.Serre.OneCell.cellInteriorOne Y ι f i) :=
  {x | (x : Work.Serre.attachOneCells Y ι f) ∈
    Work.Serre.OneCell.cellInteriorOne Y ι f i \
      {Work.Serre.OneCell.oneCellCentreOne Y ι f i}}

/-- The target pair of the per-cell comparison, as a relative chain complex over `ℚ`. -/
abbrev tgtOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) (i : ι) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.OneCell.cellInteriorOne Y ι f i))
    (tgtRelOne Y ι f i)

/-- The relative part of the source pair of the `i`-th piece: the preimage of the punctured open
`i`-th cell. -/
def srcRelOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (i : ι) :
    Set ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i) :=
  {x | (x : E) ∈ q ⁻¹' (Work.Serre.OneCell.cellInteriorOne Y ι f i \
    {Work.Serre.OneCell.oneCellCentreOne Y ι f i})}

/-- The source pair of the per-cell comparison, as a relative chain complex over `ℚ`. -/
abbrev srcOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (i : ι) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' Work.Serre.OneCell.cellInteriorOne Y ι f i))
    (srcRelOne Y ι f q i)

/-- **The per-cell comparison**: the map of pairs `(q⁻¹'oᵢ, q⁻¹'(oᵢ∖{cᵢ})) → (oᵢ, oᵢ∖{cᵢ})` on
relative rational chains, induced by `q`. -/
def perCellMapOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) (i : ι) :
    srcOne Y ι f q i ⟶ tgtOne Y ι f i :=
  Work.Serre.relChainsRPairMap (srcRelOne Y ι f q i) (tgtRelOne Y ι f i)
    (Work.Serre.csrRestrict q (Work.Serre.OneCell.cellInteriorOne Y ι f i))
    (fun _ hx => hx)

/-- **The comparison over the union of the open cells**: the map of pairs
`(q⁻¹'U, q⁻¹'V) → (U, V)` induced by `q`, where `U = ⋃ᵢ oᵢ` is the union of the open cells and
`V = Z ∖ {cᵢ}` is the complement of the cell centres. -/
def midUMapOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.Serre.attachOneCells Y ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' Work.Serre.OneCell.cellInnerUnionOne Y ι f))
      {x : ↥(q ⁻¹' Work.Serre.OneCell.cellInnerUnionOne Y ι f) |
        (x : E) ∈ q ⁻¹' (Work.Serre.OneCell.oneCellCentresOne Y ι f)ᶜ} ⟶
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.OneCell.cellInnerUnionOne Y ι f))
      {x : ↥(Work.Serre.OneCell.cellInnerUnionOne Y ι f) |
        (x : Work.Serre.attachOneCells Y ι f) ∈
          (Work.Serre.OneCell.oneCellCentresOne Y ι f)ᶜ} :=
  Work.Serre.relChainsRPairMap _ _ (Work.Serre.csrRestrict q _) (fun _ hx => hx)

/-- The relative part of the middle pair over the complement of the centres. -/
abbrev midRelOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) :
    Set (Work.Serre.attachOneCells Y ι f) := (Work.Serre.OneCell.oneCellCentresOne Y ι f)ᶜ

end

end Work.Serre.B1Rel
