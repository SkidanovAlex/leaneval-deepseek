import Mathlib
import Submission.Work.Serre.SPC.One.ComplDefs
import Submission.Work.Serre.SPC.One.SigmaDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pieces of the `1`-cell cover, and the per-piece comparison

For `Z = attachOneCells Y ι f` the open cells `cellInteriorOne Y ι f i` are pairwise disjoint open
sets covering the complement of the old part, and the complement of the centres is
`Y' ∪ ⋃ᵢ (cellInteriorOne i ∖ {centre i})`.  This file fixes the pieces

* `pieceX q i = q⁻¹(cellInteriorOne i)`,
* `pieceY i = cellInteriorOne i`,

with relative parts the preimages of the punctured cell `cellInteriorOne i ∖ {centre i}`, and the
per-piece map `pieceMap q i` induced by `q`, together with the coproduct form `sigmaPieceMap q`.
The per-piece content of the `1`-cell step is that `pieceMap q i` is an isomorphism on `H_m` for
`m < 1 + φ` (and surjective in degree `1 + φ`) when `q` is a Serre fibration with homologically
`φ`-connected fibres.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellS0, Y)}
variable {X : Type} [TopologicalSpace X] {q : C(X, attachOneCells Y ι f)}

/-- The open `i`-th cell with its centre deleted. -/
def cellPunct (i : ι) : Set (attachOneCells Y ι f) :=
  cellInteriorOne Y ι f i \ {oneCellCentreOne Y ι f i}

@[simp] theorem mem_cellPunct {i : ι} {z : attachOneCells Y ι f} :
    z ∈ cellPunct (f := f) i ↔ z ∈ cellInteriorOne Y ι f i ∧ z ≠ oneCellCentreOne Y ι f i :=
  Iff.rfl

/-- The `i`-th piece of the total space: the preimage of the open `i`-th cell. -/
abbrev pieceX (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) (i : ι) : Type :=
  ↥(q ⁻¹' cellInteriorOne Y ι f i)

/-- The relative part of the `i`-th piece of the total space. -/
def pieceXrel (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) (i : ι) :
    Set (pieceX Y ι f q i) :=
  {x | (x : X) ∈ q ⁻¹' cellPunct (f := f) i}

/-- The `i`-th piece of the base. -/
abbrev pieceY (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    (i : ι) : Type :=
  ↥(cellInteriorOne Y ι f i)

/-- The relative part of the `i`-th piece of the base. -/
def pieceYrel (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y)) (i : ι) :
    Set (pieceY Y ι f i) :=
  {y | (y : attachOneCells Y ι f) ∈ cellPunct (f := f) i}

/-- The per-piece map of the total space onto the base. -/
def pieceMap (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) (i : ι) :
    C(pieceX Y ι f q i, pieceY Y ι f i) :=
  ⟨fun x => ⟨q x.1, x.2⟩,
    Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun x => x.2)⟩

theorem pieceMap_mapsTo (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellS0, Y))
    {X : Type} [TopologicalSpace X] (q : C(X, attachOneCells Y ι f)) (i : ι) :
    Set.MapsTo (pieceMap Y ι f q i) (pieceXrel Y ι f q i) (pieceYrel Y ι f i) :=
  fun x hx => hx

/-- **The per-piece comparison**, as a map of relative chain complexes. -/
noncomputable def pieceChainMap (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) {X : Type} [TopologicalSpace X]
    (q : C(X, attachOneCells Y ι f)) (i : ι) :
    Work.Cohomology.relChains (TopCat.of (pieceX Y ι f q i)) (pieceXrel Y ι f q i) ⟶
      Work.Cohomology.relChains (TopCat.of (pieceY Y ι f i)) (pieceYrel Y ι f i) :=
  pairMap (pieceXrel Y ι f q i) (pieceYrel Y ι f i) (pieceMap Y ι f q i)
    (pieceMap_mapsTo Y ι f q i)

/-- **The coproduct of the per-piece comparisons** and the comparison of the disjoint unions of the
pieces. -/
noncomputable def sigmaPieceMap (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellS0, Y)) {X : Type} [TopologicalSpace X]
    (q : C(X, attachOneCells Y ι f)) :
    Work.Cohomology.relChains (TopCat.of (Σ i, pieceX Y ι f q i))
        {x : Σ i, pieceX Y ι f q i | x.2 ∈ pieceXrel Y ι f q x.1} ⟶
      Work.Cohomology.relChains (TopCat.of (Σ i, pieceY Y ι f i))
        {x : Σ i, pieceY Y ι f i | x.2 ∈ pieceYrel Y ι f x.1} :=
  sigmaPairMap (fun i => pieceX Y ι f q i) (fun i => pieceY Y ι f i)
    (fun i => pieceXrel Y ι f q i) (fun i => pieceYrel Y ι f i)
    (fun i => pieceMap Y ι f q i) (fun i => pieceMap_mapsTo Y ι f q i)

end

end Work.Serre.SPC.One
