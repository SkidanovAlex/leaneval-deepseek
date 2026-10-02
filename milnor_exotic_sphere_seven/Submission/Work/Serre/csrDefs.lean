import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.StemsB.RelChainsR
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.AttachPush.exists_homotopy_avoids_cellOrigins
import Submission.Work.AttachPush.isClosed_cellMap_image_closedBall

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vocabulary for the rational cell step

The cell step `Work.Serre.cellStepRelHomologyIso` states that for `Z = attachCells n Y ι f` and a
Serre fibration `q : E → Z` with rationally acyclic fibres below `N`, the map of pairs
`(E, q⁻¹Y) → (Z, Y)` induced by `q` is an isomorphism on rational homology in degrees `≤ N`.

This file contains the vocabulary of the proof:

* `Work.Serre.csrRelMapOf` — the map of relative chain complexes over `ℚ` induced by a map of
  pairs (the rational analogue of `Work.Cohomology.relChainsMapOf`);
* `Work.Serre.relChainsRPairMap` — the same in the "subtype/`Set.MapsTo`" form used by the
  cell-step argument;
* the closed half-ball `csrBall`, its boundary sphere `csrSphere`, the open half-ball `csrOpenBall`
  and the centre `csrCentre` of an attached cell, together with the excision/compression data
  (`csrV`, the complement of the centres).

Nothing here is specific to the proof's direction of attack: the pieces are the standard "small
ball around the centre of each cell" of the CW-pair computation.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## Maps of relative chain complexes over `ℚ` -/

/-- The map of relative chain complexes over `ℚ` induced by a map of pairs. -/
noncomputable def csrRelMapOf (X Y : TopCat) (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.StemsB.relChainsR ℚ X A ⟶ Work.StemsB.relChainsR ℚ Y B :=
  cokernel.map (Work.StemsB.relChainsRIncl ℚ X A) (Work.StemsB.relChainsRIncl ℚ Y B)
    (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) g)
    (Work.Cohomology.chainMap ℚ X Y f) (by
      simp only [Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ w)

/-- The map of relative chain complexes over `ℚ` induced by a continuous map of pairs, in the
"subtype" form: `A ⊆ X`, `B ⊆ Y` and `g : C(X,Y)` with `g '' A ⊆ B`. -/
noncomputable def relChainsRPairMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B) :
    Work.StemsB.relChainsR ℚ (TopCat.of X) A ⟶ Work.StemsB.relChainsR ℚ (TopCat.of Y) B :=
  csrRelMapOf (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩) (by ext x; rfl)

/-- The map of relative chain complexes induced by the inclusion of pairs `(U, U ∩ A) → (X, A)`,
for `U A ⊆ X`. -/
noncomputable def relChainsRInclPairMap (X : TopCat) (U A : Set X) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥U) {x : ↥U | (x : X) ∈ A} ⟶
      Work.StemsB.relChainsR ℚ X A :=
  csrRelMapOf (TopCat.of ↥U) X {x : ↥U | (x : X) ∈ A} A
    (Work.Cohomology.subtypeIncl X U)
    (TopCat.ofHom ⟨fun x => ⟨(x.1 : X), x.2⟩, by fun_prop⟩) (by ext x; rfl)

/-! ## The half-balls around the centres of the attached cells -/

/-- The **closed half-ball** of the `i`-th attached cell: the image of the closed model ball of
radius `1/2` under the characteristic map. -/
def csrBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  Work.RatHurewicz.cellMap n Y ι f i '' {y : Work.RatHurewicz.cellDisk n |
    ‖(y : Work.RatHurewicz.CellVec n)‖ ≤ 1/2}

/-- The **boundary sphere** of the `i`-th half-ball. -/
def csrSphere (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  Work.RatHurewicz.cellMap n Y ι f i '' {y : Work.RatHurewicz.cellDisk n |
    ‖(y : Work.RatHurewicz.CellVec n)‖ = 1/2}

/-- The **open half-ball** of the `i`-th attached cell: the image of the open model ball of radius
`1/2`. -/
def csrOpenBall (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  Work.RatHurewicz.cellMap n Y ι f i '' {y : Work.RatHurewicz.cellDisk n |
    ‖(y : Work.RatHurewicz.CellVec n)‖ < 1/2}

/-- The **centre** of the `i`-th attached cell. -/
def csrCentre (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Work.RatHurewicz.attachCells n Y ι f :=
  Work.RatHurewicz.cellOrigin n Y ι f i

/-- The set of all cell centres. -/
def csrCentres (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  Set.range (csrCentre n Y ι f)

/-- The complement of the centres: the space obtained from `attachCells n Y ι f` by deleting the
centres of the attached cells.  It is open (the centres form a closed discrete set). -/
def csrV (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  (csrCentres n Y ι f)ᶜ

/-- The restriction of `q : C(E, Z)` to the preimage of a subset `O ⊆ Z`, as a map into `↥O`. -/
def csrRestrict {E Z : Type} [TopologicalSpace E] [TopologicalSpace Z] (q : C(E, Z)) (O : Set Z) :
    C(↥(q ⁻¹' O), ↥O) :=
  ⟨fun x => ⟨q x.1, x.2⟩, by
    exact Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun x => x.2)⟩

end

end Work.Serre
