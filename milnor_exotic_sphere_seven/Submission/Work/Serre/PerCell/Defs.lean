import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.CellStep.Defs
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.CsrSharp.Defs
import Submission.Work.Serre.cubeDiskHomeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vocabulary for the per-cell comparison over the open half-ball

`Work.Serre.csrPerCellProved` (module `Submission.Work.Serre.csrPerCellProved`) is the per-cell
comparison of the rational cell step: for a Serre fibration `q : E → Z` over
`Z = attachCells n Y ι f` with rationally acyclic fibres below `N`, the map of pairs
`(q⁻¹oᵢ, q⁻¹(oᵢ ∖ {cᵢ})) → (oᵢ, oᵢ ∖ {cᵢ})` over the open half-ball `oᵢ = csrOpenBall i` of the
`i`-th cell is an isomorphism on rational homology in degrees `≤ N`.

This file contains the vocabulary of the proof, so that the pieces of the argument can be stated
and proved independently:

* `Work.Serre.PerCell.modelFibration` — the pullback `π` of `q` along the characteristic map of
  the `i`-th cell (a Serre fibration over the model cell `cellDisk n`);
* `Work.Serre.PerCell.modelAmbient`, `Work.Serre.PerCell.modelRelPart` — the model pair
  `(dOpen n (1/2), dPunct n (1/2))` inside the pullback;
* `Work.Serre.PerCell.modelPairMap` — the per-cell comparison over that model pair;
* `Work.Serre.PerCell.discPairRat` — the rational version of the "disc pair map"
  `Work.Serre.discPairMap` (the comparison over the pair `(D^{n+2}, S^{n+1})` of the model cell),
  which is what the cube statement `Work.Serre.cubeRelIso` computes.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.PerCell

noncomputable section

/-- **The rational disc pair map** `(τ^*E, τ^*E|_{S^{n+1}}) ⟶ (D^{n+2}, S^{n+1})` — the
`ℚ`-coefficient version of `Work.Serre.discPairMap` (`Submission/Work/Serre/CellStep/Defs.lean`). -/
noncomputable def discPairRat (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.RatHurewicz.cellDisk n, B)) :
    Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.discPre n p τ (Work.Serre.cellSphereSet n)) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Work.RatHurewicz.cellDisk n))
        (Work.Serre.cellSphereSet n) :=
  Work.Serre.relChainsRPairMap (Work.Serre.discPre n p τ (Work.Serre.cellSphereSet n))
    (Work.Serre.cellSphereSet n) (Work.StemsB.pullbackSnd p τ) (fun _ hx => hx)

/-- **The model fibration of the `i`-th cell**: the pullback of `q` along the characteristic map
`χᵢ = cellMap n Y ι f i`, as a map over the model cell `cellDisk n`. -/
noncomputable abbrev modelFibration (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    C(Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i),
      Work.RatHurewicz.cellDisk n) :=
  Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i)

/-- The model ambient `dOpen n (1/2)` inside the pullback of `q` along the characteristic map. -/
noncomputable abbrev modelAmbient (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    Set (Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)) :=
  Set.preimage (modelFibration n Y ι f q i) (Work.Serre.dOpen n (1/2))

/-- The model relative part `dPunct n (1/2)` inside the pullback of `q` along the characteristic
map. -/
noncomputable abbrev modelRelPart (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    Set (Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)) :=
  Set.preimage (modelFibration n Y ι f q i) (Work.Serre.dPunct n (1/2))

/-- The relative part of the model pair `(dOpen n (1/2), dPunct n (1/2))`, as a subset of the
ambient `↥(modelAmbient n Y ι f q i)`. -/
noncomputable abbrev modelRelPart' (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    Set ↥(modelAmbient n Y ι f q i) :=
  {x | (x : Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)) ∈ modelRelPart n Y ι f q i}

/-- The relative part of the model pair `(dOpen n (1/2), dPunct n (1/2))`, on the base side. -/
abbrev modelRelPartBase (n : ℕ) : Set ↥(Work.Serre.dOpen n (1/2)) :=
  {x | (x : Work.RatHurewicz.cellDisk n) ∈ Work.Serre.dPunct n (1/2)}

/-- **The per-cell comparison over the model pair** `(dOpen n (1/2), dPunct n (1/2))`: the map of
pairs induced by the model fibration. -/
noncomputable def modelPairMap (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(modelAmbient n Y ι f q i))
        (modelRelPart' n Y ι f q i) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.dOpen n (1/2)))
        (modelRelPartBase n) :=
  Work.Serre.relChainsRPairMap (modelRelPart' n Y ι f q i) (modelRelPartBase n)
    (Work.Serre.csrRestrict (modelFibration n Y ι f q i) (Work.Serre.dOpen n (1/2)))
    (fun _ hx => hx)

end

end Work.Serre.PerCell
