import Mathlib
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.cubeRelIso
import Submission.Work.Serre.cubeDiskHomeo

set_option synthInstance.maxHeartbeats 400000


/-!
# The model pair map on the closed cell

`Work.Serre.cellStep` reduces, cell by cell, to the statement that for a Serre fibration
`p : E → B`, a map `τ : D^{n+2} → B` from the model cell and a fibre which is homologically
`φ`-connected over every point of the cell, the map of pairs

  `(τ^*E, τ^*E|_{S^{n+1}}) ⟶ (D^{n+2}, S^{n+1})`

induced by the projection is an isomorphism on homology in degrees `< (n+2) + φ`.  This is the
"disc" form of statement `(P_D)` (`Work.Serre.cubeRelIso`), obtained from it by transporting along
the homeomorphism `I^{n+2} ≅ D^{n+2}` (`Work.Serre.cubeDiskHomeo`).

This file contains the vocabulary (`cellSphereSet`, `discPairMap`, `discPairMapRel`) and the
transport statement is delegated.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

/-- The boundary sphere of the model cell, as a subset of the closed model cell. -/
def cellSphereSet (n : ℕ) : Set (cellDisk n) := {x | ‖(x : CellVec n)‖ = 1}

@[simp] theorem mem_cellSphereSet {n : ℕ} {x : cellDisk n} :
    x ∈ cellSphereSet n ↔ ‖(x : CellVec n)‖ = 1 := Iff.rfl

/-- The preimage in the pullback `τ^*E` of a subset `S` of the model cell (the disc analogue of
`Work.Serre.pbPre`). -/
def discPre {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (n : ℕ) (p : C(E, B))
    (τ : C(cellDisk n, B)) (S : Set (cellDisk n)) : Set (Work.StemsB.Pullback p τ) :=
  {x | Work.StemsB.pullbackSnd p τ x ∈ S}

@[simp] theorem mem_discPre {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (n : ℕ)
    (p : C(E, B)) (τ : C(cellDisk n, B)) (S : Set (cellDisk n))
    (x : Work.StemsB.Pullback p τ) : x ∈ discPre n p τ S ↔
      Work.StemsB.pullbackSnd p τ x ∈ S := Iff.rfl

/-- The restriction of the projection `τ^*E → D^{n+2}` to the preimage of the boundary sphere, as a
map of the relative parts. -/
def discPairMapRel {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (n : ℕ)
    (p : C(E, B)) (τ : C(cellDisk n, B)) :
    C(↥(discPre n p τ (cellSphereSet n)), ↥(cellSphereSet n)) :=
  ⟨fun x => ⟨Work.StemsB.pullbackSnd p τ x.1, x.2⟩, by
    exact Continuous.subtype_mk
      ((Work.StemsB.pullbackSnd p τ).continuous.comp continuous_subtype_val) (fun x => x.2)⟩

/-- **The map of pairs `(τ^*E, τ^*E|_{S^{n+1}}) → (D^{n+2}, S^{n+1})`** induced by a continuous map
`p : E → B` along a map `τ : D^{n+2} → B` from the model cell. -/
noncomputable def discPairMap {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (n : ℕ)
    (p : C(E, B)) (τ : C(cellDisk n, B)) :
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
      (discPre n p τ (cellSphereSet n)) ⟶
      Work.Cohomology.relChains (TopCat.of (cellDisk n)) (cellSphereSet n) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback p τ))
    (TopCat.of (cellDisk n)) (discPre n p τ (cellSphereSet n)) (cellSphereSet n)
    (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
    (TopCat.ofHom (discPairMapRel n p τ))
    (by ext x; rfl)

end

end Work.Serre
