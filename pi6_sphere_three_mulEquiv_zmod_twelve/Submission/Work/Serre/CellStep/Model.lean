import Mathlib
import Submission.Work.Serre.CellStep.Defs
import Submission.Work.Serre.CellStep.Tools

set_option synthInstance.maxHeartbeats 400000


/-!
# The model per-cell vocabulary

Fix the parameters of the cell cover: the pieces are the open model cells (the images of the open
unit ball), and the closed balls removed from the cell centres have radius `ρ = 3/4`.  Inside the
model cell `D^{n+2} = cellDisk n` this gives the sets

* `csSh = {3/4 < ‖x‖ < 1}` — the relative part of an excised piece;
* `csS = {‖x‖ = 7/8}`, `csQ = {7/8 ≤ ‖x‖ ≤ 1}`, `csB = {‖x‖ < 1}`, `csPt = {0}` — the intermediate
  subsets of the chain of triples used in the reduction of the model pair `(csB, csSh)` to the pair
  `(cellDisk, cellSphereSet)`.

`csModelMap` is the map of pairs `(τ^*E, τ^*E|_{csSh}) → (csB, csSh)` induced by the projection, the
model form of the per-cell map.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

variable {n : ℕ}

/-- The relative part of an excised piece: the shell `{3/4 < ‖x‖ < 1}`. -/
abbrev csSh : Set (cellDisk n) := cellShellSet n (3/4) 1

/-- The intermediate sphere `{‖x‖ = 7/8}`. -/
abbrev csS : Set (cellDisk n) := {x | ‖(x : CellVec n)‖ = 7/8}

/-- The intermediate closed shell `{7/8 ≤ ‖x‖ ≤ 1}`. -/
abbrev csQ : Set (cellDisk n) := {x | 7/8 ≤ ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ ≤ 1}

/-- The open model cell. -/
abbrev csB : Set (cellDisk n) := cellInner n

/-- The centre of the model cell. -/
abbrev csPt : Set (cellDisk n) := {x | (x : CellVec n) = 0}

theorem csS_subset_csSh : csS (n := n) ⊆ csSh := by
  intro x hx
  change 3 / 4 < ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ < 1
  rw [show ‖(x : CellVec n)‖ = 7 / 8 from hx]
  norm_num

theorem csS_subset_csQ : csS (n := n) ⊆ csQ := by
  intro x hx
  change 7 / 8 ≤ ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ ≤ 1
  rw [show ‖(x : CellVec n)‖ = 7 / 8 from hx]
  norm_num

theorem cellSphereSet_subset_csQ : cellSphereSet n ⊆ csQ (n := n) := by
  intro x hx
  rw [mem_cellSphereSet] at hx
  change 7 / 8 ≤ ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ ≤ 1
  rw [hx]
  norm_num

theorem csSh_subset_csB : csSh (n := n) ⊆ csB := by
  intro x hx
  change ‖(x : CellVec n)‖ < 1
  exact (mem_cellShellSet.mp hx).2

theorem csPt_subset_csB : csPt (n := n) ⊆ csB := by
  intro x hx
  change ‖(x : CellVec n)‖ < 1
  rw [show (x : CellVec n) = 0 from hx, norm_zero]
  norm_num

theorem norm_coe_le_one (x : cellDisk n) : ‖(x : CellVec n)‖ ≤ 1 := by
  have := Metric.mem_closedBall.mp x.2
  simpa [dist_eq_norm] using this

/-- The model per-cell map: the map of pairs `(τ^*E, τ^*E|_{csSh}) → (csB, csSh)` induced by the
projection `τ^*E → D^{n+2}`. -/
noncomputable def csModelMap (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(cellDisk n, B)) :
    Work.Cohomology.relChains (TopCat.of ↥(discPre n p τ (csB (n := n))))
      {x : ↥(discPre n p τ (csB (n := n))) |
        (x : Work.StemsB.Pullback p τ) ∈ discPre n p τ (csSh (n := n))} ⟶
    Work.Cohomology.relChains (TopCat.of ↥(csB (n := n)))
      {x : ↥(csB (n := n)) | (x : cellDisk n) ∈ csSh (n := n)} :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(discPre n p τ (csB (n := n))))
    (TopCat.of ↥(csB (n := n)))
    {x : ↥(discPre n p τ (csB (n := n))) |
      (x : Work.StemsB.Pullback p τ) ∈ discPre n p τ (csSh (n := n))}
    {x : ↥(csB (n := n)) | (x : cellDisk n) ∈ csSh (n := n)}
    (TopCat.ofHom ⟨fun x => ⟨(Work.StemsB.pullbackSnd p τ) x.1, x.2⟩, by
      exact Continuous.subtype_mk
        ((Work.StemsB.pullbackSnd p τ).continuous.comp continuous_subtype_val) (fun x => x.2)⟩)
    (TopCat.ofHom ⟨fun x => ⟨⟨(Work.StemsB.pullbackSnd p τ) x.1.1, x.1.2⟩, x.2⟩, by
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      exact (Work.StemsB.pullbackSnd p τ).continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)⟩)
    (by ext x; rfl)

end

end Work.Serre
