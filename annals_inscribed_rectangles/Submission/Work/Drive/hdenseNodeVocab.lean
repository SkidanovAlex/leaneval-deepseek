import Mathlib
import Submission.Work.Drive.hdenseDesignData
import Submission.Work.Drive.T6GenAtDefs
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.diamCoreParity
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.endsParity
import Submission.Work.Drive.chartShiftHsurj
/-!
# The design vocabulary of the `hdense` node, **below** the node (agent of `hdense_sideGerm`)

`Submission/Work/Drive/hdenseOneT.lean` declares `Work.Drive.DesignTripleAtN`, `BlockT6AtN`, `GermDataAtN`
and its importers `germDataAt.lean` / `hdense_identity_of_designTripleAtN.lean` prove the two producers
the node needs.  Those three modules sit **above** the node (they import
`Submission.Work.Drive.hdense_sideGerm`, only for the declarations moved to `hdenseDesignData.lean`),
and `hdenseOneT.lean` additionally *fails to build* (`Work.Drive.T6GenAtDBox` is declared both there
and in `T6GenAtD.lean`), so the node cannot use them at all: Lean forbids import cycles, and the
duplicate declaration makes the whole group unusable.

This module and its two companions `hdenseNodeGerm.lean` / `hdenseNodeE3.lean` are below-the-node
copies of exactly that content, with the same names suffixed `N`, so that the node's own proof can
consume them.  The copies use `Work.Drive.T6GenAtDBox` of `T6GenAtD.lean` (propositionally the same
predicate: `Work.Drive.DiamFamReg` there is already the box-restricted quartet) and they import
`Submission.Work.Drive.hdenseDesignData` instead of the node.  See
`Submission/Work/Drive/NOTE_hdense_import_cycle.md`.
-/
namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The design's one-parameter data of the `hdense` node**: the perturbed-design goodness, the
class-triple oddness, and the three `T6GenAtD` blocks of the block triple at the time `t`. -/
def DesignTripleAtN (Q : ℂ → CappingSpace) (c : ℝ) (cblk : Fin 3 → ℝ)
    (u : Fin 3 → UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  DesignGoodData Q c cblk u t ∧
    Odd (classTripleSet
      (fun k z => chartPert (blk k t) (rotPresentation Q (u k) z))).ncard ∧
    ∀ k : Fin 3,
      T6GenAtDBox (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))
        (cblk (k + 1)) (cblk (k + 2))

end

end Work.Drive

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The per-block transport conclusion `hblock` at the design's triple and parameter**: the `T6`
equivalence of block `k`.  This is the conclusion of the transport wrapper (item (E1) of
`NOTES_LEAD_hdense.md` §3, H4's lane) at the blocks of the design; it is carried as a hypothesis of
the endpoint `Work.Drive.hdense_identity_of_designTripleAtN` until that wrapper lands, at which point
it follows from `DesignTripleAtN`'s third conjunct. -/
def BlockT6AtN (Q : ℂ → CappingSpace) (c : ℝ) (cblk : Fin 3 → ℝ)
    (u : Fin 3 → UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  ∀ k : Fin 3,
    Odd ((topBdryMeet CappingSpace
        (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk) k).ncard) ↔
      (Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
            (cblk (k + 1))
            (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1)))
        ∧ Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
            (cblk (k + 2))
            (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))))

/-- **The germ-lane data at the six ordered pairs of the design's triple.**  These are the inputs of
`Work.Drive.CntAt_cast_eq_sideGerm_of_level_lt_guarded` at the two levels `c`, `cblk j` and at the six
angles `u j - u k`: the parity locality at each level and the cross-level parity agreement.  They are
the "germ locality" hypotheses of the route (proved lemmas
`Work.Drive.sideGerm_parity_eq_of_close_of_separation` and
`Work.Drive.odd_coreSideCount_eq_of_levelBand` with their own separation/`GoodPair` inputs). -/
def GermDataAtN (Q : ℂ → CappingSpace) (c : ℝ) (cblk : Fin 3 → ℝ)
    (u : Fin 3 → UnitAddCircle) (ε : ℝ) : Prop :=
  (∀ (k j : Fin 3), k ≠ j →
    ∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖t‖ < ε → ‖t'‖ < ε →
      GoodAt (fun s p => chartPert s p) Q c (u j - u k) t →
      GoodAt (fun s p => chartPert s p) Q c (u j - u k) t' →
      Odd (CntAt (fun s p => chartPert s p) Q c (u j - u k) t) =
        Odd (CntAt (fun s p => chartPert s p) Q c (u j - u k) t'))
  ∧ (∀ (k j : Fin 3), k ≠ j →
    ∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖t‖ < ε → ‖t'‖ < ε →
      GoodAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t →
      GoodAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t' →
      Odd (CntAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t) =
        Odd (CntAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t'))
  ∧ (∀ (k j : Fin 3), k ≠ j →
    ∀ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4), ‖t‖ < ε →
      GoodAt (fun s p => chartPert s p) Q c (u j - u k) t →
      GoodAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t →
      Odd (CntAt (fun s p => chartPert s p) Q c (u j - u k) t) =
        Odd (CntAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t))

end

end Work.Drive
