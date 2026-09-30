/-
# `BridgeSquare/Final.lean` — the unconditional challenge theorem

This is the last file of the area `Submission/Work/BridgeSquare/`: it instantiates the assembly of
`Endgame.lean` with the three chain-level fibre identities

* `Work.BridgeSquare.fibreLoopIdentA` (the `κ_{v,2}` longitude),
* `Work.BridgeSquare.fibreLoopIdentB` (the `κ_{v,3}` longitude),
* `Work.BridgeSquare.planeIdentT` (the `κ_{v,2} ∧ κ_{v,3}` plane cycle),

registers the resulting `Work.Final.FinalInputsP` instance, and proves

  `Work.BridgeSquare.aspherical_integer_homology_four_sphere :
      ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere`,

which is the challenge statement (`Challenge.lean`), so that `Submission.lean` is one line.

The chain of implications (`Endgame.lean`), all of it proved:

```
fibreLoopIdentA, fibreLoopIdentB, planeIdentT
   ─► SubtorusBoundaries ─► SubtorusNull                     (a)
                             └─ cuspMap_surjective (c) ─► cuspPair_surjective
                                                            ─► hsurj, hker
                                                                  │
                                       Work.Final.FinalInputsP  ◄──┘
                                                  │
                                                  ▼
                     Work.Final.aspherical_integer_homology_four_sphere_P
```

## Why this is the right wiring (and not the bridge square)

The bridge square `Work.FinalWire.SquareOf (Work.FinalWire.pieceData_of Work.MbarHomology.eA)` —
the originally requested deliverable — is **not provable**: `D.eN k` ends in the
`Classical.choice`-witness `(HomologyBiprod …).some` (`Work.BridgeSquare.pieceData_eN_unfold`), so
the square is a proposition about an opaque term and is independent of the axioms
(`Work.BridgeSquare.squareAt_iff_conj`, `NOTES.md` §2).  The redesign of
`Submission/Work/NOTES_LEAD_aspherical_bridge.md` §1 replaces it by the two *properties* `hsurj`,
`hker` of the actual Mayer–Vietoris map: `Work.HomologyMV.mv_homology_of_props` rebuilds the square
*by construction* for whatever opaque identifications are delivered, so nothing has to be exhibited.
-/
import Mathlib
import Submission.Work.BridgeSquare.Endgame
import Submission.Work.BridgeSquare.fibreLoopIdentA
import Submission.Work.BridgeSquare.fibreLoopIdentB
import Submission.Work.BridgeSquare.planeIdentT

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.Topology

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  The three fibre identities in the bundled form of `Endgame.lean` -/

/-- The `κ_{v,2}` fibre identity. -/
theorem signedFibreIdentA : SignedFibreIdentA := fibreLoopIdentA

/-- The `κ_{v,3}` fibre identity. -/
theorem signedFibreIdentB : SignedFibreIdentB := fibreLoopIdentB

/-- The `κ_{v,2} ∧ κ_{v,3}` plane identity. -/
theorem signedFibreIdentT : SignedFibreIdentT := planeIdentT

/-- **The single remaining mathematical input of the whole project**, now proved. -/
theorem subtorusNull : SubtorusNull (rt := Work.RTOwed.rtData) :=
  subtorusNull_of_signed signedFibreIdentA signedFibreIdentB signedFibreIdentT

/-! ## §2  The instance and the challenge theorem -/

/-- **The final input of the challenge theorem**, built from `SubtorusNull`. -/
@[instance_reducible]
def finalInputsPC : Work.Final.FinalInputsP := finalInputsPOf subtorusNull

-- Registered **globally**, so that `Work.Final.aspherical_integer_homology_four_sphere_P` (and
-- anything else needing a `Work.Final.FinalInputsP`) works in any importing module.
attribute [instance] finalInputsPC

/-- **THE CHALLENGE THEOREM is unconditional.** -/
theorem aspherical_integer_homology_four_sphere :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere_P

end

end Work.BridgeSquare
