import Mathlib
import Submission.Work.Peluse.PaperRoute.area_a2_of_piecePet
import Submission.Work.Peluse.PaperRoute.piecePetTwo_of_prop36SW

/-!
# The frozen target `AreaA2` from the single §5 chapter `Prop36SW`

`Work.Peluse.PaperRoute.area_a2_of_piecePet` reduces the frozen target
`Work.KMTContract.AreaA2` to the single chapter `Work.Peluse.UControl.PiecePetTwo`
(Peluse's Propositions 3.4 + 3.6 for `(x, x+y, x+P(y))` at a level `≥ 2`).  Weakening the recorded
level from `PiecePet` to `PiecePetTwo` was necessary (`PaperRoute/PiecePetTwo.lean`) because the
recorded `PiecePet` only fixes `1 ≤ s₀` while every consumer needs `s₀ ≥ 2` and no level-raising
transfer exists in that shape.

This file performs the *other* half of that bookkeeping: `PiecePetTwo` is produced from the §5
chapter `Work.Peluse.C46.Prop36SW P` (Peluse's Proposition 3.6 with the window the ladder actually
delivers) by `Work.Peluse.PaperRoute.piecePetTwo_of_prop36SW`, so the frozen target follows from
`Prop36SW` alone:

  `areaA2_of_Prop36SW h := area_a2_of_piecePet (fun P hd => piecePetTwo_of_prop36SW P hd (h P hd))`.

The §5 lane's remaining nodes are precisely those that produce `Prop36SW`:

  `Prop36SW P ← prop36SW_of_ladderA (O2, in flight) ← PeluseLadderA ← ladderA_of_concatFixed (O3,
  proved) ← PeluseConcatFixed ← peluseConcatFixed_of_shortsA (O4, proved) ← ExpansionPETShortA
  (O5, proved) ∧ ConcatBridgeShortA (O6, in flight)`;

as soon as O2 lands, `areaA2_of_Prop36SW (fun P hd => <O2> P (ladderA_of_concatFixed ...))` is the
whole of Area A2.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.PaperRoute

noncomputable section

/-- **The frozen target `Work.KMTContract.AreaA2` from the §5 chapter `Prop36SW`.** -/
theorem areaA2_of_Prop36SW
    (h : ∀ P : Polynomial ℤ, 2 ≤ P.natDegree → Work.Peluse.C46.Prop36SW P) :
    Work.KMTContract.AreaA2 :=
  area_a2_of_piecePet fun P hd => piecePetTwo_of_prop36SW P hd (h P hd)

end

end Work.Peluse.PaperRoute
