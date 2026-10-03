import Submission.Work.Peluse.SwapE.Reduce
import Submission.Work.Peluse.SwapE.pboxLeOne
import Submission.Work.Peluse.SwapE.massAvgLeOne
import Submission.Work.Peluse.SwapE.windowShrink
import Submission.Work.Peluse.SwapE.slotMassLower
import Submission.Work.Peluse.SwapE.linearInLaw
import Submission.Work.Peluse.SwapE.slotDensity

/-!
# `SwapE` — wiring the proved bricks into the node

The bricks `PboxLeOne`, `MassAvgLeOne`, `WindowShrink`, `LinearInLaw`, `SlotMassLower` and
`SlotDensity` are all **proved** (modules `SwapE/pboxLeOne.lean`, `SwapE/massAvgLeOne.lean`,
`SwapE/windowShrink.lean`, `SwapE/linearInLaw.lean`, `SwapE/slotMassLower.lean`,
`SwapE/slotDensity.lean`), so the proved reductions of `SwapE/Reduce.lean` collapse the node
`DenseEndgame` to the *single* analytic input `MassToCube` (or its squared refinement `SqToCube`).

The chain of this module, in increasing strength of hypothesis:

```
denseEndgame_of_massToCube      : LinearInLaw → SlotDensity → SlotMassLower → MassToCube → DenseEndgame
denseEndgame_of_law             : LinearInLaw → SlotDensity → MassToCube → DenseEndgame
denseEndgame_of_slotDensity     : SlotDensity → MassToCube → DenseEndgame
denseEndgame_of_sq              : SlotDensity → SqToCube → DenseEndgame
denseEndgame_of_massToCubeHolds : MassToCube → DenseEndgame
denseEndgame_of_sqHolds         : SqToCube → DenseEndgame
```

With `SwapE/massToCube.lean` (`Work.Peluse.SwapE.massToCube : MassToCube`) and
`SwapE/sqToCube.lean` (`Work.Peluse.SwapE.sqToCube : SqToCube`) in place, the node itself is
`denseEndgame := denseEndgame_of_sqHolds sqToCube` in `SwapE/Node.lean`.

**Consumer interface.** `Work.Peluse.SwapE.denseEndgame` is character-identical to the frozen
statements file, so it discharges the `SwapA` lane's hypothesis directly:

```
example : Work.Peluse.SwapA.DenseEndgameP := Work.Peluse.SwapE.denseEndgame   -- checks
```
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse

/-- **The node from the four open pieces.**  All five bricks of `SwapE/Assembly.lean` /
`SwapE/Reduce.lean` other than `SlotMassLower` and `MassToCube` are discharged by the proved
children `pboxLeOne`, `massAvgLeOne` and `windowShrink`. -/
theorem denseEndgame_of_massToCube (hL : LinearInLaw) (hD : SlotDensity)
    (hSL : SlotMassLower) (hMC : MassToCube) : DenseEndgame :=
  denseEndgame_of_cube pboxLeOne massAvgLeOne hSL hMC windowShrink

/-- **The node from the three open pieces**, using the proved children
`pboxLeOne`, `massAvgLeOne`, `windowShrink` and the delegated `slotMassLower`. -/
theorem denseEndgame_of_law (hL : LinearInLaw) (hD : SlotDensity) (hMC : MassToCube) :
    DenseEndgame :=
  denseEndgame_of_massToCube hL hD (slotMassLower hL hD pboxLeOne) hMC

/-- **The node from `SlotDensity` and `MassToCube` alone**: `LinearInLaw` is the proved child
`Work.Peluse.SwapE.linearInLaw` (`SwapE/linearInLaw.lean`). -/
theorem denseEndgame_of_slotDensity (hD : SlotDensity) (hMC : MassToCube) : DenseEndgame :=
  denseEndgame_of_law linearInLaw hD hMC

/-- **The node from `SlotDensity` and the squared form `SqToCube`** (via
`massToCube_of_sq`). -/
theorem denseEndgame_of_sq (hD : SlotDensity) (hS : SqToCube) : DenseEndgame :=
  denseEndgame_of_slotDensity hD (massToCube_of_sq hS)

/-- **The node from `MassToCube` alone** (`SlotDensity` is the proved child
`Work.Peluse.SwapE.slotDensity`). -/
theorem denseEndgame_of_massToCubeHolds (hMC : MassToCube) : DenseEndgame :=
  denseEndgame_of_slotDensity slotDensity hMC

/-- **The node from `SqToCube` alone.** -/
theorem denseEndgame_of_sqHolds (hS : SqToCube) : DenseEndgame :=
  denseEndgame_of_slotDensity slotDensity (massToCube_of_sq hS)

end

end Work.Peluse.SwapE
