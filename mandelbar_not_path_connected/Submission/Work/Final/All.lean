/-
# `Submission/Work/Final/` — the whole area in one import

`import Submission.Work.Final.All` brings in the final wiring of

  `theorem mandelbar_not_path_connected : ¬ IsPathConnected Mandelbar`

modulo the holder structure `Work.Final.FinalInputs`; see `NOTES.md` in this directory for the
field-by-field provenance.

Modules:

* `Defs`     — vocabulary: `RootArc`, `critHeight`, `EquatorLeak`, `BifSide`, `ImplosionSide`,
               `ParamAngleRepelling`, the root-portrait constants and `window_separation`;
* `RootArc`  — the flower exists at every root-parabolic parameter (`exists_rootArc`,
               `ofRootParabolic`) and the differentiability lemmas behind it;
* `Glue`     — the concrete glue of the endgame: the `Work.Top`/`Work.ParamRays` conversions,
               `hX_of_twoSided`, `hθ`, `hreal`, `hp` (`hLB` is the field `noPath` itself);
* `EL`       — the bridge from the delivered equator-curve rigidity
               (`Work.EL.equatorLeak`) to `RootArc.EquatorLeak`;
* `Main`     — `FinalInputs` and `mandelbar_not_path_connected_of_inputs`;
* `Checks`   — the axiom audit.

and the delegated lemmas of the area:

* `equatorLeak_shift` — the equator leak propagates to `Ψ (x + 1/2)` and `Ψ (x + 1)` (the
  two-sidedness of the leak);
* `ParamAngleRepelling_of_classical` — the Landing input of `hθ` from the classical Landing
  inputs;
* `FQCBridge` — the bridge to the `FQC` area: `RootArc.critHeight` *is*
  `Work.FQC.critHeightAt (EcalleData.ofFlower …)`, and the Abel equation `φa_shift` gives the
  tap-time independence of the height;
* `exists_alphaPair_pairSides` — the `α`-pair of the root portrait with its `PairSides`, i.e. the
  first block of the assembly of the ELRig input structure `Work.EL.Z1Nest` from ELTop's output;
* `FQCBridge` — the bridge to the `FQC` area: `RootArc.critHeight` *is*
  `Work.FQC.critHeightAt (EcalleData.ofFlower …)`, and `Work.FQC.PetalInput.mapsto_g` discharges
  the interface hypothesis of `RootArc.ecalleHeightAt_eq`.
-/
import Submission.Work.Final.Defs
import Submission.Work.Final.RootArc
import Submission.Work.Final.Glue
import Submission.Work.Final.EL
import Submission.Work.Final.Main
import Submission.Work.Final.equatorLeak_shift
import Submission.Work.Final.ParamAngleRepelling_of_classical
import Submission.Work.Final.FQCBridge
import Submission.Work.Final.exists_alphaPair_pairSides

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

