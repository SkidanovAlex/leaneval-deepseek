/-
# `Work.MandelFinal.Main` — the final assembly of the mandelbar theorem

Area `Submission/Work/MandelFinal/` (requested by the lead of `mandelbar_not_path_connected`).

**The deliverable** is `Work.MandelFinal.finalInputs_of`: given

* the **root-arc data** `root : Work.FinalFix.RootArcHeightZero` (a parameter `c₀` of the
  mandelbar with root-arc data of critical Écalle height `0` — the *only* input that is not
  produced in this area; see `Submission/Work/MandelFinal/NOTES.md` §2 for the exact missing
  input, `Work.SeedExist.FatouCritInBasin`, and §3 for why it must be an opaque argument);
* `hP : Work.PARIMPL2.Lavaurs.LavaursInputs d P fl nIn` — the **current export of the area
  PARIMPL2** (chain C), at the root-parabolic data `d` of that arc and at a caller-chosen
  `ParNormal` / flower / tap time;
* `hG : Work.GATE.TwoSided (c₀Of root) P.Nm` — the **current export of the area GATE2** (its
  conclusion `Work.GATE.TwoSided`, *definitionally* the `twoSided` field of `FinalInputs`);
* `hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate` — the degenerate (multi-petal)
  half of Fatou's theorem on parabolic cycles, the one classical input of the assembly that has no
  producer on disk (its simple half is the theorem
  `Work.FatouParabolic2.fatouParabolicInput_simple`; see `NOTES.md` §1(c)),

it produces a full `Work.Final.FinalInputs`, hence

`Work.Final.mandelbar_not_path_connected_of_inputs (finalInputs_of …) : ¬ IsPathConnected Mandelbar`.

Everything else is discharged here or in `Classical.lean`: `Nm`, `impl` and `noPath` come from
`hP` (`Work.PARIMPL2.Lavaurs.implSide`, `Work.PARIMPL2.Lavaurs.noPath_of_inputs`), `twoSided` from
`hG`, and `nakane`, `gm`, `repAngle`, `repAngle_quarter` from the delivered areas
(`NAKANE2`/`NAKANE`, `LandLeaves`, `FatouParabolic2`; the auxiliary input
`Work.Landing.RotationNumberZero (1/4) 1` of the `1/4`-row is discharged by the *proved*
`Work.MandelFinal.rotationNumberZero_quarter`).

`finalInputs_of_landing` is the variant in which `hDeg` is replaced by its two *weaker*
consequences, the ledger's own items `Work.LANDCL.ParabolicCycleInOmegaLimit (c₀Of root)` and
`Work.LANDCL.QuarterParabolicIsFixed`.

## Coherence

All the fields are stated at `Work.FinalFix.c₀Of root` and `Work.FinalFix.arcOf root`, the
parameter and the root-arc data read off the given `root`; the implosion side is `P.Nm`, the very
set that `noPath` and `twoSided` refer to, so the three fields `impl`, `noPath`, `twoSided` are
*simultaneously* satisfied.  No hypothesis of `finalInputs_of` mentions any other parameter.
-/
import Submission.Work.MandelFinal.Classical
import Submission.Work.MandelFinal.rotationNumberZero_quarter
import Submission.Work.Final.Main
import Submission.Work.PARIMPL2.Lavaurs.Inputs
import Submission.Work.PARIMPL2.Lavaurs.ImplSide
import Submission.Work.PARIMPL.Bridge
import Submission.Work.PARIMPL.exists_parNormal
import Submission.Work.PARIMPL.exists_flowerFix
import Submission.Work.GATE.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.MandelFinal

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **THE FINAL ASSEMBLY.**  `Work.Final.FinalInputs` from the two live areas' exports (PARIMPL2's
`LavaursInputs`, GATE2's `TwoSided`) at the root arc, plus the degenerate half of Fatou's theorem.

See the module docstring for the hypothesis list and `NOTES.md` for the field-by-field
provenance. -/
noncomputable def finalInputs_of
    (root : Work.FinalFix.RootArcHeightZero)
    {P : Work.PARIMPL.ParNormal (Work.FinalFix.arcOf root).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft (Work.FinalFix.c₀Of root))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of root)) (Work.FinalFix.arcOf root).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs (Work.FinalFix.arcOf root).d P fl nIn)
    (hG : Work.GATE.TwoSided (Work.FinalFix.c₀Of root) P.Nm)
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) :
    Work.Final.FinalInputs where
  root := root
  Nm := P.Nm
  impl := (Work.PARIMPL2.Lavaurs.implSide P).toFinal
  noPath := Work.PARIMPL2.Lavaurs.noPath_of_inputs (Work.FinalFix.arcOf root).d P fl nIn hP
  twoSided := hG
  nakane := nakaneInput
  gm := repellingRayParamStable
  repAngle := paramAngleRepelling hDeg (Work.FinalFix.arcOf root)
  repAngle_quarter := paramAngleRepelling_quarter hDeg

/-- **The endgame, wired**: the two live exports plus the degenerate half of Fatou's theorem give
`¬ IsPathConnected Mandelbar` (through `Work.TopJordan`'s endgame, via `Work.Final`). -/
theorem mandelbar_not_path_connected_of
    (root : Work.FinalFix.RootArcHeightZero)
    {P : Work.PARIMPL.ParNormal (Work.FinalFix.arcOf root).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft (Work.FinalFix.c₀Of root))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of root)) (Work.FinalFix.arcOf root).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs (Work.FinalFix.arcOf root).d P fl nIn)
    (hG : Work.GATE.TwoSided (Work.FinalFix.c₀Of root) P.Nm)
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) :
    ¬ IsPathConnected Mandelbar :=
  Work.Final.mandelbar_not_path_connected_of_inputs (finalInputs_of root hP hG hDeg)

/-- **The final assembly with the two *Landing-level* classical inputs instead of the degenerate
Fatou input.**  These are the ledger's own items (`NOTES_LEAD_mandelbar_ledger.md` §5) and they are
*weaker* than `Work.FatouParabolic2.FatouParabolicInput_degenerate` (which implies both of them via
`Work.FatouParabolic2.parabolicCycleInOmegaLimit_of_degenerate` /
`quarterParabolicIsFixed_of_degenerate`); a caller who has either of them separately — for instance
from the *simple* case of Fatou plus `Work.FatouParabolic2.ParabolicCyclesSimple` — can use this
entry point instead. -/
noncomputable def finalInputs_of_landing
    (root : Work.FinalFix.RootArcHeightZero)
    {P : Work.PARIMPL.ParNormal (Work.FinalFix.arcOf root).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft (Work.FinalFix.c₀Of root))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of root)) (Work.FinalFix.arcOf root).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs (Work.FinalFix.arcOf root).d P fl nIn)
    (hG : Work.GATE.TwoSided (Work.FinalFix.c₀Of root) P.Nm)
    (hOmega : Work.LANDCL.ParabolicCycleInOmegaLimit (Work.FinalFix.c₀Of root))
    (hFixq : Work.LANDCL.QuarterParabolicIsFixed) :
    Work.Final.FinalInputs where
  root := root
  Nm := P.Nm
  impl := (Work.PARIMPL2.Lavaurs.implSide P).toFinal
  noPath := Work.PARIMPL2.Lavaurs.noPath_of_inputs (Work.FinalFix.arcOf root).d P fl nIn hP
  twoSided := hG
  nakane := nakaneInput
  gm := repellingRayParamStable
  repAngle := Work.LandLeaves.paramAngleRepelling_of_rootArc_final (Work.FinalFix.arcOf root)
    (Work.FinalFix.arcOf root).mem_Mandelbar hOmega
  repAngle_quarter := Work.LandLeaves.paramAngleRepelling_quarter_final Work.ParamRays.quarter_mem
    hFixq rotationNumberZero_quarter

/-- The endgame, wire-complete, with the two Landing-level classical inputs. -/
theorem mandelbar_not_path_connected_of_landing
    (root : Work.FinalFix.RootArcHeightZero)
    {P : Work.PARIMPL.ParNormal (Work.FinalFix.arcOf root).d}
    {fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft (Work.FinalFix.c₀Of root))
      (Work.PARIMPL.gtc (Work.FinalFix.c₀Of root)) (Work.FinalFix.arcOf root).d.z₁}
    {nIn : ℕ}
    (hP : Work.PARIMPL2.Lavaurs.LavaursInputs (Work.FinalFix.arcOf root).d P fl nIn)
    (hG : Work.GATE.TwoSided (Work.FinalFix.c₀Of root) P.Nm)
    (hOmega : Work.LANDCL.ParabolicCycleInOmegaLimit (Work.FinalFix.c₀Of root))
    (hFixq : Work.LANDCL.QuarterParabolicIsFixed) :
    ¬ IsPathConnected Mandelbar :=
  Work.Final.mandelbar_not_path_connected_of_inputs
    (finalInputs_of_landing root hP hG hOmega hFixq)

/-! ## Non-vacuity of the structure arguments -/

/-- **Non-vacuity of the `ParNormal` argument**: at the root arc of `finalInputs_of` the parameter
normal form exists (`Work.PARIMPL.exists_parNormal`, HS Proposition 4.1). -/
theorem exists_parNormal_arc (root : Work.FinalFix.RootArcHeightZero) :
    Nonempty (Work.PARIMPL.ParNormal (Work.FinalFix.arcOf root).d) :=
  Work.PARIMPL.exists_parNormal _

/-- **Non-vacuity of the flower argument**: at the root arc of `finalInputs_of` a
`Work.FatouCoordFix.ParabolicFlowerFix` (with its `Work.PARIMPL.FlowerFix`) exists
(`Work.PARIMPL.exists_flowerFix`). -/
theorem exists_flowerFix_arc (root : Work.FinalFix.RootArcHeightZero) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft (Work.FinalFix.c₀Of root))
        (Work.PARIMPL.gtc (Work.FinalFix.c₀Of root)) (Work.FinalFix.arcOf root).d.z₁,
      Nonempty (Work.PARIMPL.FlowerFix (Work.FinalFix.arcOf root).d
        (Work.PARIMPL.Ft (Work.FinalFix.c₀Of root)) (Work.PARIMPL.gtc (Work.FinalFix.c₀Of root))
        (Work.FinalFix.arcOf root).d.z₁ fl.Pa fl.φa) :=
  Work.PARIMPL.exists_flowerFix _

/-- The parameter of the root arc lies in the mandelbar. -/
theorem mem_Mandelbar_of_root (root : Work.FinalFix.RootArcHeightZero) :
    Work.FinalFix.c₀Of root ∈ Mandelbar :=
  (Work.FinalFix.arcOf root).mem_Mandelbar

/-! ## Coherence of the root accessors

`Work.FinalFix.RootArcHeightZero` is a `Prop`, so all its elements are equal by proof irrelevance
and the accessors `c₀Of`, `arcOf` are therefore **constant**: the parameter and the root-arc data of
the assembly do not depend on *which* witness of the existential is supplied.  This is why the
hypotheses of `finalInputs_of` can be stated at `c₀Of root` / `arcOf root` without any loss: every
caller who can produce a `RootArcHeightZero` at all gets the same parameter. -/

theorem c₀Of_eq_of (h1 h2 : Work.FinalFix.RootArcHeightZero) :
    Work.FinalFix.c₀Of h1 = Work.FinalFix.c₀Of h2 := by
  rw [Subsingleton.elim h1 h2]

theorem arcOf_z₁_eq_of (h1 h2 : Work.FinalFix.RootArcHeightZero) :
    (Work.FinalFix.arcOf h1).d.z₁ = (Work.FinalFix.arcOf h2).d.z₁ := by
  rw [Subsingleton.elim h1 h2]

theorem arcOf_critHeight_eq_of (h1 h2 : Work.FinalFix.RootArcHeightZero) :
    (Work.FinalFix.arcOf h1).critHeight = (Work.FinalFix.arcOf h2).critHeight := by
  rw [Subsingleton.elim h1 h2]

end Work.MandelFinal
