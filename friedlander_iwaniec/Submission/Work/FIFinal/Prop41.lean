/-
# `Submission.Work.FIFinal.Prop41` — the seven areas composed

`Work.FITop4.Prop41StatementPiBig` — Friedlander–Iwaniec's Proposition 4.1 in the `Π`-restricted
form (B\*) that the round-6 reduction produces — stated over the seven areas and **proved here**,
axiom-clean, from the pieces that are on disk:

| area | statement | witness |
|---|---|---|
| 1 | `Work.FITop4.Area1Sieve6` | `Work.FIArea1.area1s_r6` (`Submission/Work/FIFinal/Area1Bridge.lean`) |
| 2 | `Work.FITop4.Area2_6b` | `Work.FIArea2.area2_6e` |
| 3 | `Work.FITop4.Area3_6` | `Work.FIArea3.area3_6` |
| 4 | `Work.FITop4.Area4_6c` | hypothesis (`Work.FIArea4.area4_6c` is on disk) |
| 6 | `Work.FITop4.Area6_6e` | `Work.FIFinal.area6_6e` (`Submission/Work/FIFinal/Clean6.lean`) |
| τ | `Work.FITop4.TauRemoval6` | `Work.FIArea6T.tauRemoval6` |
| 7 | `Work.FITop4.Area7_6b` | `Work.FIArea7.area7_6b` |

Two of the witnesses are local, and both are *repairs* of workspace obstructions rather than new
mathematics:

* **area 1.** `Submission/Work/FITop4/Bridge/area1Sieve6.lean` (the only other producer of
  `Area1Sieve6`) does not compile: three identifiers `Work.FITop4.seqOf` are undeclared, and five
  `rw`-sites still assume the pre-round-6.3 shape of `Work.FITop4.IsBetaCoeff6` (which now carries
  the conjunct `IsAxisFree Pa z`).  `Area1Bridge.lean` is that file repaired; its imports are also
  re-pointed from the `Submission/Work/FIArea1/shim/*` copies to the `Submission/Work/FIArea1/*`
  originals, because the shims re-declare `Work.FITop3.*` and therefore clash with
  `Submission.Work.FITop3.Areas3` (which areas 2, 3 and 4 need).
* **area 6.** `Work.FIArea6V.area6_6e`'s import closure contains
  `Submission.Work.FIArea6Hecke.R.LHBHead`, which imports the *non*-clash-free
  `Submission.Work.FIArea7.card_pairs_gBox_absDelta_lt`; that module re-declares
  `Work.FIArea7.gRadius` and friends, so `Work.FIArea6V.area6_6e` and `Work.FIArea7.area7_6b` (whose
  lane `Submission.Work.FIArea7CF` is the clash-free copy) cannot be imported into one file.
  `Clean6.lean` re-proves the area-6 contract along the copy lane `Submission/Work/FIFinal/CL/`.

Consequently `prop41` and `prop41_unconditional` below are the *first* place in the workspace where
all seven areas are instantiated together.
-/
import Mathlib
import Submission.Work.FIFinal.Defs
import Submission.Work.FIFinal.Area1Bridge
import Submission.Work.FIFinal.Clean6
import Submission.Work.FIArea2.area2_6e
import Submission.Work.FIArea3.area3_6
import Submission.Work.FIArea4.area4_6c
import Submission.Work.FIArea6T.tauRemoval6
import Submission.Work.FIArea7.area7_6b
import Submission.Work.FIRed6e.prop41_of_areas6f

set_option autoImplicit false

namespace Work.FIFinal

open Finset Filter
open scoped BigOperators

noncomputable section

/-- **The composition of the seven areas**, re-exported from the proved
`Work.FIRed6e.prop41_of_areas6f` with the areas as explicit hypotheses (no clash is touched: this
statement produces nothing). -/
theorem prop41_of_areas (h1 : Work.FITop4.Area1Sieve6) (h2 : Work.FITop4.Area2_6b)
    (h3 : Work.FITop4.Area3_6) (h4 : Work.FITop4.Area4_6c) (h6 : Work.FITop4.Area6_6e)
    (hτ : Work.FITop4.TauRemoval6) (h7 : Work.FITop4.Area7_6b) :
    Work.FITop4.Prop41StatementPiBig :=
  Work.FIRed6e.prop41_of_areas6f h1 h2 h3 h4 h6 hτ h7

/-- **The deliverable of this module**: Friedlander–Iwaniec's Proposition 4.1 in the
`Π`-restricted form (B\*), from the seven areas — area 4 as the explicit hypothesis requested by
the lead, areas 1, 2, 3, 6, τ, 7 taken from disk (area 1 and area 6 through this directory's
repaired / clash-free witnesses). -/
theorem prop41 (h4 : Work.FITop4.Area4_6c) : Work.FITop4.Prop41StatementPiBig :=
  prop41_of_areas Work.FIArea1.area1s_r6 Work.FIArea2.area2_6e Work.FIArea3.area3_6 h4
    Work.FIFinal.area6_6e Work.FIArea6T.tauRemoval6 Work.FIArea7.area7_6b

/-- **Proposition 4.1' in the `Π`-restricted form, unconditionally**: `prop41` at the area-4
deliverable `Work.FIArea4.area4_6c` that is already on disk. -/
theorem prop41_unconditional : Work.FITop4.Prop41StatementPiBig :=
  prop41 Work.FIArea4.area4_6c

end

end Work.FIFinal
