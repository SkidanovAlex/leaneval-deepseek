/-
# `Work.FinalFix.RootExport` — FQC's export of the root-arc parameter, and the derived `nonreal`

Area `Submission/Work/FinalFix/` of the mandelbar project.

`NOTES_LEAD_mandelbar_residuals.md` §4 assigns the three fields `c₀`, `arc`, `critHeight_zero`
of the final holder structure to one single *export of the `FQC` area*:

```lean
∃ c₀ : ℂ, ∃ A : Work.Final.RootArc c₀, A.critHeight = 0
```

(`FSeed.exists_rootParabolic_at` + `FQC.heightShift` + the root-parabolic transport along the
quasiconformal conjugacy `principal μ`; the restated `PetalInput` on `Pg` of §3.1).  This module

* names that export (`RootArcHeightZero`) and exposes its components (`c₀Of`, `arcOf`,
  `critHeight_arcOf`, `mem_Mandelbar_c₀Of`, `per_half_arcOf`);
* **derives `nonreal`** at the exported parameter: `(c₀Of h).im ≠ 0`
  (`nonreal_c₀Of`, from `Work.FinalFix.nonreal` and the root-parabolic structure alone — no
  portrait, no ray-count bound, see `Nonreal.lean`).

`Work.Final.FinalInputs` (in `Submission/Work/Final/Main.lean`) is stated on top of this module,
so its root data is *exactly* FQC's export and its `nonreal` field is *derived*, not assumed.
-/
import Submission.Work.Final.Defs
import Submission.Work.FinalFix.Nonreal

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

namespace Work.FinalFix

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **FQC's export** (`NOTES_LEAD_mandelbar_residuals.md` §4, row `c₀`/`arc`/`critHeight_zero`):
a parameter of the mandelbar carrying root-arc data whose critical Écalle height vanishes. -/
def RootArcHeightZero : Prop := ∃ c : ℂ, ∃ A : Work.Final.RootArc c, A.critHeight = 0

/-- The parameter of FQC's export. -/
noncomputable def c₀Of (h : RootArcHeightZero) : ℂ := Classical.choose h

/-- The root-arc data of FQC's export, at the chosen parameter. -/
noncomputable def arcOf (h : RootArcHeightZero) : Work.Final.RootArc (c₀Of h) :=
  Classical.choose (Classical.choose_spec h)

/-- The critical Écalle height of FQC's export vanishes — the exported data *is* height-`0`
data. -/
theorem critHeight_arcOf (h : RootArcHeightZero) : (arcOf h).critHeight = 0 :=
  Classical.choose_spec (Classical.choose_spec h)

/-- The exported parameter belongs to the connectedness locus. -/
theorem mem_Mandelbar_c₀Of (h : RootArcHeightZero) : c₀Of h ∈ Mandelbar :=
  (arcOf h).mem_Mandelbar

/-- **`nonreal`, derived from FQC's export.**  The root-parabolic structure of the exported arc
is uninhabitable at real parameters (`Work.FinalFix.nonreal`), so the exported parameter is
non-real: this is the `nonreal` field of `Work.Final.FinalInputs`, no longer an assumption. -/
theorem nonreal_c₀Of (h : RootArcHeightZero) : (c₀Of h).im ≠ 0 :=
  nonreal (arcOf h).d

/-- **The equator leak at FQC's exported parameter.**  This is the *input* of the PARIMPL and
GATE derivations of the fields `noPath` and `twoSided` (§1.4 and §2.1 of
`NOTES_LEAD_mandelbar_residuals.md`); it is **not** a field of `Work.Final.FinalInputs`
(§4: "make `leak` an input of PARIMPL/GATE"), so it is named here for those two areas. -/
abbrev EquatorLeakAt (h : RootArcHeightZero) : Prop := (arcOf h).EquatorLeak

theorem equatorLeakAt_iff (h : RootArcHeightZero) :
    EquatorLeakAt h ↔ ∃ x : ℝ, (arcOf h).fl.Ψ (x : ℂ) ∉ Work.EL.K (c₀Of h) := Iff.rfl

/-- The characteristic parabolic point of the exported arc is fixed by `(T_c)^5`. -/
theorem per_half_arcOf (h : RootArcHeightZero) :
    (Tantibar (c₀Of h))^[5] (arcOf h).d.z₁ = (arcOf h).d.z₁ :=
  (arcOf h).per_half

end Work.FinalFix
