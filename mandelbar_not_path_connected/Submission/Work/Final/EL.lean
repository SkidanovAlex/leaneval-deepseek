/-
# The bridge from the equator-curve rigidity to `RootArc.EquatorLeak`

Area `Submission/Work/Final/`.  The equator leak

  `RootArc.EquatorLeak A`  ⟺  `∃ x : ℝ, A.fl.Ψ (x : ℂ) ∉ Work.EL.K c`

is the output of the **EL** area `Work.ELRig` (the equator-curve rigidity, HS Lemma 5.5 replaced
by the rigidity argument of `NOTES_LEAD_mandelbar_EL.md` §2).  The delivered statement is

```lean
Work.EL.equatorLeak (hJ : Work.Top.JordanForm) (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (L : Work.ELRig.RayLift d fl)
    (tr : Work.EL.B2Data d.hN d.z₁) : ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ Work.EL.K c
```

with the Jordan curve theorem discharged by `Work.TopJordan.jordanForm`.  This module records the
bridge, so that the field `FinalInputs.leak` can be produced from the delivered ELRig chain
instead of being assumed.

The *residual* inputs of `equatorLeak` (the parts of the EL chain that are still open) are the
three sibling structures:

* `nest : Work.EL.Z1Nest …` — the nest at the parabolic point (ELNest N1–N4 and the side
  preservation `SP`; ELPull's `L`-wake);
* `L : Work.ELRig.RayLift …` — the lift data of the two root rays (R-a2).  All of its fields are
  produced by ELRig itself *except* `strand : Work.ELRig.RayStrand`, the curve-free statement
  "the two rays project to simple closed curves in the Écalle cylinder" (see
  `Submission/Work/ELRig/NOTES.md` §6);
* `tr : Work.EL.B2Data …` — the tripod at `b₂`, the certificate `C7` and the nest at `b₂`
  (ELNest N3–N5, ELPull P5/P6, ELTop T8).

## Main result

* `Work.Final.equatorLeak_of_ELRig` — `RootArc.EquatorLeak` from the refined ELRig inputs;
* `Work.Final.equatorLeak_contra_of_ELRig` — the contradiction form.
-/
import Submission.Work.Final.RootArc
import Submission.Work.ELRig.EquatorLeak

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

namespace Work.Final

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The equator leak, from the delivered equator-curve rigidity.** -/
theorem equatorLeak_of_ELRig {c : ℂ} (A : RootArc c)
    (nest : Work.EL.Z1Nest A.d.hN A.d.z₁ A.fl.Pa)
    (L : Work.ELRig.RayLift A.d A.fl)
    (tr : Work.EL.B2Data A.d.hN A.d.z₁) : A.EquatorLeak :=
  Work.EL.equatorLeak Work.TopJordan.jordanForm A.d A.fl nest L tr

/-- **The equator leak, in the contradiction-free form**: an explicit equator point outside the
filled Julia set. -/
theorem exists_equator_notMem_K_of_ELRig {c : ℂ} (A : RootArc c)
    (nest : Work.EL.Z1Nest A.d.hN A.d.z₁ A.fl.Pa)
    (L : Work.ELRig.RayLift A.d A.fl)
    (tr : Work.EL.B2Data A.d.hN A.d.z₁) :
    ∃ x : ℝ, A.fl.Ψ (x : ℂ) ∉ Work.EL.K c :=
  equatorLeak_of_ELRig A nest L tr

end Work.Final

namespace Work.Final

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The residuals of the EL chain.**  The delivered `Work.EL.equatorLeak` produces
`RootArc.EquatorLeak` from exactly these three structures; this bundle names them so that
`FinalInputs` can be stated as "the EL area's output" plus this one datum.

* `nest` — the nest at the parabolic point `z₁` (ELNest N1–N4, `SP`; ELPull's `L`-wake);
* `L` — the lift data of the two root rays (R-a2), whose only genuinely open field is
  `Work.ELRig.RayStrand` (`Submission/Work/ELRig/NOTES.md` §6);
* `tr` — the tripod at `b₂` and the certificate `C7` (ELNest N3–N5, ELPull P5/P6, ELTop T8). -/
structure ELResiduals {c : ℂ} (A : RootArc c) where
  /-- the nest at the parabolic point. -/
  nest : Work.EL.Z1Nest A.d.hN A.d.z₁ A.fl.Pa
  /-- the lift data of the two root rays. -/
  L : Work.ELRig.RayLift A.d A.fl
  /-- the tripod data at the branch point `b₂`. -/
  tr : Work.EL.B2Data A.d.hN A.d.z₁

namespace ELResiduals

variable {c : ℂ} {A : RootArc c}

/-- The equator leak from the residuals of the EL chain. -/
theorem equatorLeak (h : ELResiduals A) : A.EquatorLeak :=
  equatorLeak_of_ELRig A h.nest h.L h.tr

end ELResiduals

end Work.Final
