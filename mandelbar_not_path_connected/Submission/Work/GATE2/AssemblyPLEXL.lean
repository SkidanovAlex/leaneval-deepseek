/-
# GATE2 — the headline drive: `twoSided` from PARIMPL + PL + EXL + the floored UT

This is the endgame of residual 2 (TRANSPORT).  `Work.GATE2.twoSided_of_PARIMPL_exitPath`
(`Submission/Work/GATE2/Bridge.lean`) reduces `Work.GATE.TwoSided c₀ P.Nm` — *definitionally* the
`twoSided` field of `Work.Final.FinalInputs` — to PARIMPL's own data
(`ParNormal`/`MatchData`/`TransitData`/`LeakData`), the four flower facts of the implosion side, and
the **exit-path datum** `Work.GATE2.ExitPathData` for the `b`- and the `ι b`-tongue.  D1
(`Work.GATE2.D1.exitPath_of_tongue`, `…_iota`) constructs that datum from the two static `c₀`
statements PL and EXL plus UT with the caller-prescribed floor:

```
twoSided_of_PARIMPL_exitPath
  ├─ D1.exitPath_of_tongue       (α₁, bTongue, leak centre L.xstar − L.j₀)
  └─ D1.exitPath_of_tongue_iota  (α₂, iotaTongue, leak centre L.xstar − L.j₀ + 1/2)
       ← PL (PrincipalParam), EXL (ExitLoop with the loop confinement K₀),
         UT (TransitLockstepAbove at Xb = PL.X + 1)
```

Residuals 1 (ACCESS) and 3 (the shifted `trans_escape`) are **not** hypotheses: they are proved in
this area, and the two escape fields of GATE's `TransitData` come from PARIMPL's own
`LeakData.escape` (stated for both leak lattices).  The tube / `BranchData` phrasing of residual 2
is uninhabitable (`Work.GATE2.no_baseWindow_of_tube_subset_critDomain`), which is why the residual
is stated as the exit-path datum / the phase identity.

**The complete hypothesis list** (all named objects, no GATE-specific residual):

* `fl`, `FF` — the `c₀`-flower and the `FatouCoord` fix (`Work.PARIMPL.exists_flowerFix`);
* `P`, `M`, `T`, `L` — PARIMPL's normal form, MATCH, TRANS and LEAK data;
* `hOpen`, `hfront` — `P.Nm` open and accumulating at `c₀`;
* `hPaeq : Pa = fl.Pa`, `hφa_eq`, `hΨeq` — the identification of PARIMPL's coordinates with the
  flower's;
* `hentry₀`, `hcrit` — the entry point lies in `Pa` and the critical Écalle height vanishes;
* `hPL` — PL (`PrincipalParam`), the principal Fatou parametrisation of the `c₀`-flower;
* `hEXL₁`, `hEXL₂` — EXL (`ExitLoop`, with the loop confinement) at the two leak centres;
* `hUT` — UT with the caller-prescribed floor `Xb = hPL.X + 1`.
-/
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.Relay
import Submission.Work.GATE2.Bridge
import Submission.Work.GATE2.D1.exitPath_of_tongue
import Submission.Work.GATE2.D1.exitPath_of_tongue_iota

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The `twoSided` field of `Work.Final.FinalInputs` from PARIMPL, PL, EXL and the floored UT.**
See the module docstring for the hypothesis list; residuals 1 and 3 are not among the hypotheses. -/
theorem twoSided_of_PARIMPL_PL_EXL {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hPL : Work.GATE2.PrincipalParamFlower c₀ FF.Pg fl.φa
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (hEXL₁ : Work.GATE2.ExitLoop c₀ fl.Ψ (L.xstar - (L.j₀ : ℝ)) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha1)
    (hEXL₂ : Work.GATE2.ExitLoop c₀ fl.Ψ ((L.xstar - (L.j₀ : ℝ)) + 1 / 2) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha2)
    (hUT : Work.GATE2.TransitLockstepAbove c₀ P.Nm (Work.PARIMPL.transU P M.nIn) M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ (hPL.X + 1)
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ))) :
    Work.GATE.TwoSided c₀ P.Nm :=
  twoSided_of_PARIMPL_exitPath (c₀ := c₀) (d := d) (P := P) (M := M) (T := T) (L := L)
    hOpen hfront
    (by rw [hPaeq]; exact fl.isOpen_Pa)
    (by rw [hφa_eq, hPaeq]; exact fl.φa_fatou.1.2.1)
    hentry₀ hcrit
    (D1.exitPath_of_tongue FF hPaeq hφa_eq hΨeq hcrit hPL hEXL₁ hUT)
    (D1.exitPath_of_tongue_iota FF hPaeq hφa_eq hΨeq hcrit hPL hEXL₂ hUT)

end Work.GATE2
