/-
Copyright: subproject `Submission/Work/LANDCL/` of `mandelbar_not_path_connected`.

# `repAngle` : the window ray `R(23/63)` lands at a repelling periodic point

Row `repAngle` of the delivery table: `Work.Final.ParamAngleRepelling c` at the root-arc
parameter, i.e. the dynamic ray `R_c(23/63)` lands at a repelling periodic point of `T_c`.

The assembly follows `Work.Final.ParamAngleRepelling.of_landing`:

1. `hper : Work.Landing.PeriodicRaysLand c` produces a landing point `z` of `R_c(23/63)` — via
   `Work.LANDCL.exists_landsAt_paramAngle`; the classical source is the hyperbolic contraction
   (`Work.LANDCL.HyperbolicContraction`, see
   `Work.LANDCL.periodicRaysLand_of_hyperbolicContraction`), Douady–Hubbard/Milnor 18.10;
2. `hdich : Work.Landing.EvenPeriodLandingDichotomy c` (Milnor 18.10 for the even period `6`
   together with the Snail lemma) makes `z` repelling unless it is parabolic;
3. non-parabolicity of `z`: the parabolic cycle at the root-parabolic parameter is the
   *exact* period-`5` cycle of the characteristic point (`Work.LANDCL.OnlyParabolicIsCycleOf`),
   while `R_c(23/63)` lands at a point of period dividing `6`, and `6 ∤ 10` —
   `Work.LANDCL.not_isParabolic_of_landsAt_paramAngle`. -/
import Submission.Work.LANDCL.Defs
import Submission.Work.LANDCL.GM
import Submission.Work.LANDCL.ParamAngle.exists_landsAt_paramAngle
import Submission.Work.LANDCL.ParamAngle.periodicRaysLand_of_hyperbolicContraction
import Submission.Work.LANDCL.ParamAngle.paramAngleRepelling_of_classical
import Submission.Work.LANDCL.ParamAngle.paramAngleRepelling_of_rootParabolic
import Submission.Work.LANDCL.ParamAngle.not_isParabolic_of_landsAt_paramAngle
import Submission.Work.LANDCL.ParamAngle.evenPeriodLandingDichotomy_of_snail
import Submission.Work.LANDCL.ParamAngle.onlyParabolicIsCycleOf_of_critOrbit
import Submission.Work.Final.RootArc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LANDCL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **`repAngle` from the Carathéodory/hyperbolic route.**  If the inverse Böttcher coordinate
extends to the closed exterior of the unit disk (`Work.LANDCL.HyperbolicContraction`, the
Douady–Hubbard contraction input), then the window ray lands at a repelling periodic point,
provided the even-period landing dichotomy and the non-parabolicity of the landing point. -/
theorem paramAngleRepelling_of_hyperbolicContraction {c : ℂ}
    (h : HyperbolicContraction c) (hdich : Work.Landing.EvenPeriodLandingDichotomy c)
    (hpar : ∀ (m : ℕ) (z : ℂ), Work.Landing.IsParabolic c m z →
      ¬ Work.Landing.landsAt c Work.Landing.paramAngle z) :
    Work.Final.ParamAngleRepelling c :=
  ParamAngle.paramAngleRepelling_of_classical
    (ParamAngle.periodicRaysLand_of_hyperbolicContraction h) hdich hpar

/-- **`repAngle` at the root-parabolic parameter**, in its final form: from the landing input,
the even-period dichotomy and the uniqueness of the parabolic cycle, the window ray lands at a
repelling periodic point. -/
theorem paramAngleRepelling_of_rootParabolic' {c : ℂ} (d : Work.EL.RootParabolic c)
    (hper : Work.Landing.PeriodicRaysLand c)
    (hdich : Work.Landing.EvenPeriodLandingDichotomy c)
    (huniq : OnlyParabolicIsCycleOf c d.z₁) :
    Work.Final.ParamAngleRepelling c :=
  ParamAngle.paramAngleRepelling_of_rootParabolic d hper hdich huniq

/-- The same, for the `RootArc` data of `Submission/Work/Final/Defs.lean`. -/
theorem paramAngleRepelling_of_rootArc {c : ℂ} (A : Work.Final.RootArc c)
    (hper : Work.Landing.PeriodicRaysLand c)
    (hdich : Work.Landing.EvenPeriodLandingDichotomy c)
    (huniq : OnlyParabolicIsCycleOf c A.d.z₁) :
    Work.Final.ParamAngleRepelling c :=
  ParamAngle.paramAngleRepelling_of_rootParabolic A.d hper hdich huniq

/-- The `hθ` clause at the root-parabolic parameter, assembled from `repAngle` and `gm`. -/
theorem notMem_closure_paramRay_windowAngle_of_rootArc (hgm : Work.FSeed.RepellingRayParamStable)
    {c : ℂ} (A : Work.Final.RootArc c) (hper : Work.Landing.PeriodicRaysLand c)
    (hdich : Work.Landing.EvenPeriodLandingDichotomy c)
    (huniq : OnlyParabolicIsCycleOf c A.d.z₁) :
    c ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) :=
  notMem_closure_paramRay_windowAngle hgm
    (paramAngleRepelling_of_rootArc A hper hdich huniq)

/-- The uniqueness of the parabolic cycle implies the weaker `Work.Landing.OnlyParabolicIsPeriodK`:
at the root-parabolic parameter every parabolic point is fixed by the fifth iterate. -/
theorem onlyParabolicIsPeriodK_of_cycleOf {c z₁ : ℂ} (h : OnlyParabolicIsCycleOf c z₁) :
    Work.Landing.OnlyParabolicIsPeriodK c 5 := by
  rintro z ⟨m, hmpar⟩
  obtain ⟨j, _hj, rfl⟩ := h.2.2 z ⟨m, hmpar⟩
  rw [← Function.iterate_add_apply (Tantibar c) 5 j, show 5 + j = j + 5 from by omega,
    Function.iterate_add_apply (Tantibar c) j 5, h.1]

/-- **`repAngle` from the hyperbolic route, in the final assembled form**: the root-arc data,
the Carathéodory/hyperbolic input, the even-period landing dichotomy and the uniqueness of the
parabolic cycle give `Work.Final.ParamAngleRepelling c`. -/
theorem paramAngleRepelling_of_rootArc_hyperbolic {c : ℂ} (A : Work.Final.RootArc c)
    (h : HyperbolicContraction c) (hdich : Work.Landing.EvenPeriodLandingDichotomy c)
    (huniq : OnlyParabolicIsCycleOf c A.d.z₁) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc A
    (ParamAngle.periodicRaysLand_of_hyperbolicContraction h) hdich huniq

/-- **`repAngle` from the Snail lemma.**  The even-period landing dichotomy is *derived* from the
Snail lemma input (`Work.LANDCL.SnailDichotomy`) and the geometric input of Milnor 18.10
(`Work.Landing.AttractingCyclesInner`), so `repAngle` rests only on the primitive landing inputs. -/
theorem paramAngleRepelling_of_rootArc_snail {c : ℂ} (A : Work.Final.RootArc c)
    (hcontr : HyperbolicContraction c) (hsnail : SnailDichotomy)
    (hgeo : Work.Landing.AttractingCyclesInner c) (huniq : OnlyParabolicIsCycleOf c A.d.z₁) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc A
    (ParamAngle.periodicRaysLand_of_hyperbolicContraction hcontr)
    (ParamAngle.evenPeriodLandingDichotomy_of_snail hsnail hgeo) huniq

/-- The uniqueness of the parabolic cycle at the root-parabolic parameter, from Fatou's theorem
(`Work.LANDCL.ParabolicCycleInOmegaLimit`) and the critical-orbit convergence of the
root-parabolic data. -/
theorem onlyParabolicIsCycleOf_of_rootParabolic {c : ℂ} (d : Work.EL.RootParabolic c)
    (h : ParabolicCycleInOmegaLimit c) : OnlyParabolicIsCycleOf c d.z₁ :=
  ParamAngle.onlyParabolicIsCycleOf_of_critOrbit h d.per_half
    (d.ne_per 1 (by simp [Finset.mem_Ioo])) d.crit.1

/-- **`repAngle` in the fully assembled primitive form**: the root-arc data, the Carathéodory
contraction input, the Snail lemma, Milnor 18.10's geometric input and Fatou's theorem on
parabolic cycles. -/
theorem paramAngleRepelling_of_rootArc_omegaLimit {c : ℂ} (A : Work.Final.RootArc c)
    (hcontr : HyperbolicContraction c) (hsnail : SnailDichotomy)
    (hgeo : Work.Landing.AttractingCyclesInner c) (homega : ParabolicCycleInOmegaLimit c) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc_snail A hcontr hsnail hgeo
    (onlyParabolicIsCycleOf_of_rootParabolic A.d homega)

end Work.LANDCL
