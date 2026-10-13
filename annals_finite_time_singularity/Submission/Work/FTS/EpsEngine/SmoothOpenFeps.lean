/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/SmoothOpenFeps.lean` — the right-hand side `Feps` of the projected
# `ε`-scheme is `C^∞` on the open quadrant at every profile of the engine's class

The class-invariance obligation `hkeepIter` of the local step (`EpsClass α ρ ε C₁ B` is preserved
by the Picard step `u ↦ h₀ + ∫₀^τ Feps (slice (iter F h₀ n) s) ds`) requires, among other things,
the open-quadrant smoothness of the *integrand* `Feps u` at every class profile `u`.

    `Feps α ρ ε Φs E u = Pz (J_ε (profRHS α Φs E (Pz (J_ε u))))`

is smooth in `(z,θ)` because

* the class clause of `EpsClass` gives `ClassC α (Pz (J_ε u))` (`EpsClass.classC`),
* the proved `smoothOpen_profRHS_of_classC` gives the smoothness of `profRHS α Φs E` at a
  class-`C` profile,
* the proved `Work.FTS.StrongEps.smoothOpen_Jeps` (mollification with a smooth kernel) and the
  projection `Pz` (a linear correction by the explicit smooth `bump`) preserve `SmoothOpen`.

This is the *fixed-profile* half of the smoothness story; the family version (joint smoothness of
`(s,z,θ) ↦ Feps (slice (iter F h₀ n) s) z θ`, which is what makes the parametric integral smooth)
additionally needs the (z,θ)-derivative slots of `Feps` to be bounded along the class, and is the
remaining part of the local step's analytic core (`EpsEngine/NOTES_LocalStep.md` §2).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EpsEngine.continuousOn_Feps_of_epsClass

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false

/-- **The projection `Pz` preserves `SmoothOpen`** (`Pz f = f − c•bump` with `c` a number and
`bump` smooth). -/
theorem smoothOpen_Pz_of_smoothOpen {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Pz f) := by
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Construction.L12 f 0 / pzNorm) * bump z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' _ Work.FTS.StrongEps.smoothOpen_bump
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f z θ - (Work.Construction.L12 f 0 / pzNorm) * bump z θ) :=
    Work.FTS.EllipticEst.smoothOpen_sub hf h2
  refine Work.FTS.EllipticEst.SmoothOpen.congr h3 (fun z θ _ _ _ => ?_)
  rw [Pz_apply]

/-- **`Feps` is `C^∞` on the open quadrant at every profile of the engine's class `EpsClass`.** -/
theorem smoothOpen_Feps_of_epsClass {α C₁ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℝ} {u : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hu : EpsClass α ρ ε C₁ B u) :
    Work.FTS.EllipticEst.SmoothOpen (Feps α ρ ε Φs E u) := by
  have hW : Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε u)) := hu.2.2.2.1
  have hRHS : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Pz (Jeps ρ ε u))) :=
    smoothOpen_profRHS_of_classC hα hEll hstar hW
  have hJ : Work.FTS.EllipticEst.SmoothOpen
      (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Pz (Jeps ρ ε u)))) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hRHS)
  exact smoothOpen_Pz_of_smoothOpen hJ

end Work.FTS.EpsEngine
