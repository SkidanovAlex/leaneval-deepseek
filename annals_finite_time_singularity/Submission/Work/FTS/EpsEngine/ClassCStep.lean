/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/ClassCStep.lean` — the class-`C` invariance of ONE step of the
# projected `ε`-scheme

The local step of the projected `ε`-scheme (`Work.FTS.StrongEps.EpsE4Thr.LocalStepP`) needs, at
every fake time `τ` of the flow, the class-`C` clause

    ClassC α (Pz (J_ε (slice h τ)))

of the *projected mollified* slice.  Along the Picard iteration of the engine
(`EpsEngine.exists_sol_of_engine_xball`) the slices are

    slice (epsIter g₀ (n+1)) τ = g₀ + I_n(τ),   I_n(τ) := ∫_0^τ Feps (slice (epsIter g₀ n) s) ds

(`EpsLocalPStar.iter_succ`, definitionally), so the invariance is the additivity statement

    Pz (J_ε (g₀ + I)) = Pz (J_ε g₀) + Pz (J_ε I)

together with `ClassC α (Pz (J_ε g₀))` (the datum clause, an input of the local step) and
`ClassC α (Pz (J_ε I))` (**the increment**, the genuinely new clause).  This module proves that
composition, with the increment's clause produced by `ClassCFromHonesty.classC_Pz_Jeps_of_parts`:

    ClassC α (Pz (J_ε I))  ⟸  SmoothOpen I, HkMem α 4 I, EpsMem α I,
                               ThetaUnif α 10 I,          -- the UNIFORM angular flatness
                               fsm (Pz (J_ε I))           -- all-order smoothness of the moment

The first three are metric/membership data of the increment; the angular half `TauTraces α 10` is
produced here from `ThetaUnif α 10 I` by `EpsEngine.tauTraces_Pz_Jeps_of_thetaUnif`.  **Correction
(the lead's ruling of 2026-10-12, `EpsEngine/ThetaFromEps.lean`):** the uniform clause is *not* a
residual of the chapter — `EpsMem α I` alone gives `ThetaUnif α 10 I` (indeed every order) for the
*mollified* increment, because the mollifier is a convolution in `(log z, log tan θ)` and the
Cauchy–Schwarz bound with the Jacobian keeps the factor `sin(2θ')^{γ-1}`
(`ThetaFromEps.thetaUnif_Jeps_of_epsMem`).  Hence the drop-in replacement
`ThetaFromEps.classC_step_of_epsMem` needs no uniform/flatness hypothesis at all — see
`EpsEngine/ThetaUnifPz.lean` and the `ThetaUnifFam` files for the (superseded but valid) uniform
route, and `EpsEngine/NotThetaUnif.lean` for the fact that the *pointwise* trace fields alone do not
produce `ThetaUnif`.  The single remaining input of the class-`C` invariance is therefore
`fsm (Pz (J_ε I))` — all-order smoothness on `(0,∞)` of the angular moment of the projected
mollified increment — plus the metric data.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.ThetaUnifPz
import Submission.Work.FTS.EpsEngine.ClassCFromHonesty
import Submission.Work.FTS.EpsEngine.BallLimFam
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The class-`C` invariance of one Picard step, at the level of the increment.**

If the datum's projected mollified profile is in the class `C`, and the *increment*
`I` (the fake-time integral of the scheme's right-hand side) is smooth on the open quadrant,
`ℋ⁴`-honest, `EpsMem`-honest and **uniformly** flat at both angular ends, and the angular moment of
its projected mollified image is smooth to all orders on `(0,∞)`, then the projected mollified
profile of `g₀ + I` is again in the class `C`. -/
theorem classC_Pz_Jeps_add_of_increment {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (hα1 : α ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {g₀ I : Fn}
    (hC : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g₀)))
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g₀)
    (hIsm : Work.FTS.EllipticEst.SmoothOpen I)
    (hgmem : Work.Spaces.HkMem α 4 g₀) (hImem : Work.Spaces.HkMem α 4 I)
    (hIEps : Work.FTS.StrongEps.EpsMem α I)
    (hItheta : ThetaUnif α 10 I)
    (hIfsm : ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε I)))
      (Set.Ioi 0)) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
      (fun z θ => g₀ z θ + I z θ))) := by
  -- the smoothness data in the `∀ n`-form used by the mollifier lemmas
  have hIsm' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry I)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall I).mp hIsm
  -- the increment's class-`C` clause
  have hCI : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε I)) :=
    classC_Pz_Jeps_of_parts (ρ := ρ) hρ hα hα1 hε hε1 hIsm hImem hIEps
      (tauTraces_Pz_Jeps_of_thetaUnif (ρ := ρ) hρ hα hε hIsm' hItheta) hIfsm
  have hadd : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g₀)
      + Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε I)) :=
    Work.FTS.ClassC.classC_add hC hCI
  -- the projection-additivity along the difference
  have hsum : Work.FTS.EllipticEst.SmoothOpen (fun z θ => g₀ z θ + I z θ) := hgsm.add hIsm
  have hmemSum : Work.Spaces.HkMem α 4 (fun z θ => g₀ z θ + I z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hgsm hIsm hgmem hImem
  have hsub := Work.FTS.EpsEngine.Pz_Jeps_sub_eq (α := α) (ρ := ρ) (ε := ε)
    (u := fun z θ => g₀ z θ + I z θ) (v := g₀) hρ hα hε hsum hgsm hmemSum hgmem
  have hfun : (fun z θ : ℝ => (g₀ z θ + I z θ) - g₀ z θ) = I := by
    funext z θ; ring
  rw [hfun] at hsub
  -- conclude by rearranging
  have hgoal : Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => g₀ z θ + I z θ))
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g₀)
        + Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε I) := by
    rw [hsub]; abel
  rw [hgoal]
  exact hadd

end Work.FTS.EpsEngine
