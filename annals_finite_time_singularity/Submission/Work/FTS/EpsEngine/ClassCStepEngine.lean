/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/ClassCStepEngine.lean` — one Picard step of the projected
# `ε`-scheme preserves the class `C`

This module assembles the two pieces proved in `ClassCStep.lean` and `ThetaUnifFam.lean` into the
*engine-facing* form of the class-`C` invariance: along the Picard iteration

    slice (epsIter g₀ (n+1)) τ = g₀ + epsInc n τ
    epsInc n τ   :=  (z,θ) ↦ ∫_0^τ Feps (slice (epsIter g₀ n) s) z θ ds

(`EpsLocalPStar.iter_succ`, by `rfl`), the projected mollified profile of the `(n+1)`-st iterate is
again in the class `C`, from

* the datum's class-`C` clause `ClassC α (Pz (J_ε g₀))`,
* the **family-uniform angular flatness** of the right-hand side along the `n`-th curve
  (`ThetaUnifFam α 10 δ (fun s => Feps … (slice (epsIter g₀ n) s))`), which is the single analytic
  residual of the chapter, and
* the metric data of the increment (`SmoothOpen`, `HkMem α 4`, `EpsMem`) together with the
  all-order smoothness `fsm` of its angular moment.

The flatness of the *increment* is produced here (not assumed): it is the interval-integral leg
`thetaUnifFam_intervalIntegral` applied to the right-hand side curve, with the three exchange gates
of `PerzTools.mixed_intervalIntegral_eq_gen_restricted`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.ClassCStep
import Submission.Work.FTS.EpsEngine.ThetaUnifFam
import Submission.Work.FTS.EpsEngine.LimSmoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The increment of one Picard step of the projected `ε`-scheme**:
`epsInc n τ = ∫_0^τ Feps (slice (epsIter g₀ n) s) ds`. -/
noncomputable def epsInc (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (n : ℕ) (τ : ℝ) : Fn :=
  fun z θ => ∫ s in (0 : ℝ)..τ, Feps α ρ ε Φs E (slice (epsIter α ρ ε Φs E g₀ n) s) z θ

/-- **The Picard step is the datum plus the increment** (definitional). -/
theorem slice_epsIter_succ_eq (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g₀ : Fn) (n : ℕ) (τ : ℝ) :
    slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ
      = fun z θ => g₀ z θ + epsInc α ρ ε Φs E g₀ n τ z θ := rfl

/-- **One Picard step preserves the class `C`.**

The single analytic residual is the *family-uniform* angular flatness `hflat` of the scheme's
right-hand side along the `n`-th Picard curve; everything else is either produced here (the
flatness of the increment, by `thetaUnifFam_intervalIntegral`) or is metric data of the increment.
The gates `hsmF`/`hmeasF`/`hsupF` are the three hypotheses of the exchange identity (smoothness of
the curve, a.e.-strong measurability of its slots in `s`, uniform slot bounds on compacta). -/
theorem classC_step_of_flat {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {δ τ : ℝ} {n : ℕ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hα1 : α ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g₀)))
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g₀) (hgmem : Work.Spaces.HkMem α 4 g₀)
    (hδ : 0 ≤ δ) (hτ0 : 0 ≤ τ) (hτδ : τ ≤ δ)
    (hflat : ThetaUnifFam α 10 δ
      (fun s => Feps α ρ ε Φs E (slice (epsIter α ρ ε Φs E g₀ n) s)))
    (hsmF : ∀ s ∈ Set.Icc (0 : ℝ) δ, ∀ m : ℕ,
      ContDiffOn ℝ m (Function.uncurry (Feps α ρ ε Φs E (slice (epsIter α ρ ε Φs E g₀ n) s)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmeasF : ∀ (j i : ℕ), j + i ≤ 10 → ∀ z θ : ℝ,
      (z, θ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.mixed j i
          (Feps α ρ ε Φs E (slice (epsIter α ρ ε Φs E g₀ n) s)) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) δ)))
    (hsupF : ∀ (j i : ℕ), j + i ≤ 10 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) δ, ∀ q ∈ K,
        |Work.Spaces.mixed j i (Feps α ρ ε Φs E (slice (epsIter α ρ ε Φs E g₀ n) s)) q.1 q.2| ≤ C)
    (hIsm : Work.FTS.EllipticEst.SmoothOpen (epsInc α ρ ε Φs E g₀ n τ))
    (hImem : Work.Spaces.HkMem α 4 (epsInc α ρ ε Φs E g₀ n τ))
    (hIEps : Work.FTS.StrongEps.EpsMem α (epsInc α ρ ε Φs E g₀ n τ))
    (hIfsm : ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (epsInc α ρ ε Φs E g₀ n τ)))) (Set.Ioi 0)) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
      (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))) := by
  have htheta : ThetaUnif α 10 (epsInc α ρ ε Φs E g₀ n τ) :=
    thetaUnifFam_intervalIntegral (α := α) (T := δ) (k := 10) (a := (0 : ℝ)) (b := τ)
      (H := fun s => Feps α ρ ε Φs E (slice (epsIter α ρ ε Φs E g₀ n) s))
      hδ ⟨le_refl 0, hδ⟩ ⟨hτ0, hτδ⟩ hτ0 hflat hsmF hmeasF hsupF
  rw [slice_epsIter_succ_eq]
  exact classC_Pz_Jeps_add_of_increment hρ hα hα1 hε hε1 hC₀ hgsm hIsm hgmem hImem hIEps
    htheta hIfsm

end Work.FTS.EpsEngine
