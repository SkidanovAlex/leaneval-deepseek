/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/XBallLimAux/FstarPzJepsSmooth.lean`

**`F_*(Pz (J_ε W))` is smooth to all orders on `(0,∞)`** — the `fsm` residual of the class-`C`
clause — from `SmoothOpen W` and `HkMem α 1 W`.

This is a copy of `Work.FTS.StrongEps.EpsE4Thr.FstarPzJepsSmooth` in which the input
`EpsE4Thr.FstarJepsSmooth` (whose cone still contains the `sorry`-stub
`FstarJepsSmoothAux.ThShiftPreimageNull`) is replaced by the `sorry`-free
`XBallLimAux.FstarJepsSmooth`.  The declaration name is
`Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.FstarPzJepsSmooth`; it is the `fsm` input of the class-`C`
clause of the limit slice in `Submission/Work/FTS/StrongEps/EpsE4Thr/XBallLimExists.lean`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.FstarJepsSmooth
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsMulSinCos2Integrable
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallLimAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  change Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- **`F_*(Pz (J_ε W))` is smooth to all orders on `(0,∞)`** — the `fsm` residual of the class-`C`
clause, from the `ℋ¹`-honesty of `W`. -/
theorem FstarPzJepsSmooth {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {W : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε W)))
      (Set.Ioi 0) := by
  intro m
  -- the mollified angular moment
  have hA : ContDiffOn ℝ m (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W)) (Set.Ioi 0) :=
    FstarJepsSmooth hρ hε hsm hmem m
  -- the angular constant of the bump and the `z`-cut-off
  have hconst : ContDiffOn ℝ m (fun _ : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ) (Set.Ioi 0) :=
    contDiff_const.contDiffOn
  have hB : ContDiffOn ℝ m (fun r : ℝ => Work.FTS.StrongEps.zCut r *
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ))
      (Set.Ioi 0) :=
    (Work.FTS.StrongEps.contDiff_zCut m).contDiffOn.mul hconst
  -- the scalar of the projection
  set c : ℝ := Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε W) 0 / Work.FTS.StrongEps.pzNorm
    with hc
  have hBc : ContDiffOn ℝ m (fun r : ℝ => c * (Work.FTS.StrongEps.zCut r *
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ)))
      (Set.Ioi 0) := (contDiffOn_const (c := c)).mul hB
  refine (hA.sub hBc).congr ?_
  intro r hr
  have hf : IntegrableOn (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε W r θ *
      Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    JepsMulSinCos2Integrable hρ hε hα hsm hmem r hr
  have hcont : Continuous (fun θ : ℝ => Work.FTS.StrongEps.zCut r *
      (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ)) :=
    continuous_const.mul ((Work.FTS.StrongEps.contDiff_thCut 0).continuous.mul continuous_sinCos2)
  have hb : IntegrableOn (fun θ : ℝ => c * (Work.FTS.StrongEps.zCut r *
      (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ))) Work.Spaces.Iθ :=
    (hcont.continuousOn.integrableOn_compact isCompact_Icc).const_mul c
  have hkey : ∀ θ : ℝ, Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε W) r θ *
        Work.Elliptic.sinCos2 θ
      = Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ
        - c * (Work.FTS.StrongEps.zCut r *
            (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ)) := by
    intro θ
    rw [Work.FTS.StrongEps.Pz_apply]
    simp only [Work.FTS.StrongEps.bump, hc]
    ring
  have hii : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε W) r θ *
        Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ
          - c * (Work.FTS.StrongEps.zCut r *
              (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ))) :=
    integral_congr_ae (Filter.Eventually.of_forall hkey)
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, hii, MeasureTheory.integral_sub hf hb,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end Work.FTS.StrongEps.EpsE4Thr.XBallLimAux
