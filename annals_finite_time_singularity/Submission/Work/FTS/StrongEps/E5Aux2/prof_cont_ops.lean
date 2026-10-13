/-
# `prof_cont_ops` — continuity of the coefficient operators `Rop`, `Uop`, `Vop`

The self-similar vorticity equation of §Modulation of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), 1--70,

is a transport equation whose coefficients are the three operators

  `U(Ψ) = -3Ψ - α z ∂_zΨ`,   `V(Ψ) = ∂_θΨ - tan θ · Ψ`,
  `ℛ(Ψ) = (2 sin θ · Ψ + α sin θ · z ∂_zΨ + cos θ · ∂_θΨ)/cos θ`

(`Work.Construction.Uop`, `Vop`, `Rop`).  The fake-time / fixed-point argument of the paper
(the modulation chapter, tex lines 1549--1578) evaluates these coefficients along a sequence
of approximate stream functions `Φ_n`, and needs them to be *jointly continuous* on the open
quadrant `Q0 = (0,∞) × (0,π/2)` as soon as `Φ_n` is `C¹` there — that is what this module
records.

The point is that `ContDiffOn ℝ 1 (uncurry Ψ) Q0` alone already makes the two partials
`∂_zΨ`, `∂_θΨ` continuous on `Q0`: on the *open* quadrant the Fréchet derivative equals the
`fderivWithin`, so `ContDiffOn.fderivWithin` at order `1` gives order `0` (= continuity) of
`fderiv ℝ (uncurry Ψ)`, and `Work.Spaces.pz_eq_fderiv` / `pth_eq_fderiv` identify the
slicewise derivatives `Work.Spaces.pz Ψ`, `Work.Spaces.pth Ψ` with the two partial
directional derivatives of that Fréchet derivative.  This is the order-one instance of the
general shift lemmas `contDiffOn_pz_of` / `contDiffOn_pth_of` of
`Work.FTS.EllipticEst.remov.AeNj.boxContFts`; it is reproved here so that the present module
depends on nothing beyond the definitions of the three operators.

The angular factors are continuous on `Q0` because `cos θ > 0` there: this covers `tan θ`
(as `Real.continuousOn_tan` restricted to `{cos ≠ 0} ⊇ Q0`) and the division by `cos θ` in
`ℛ`.  Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-- **`∂_z` of a `C¹` datum is continuous.**  On an open set `V`, the slicewise `z`-partial
`Work.Spaces.pz G` is continuous as soon as `G` is jointly `C¹` on `V`. -/
theorem continuousOn_uncurry_pz_of_contDiffOn_one {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry G) V) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz G p.1 p.2) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (0 : WithTop ℕ∞)) hV.uniqueDiffOn (by norm_num)
    exact h'.congr (fun p hp => (fderivWithin_of_isOpen hV hp).symm)
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    (hfd.clm_apply contDiffOn_const).continuousOn
  exact hcomp.congr (fun p hp => Work.Spaces.pz_eq_fderiv (hdiff p hp))

/-- **`∂_θ` of a `C¹` datum is continuous.**  On an open set `V`, the slicewise `θ`-partial
`Work.Spaces.pth G` is continuous as soon as `G` is jointly `C¹` on `V`. -/
theorem continuousOn_uncurry_pth_of_contDiffOn_one {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry G) V) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth G p.1 p.2) V := by
  have hdiff : ∀ p ∈ V, DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (0 : WithTop ℕ∞)) hV.uniqueDiffOn (by norm_num)
    exact h'.congr (fun p hp => (fderivWithin_of_isOpen hV hp).symm)
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    (hfd.clm_apply contDiffOn_const).continuousOn
  exact hcomp.congr (fun p hp => Work.Spaces.pth_eq_fderiv (hdiff p hp))

/-- The angular factor `cos θ` does not vanish on the open quadrant. -/
theorem cos_ne_zero_of_mem_Q0 :
    ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
  intro p hp
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)

/-- `tan θ` is continuous on the open quadrant. -/
theorem continuousOn_tan_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
  have h := Real.continuousOn_tan.comp continuousOn_snd
    (fun p hp => cos_ne_zero_of_mem_Q0 p hp)
  simpa only [Function.comp_def] using h

theorem prof_cont_ops {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 1 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (Work.Construction.Rop α Ψ)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Construction.Uop α Ψ)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Construction.Vop Ψ)) Work.FTS.EllipticEst.Q0 := by
  have hV : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hΨc : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hΨ.continuousOn
  have hpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_uncurry_pz_of_contDiffOn_one hV hΨ
  have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_uncurry_pth_of_contDiffOn_one hV hΨ
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    Real.continuous_sin.comp_continuousOn continuousOn_snd
  have hcos : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    Real.continuous_cos.comp_continuousOn continuousOn_snd
  have htan : ContinuousOn (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 :=
    continuousOn_tan_Q0
  refine ⟨?_, ?_, ?_⟩
  · -- `ℛ(Ψ) = (2 sin θ · Ψ + α sin θ · z ∂_zΨ + cos θ · ∂_θΨ)/cos θ`
    show ContinuousOn (fun p : ℝ × ℝ => (2 * Real.sin p.2 * Ψ p.1 p.2
        + α * Real.sin p.2 * p.1 * Work.Spaces.pz Ψ p.1 p.2
        + Real.cos p.2 * Work.Spaces.pth Ψ p.1 p.2) / Real.cos p.2)
        Work.FTS.EllipticEst.Q0
    refine ContinuousOn.div ?_ hcos cos_ne_zero_of_mem_Q0
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · exact ContinuousOn.mul (ContinuousOn.mul continuousOn_const hsin) hΨc
    · exact ContinuousOn.mul
        (ContinuousOn.mul (ContinuousOn.mul continuousOn_const hsin) continuousOn_fst) hpz
    · exact ContinuousOn.mul hcos hpth
  · -- `U(Ψ) = -3Ψ - α z ∂_zΨ`
    show ContinuousOn (fun p : ℝ × ℝ =>
        -3 * Ψ p.1 p.2 - α * p.1 * Work.Spaces.pz Ψ p.1 p.2) Work.FTS.EllipticEst.Q0
    refine ContinuousOn.sub (ContinuousOn.mul continuousOn_const hΨc) ?_
    exact ContinuousOn.mul (ContinuousOn.mul continuousOn_const continuousOn_fst) hpz
  · -- `V(Ψ) = ∂_θΨ - tan θ · Ψ`
    show ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth Ψ p.1 p.2 - Real.tan p.2 * Ψ p.1 p.2) Work.FTS.EllipticEst.Q0
    exact ContinuousOn.sub hpth (ContinuousOn.mul htan hΨc)

end Work.FTS.StrongEps.E5Aux2
