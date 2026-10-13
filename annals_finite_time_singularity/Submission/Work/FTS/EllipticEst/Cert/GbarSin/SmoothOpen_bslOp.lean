/-
Copyright: work module for the Elgindi finite-time singularity project.

# `bslOp` preserves `C^∞`-smoothness on the open quadrant

The elliptic estimates of §'Elliptic Regularity Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

are stated for a source `F` that is `C^∞` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`).  The source produced by the
elliptic law `bslOp α Ψ = F` is smooth there as soon as `Ψ` is smooth on a neighbourhood of
the closed quadrant.

The point of this lemma is that `SmoothNbhd` — which in this Mathlib is *analyticity* on the
open box `(-1,∞) × (-1, π/2+1)` (the order `⊤ : ℕ∞ω` is `ω`, not `∞`) — is enough: every
building block of

`L(Ψ) = -α²z²∂_zzΨ - α(5+α)z∂_zΨ + L₀(Ψ)`,
`L₀(Ψ) = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`

is `C^∞` (in the genuine smooth order `Work.Stability.smoothOrder = ∞`) on the open quadrant.
The `tan` in the `L₀`-term is harmless because `Q0` has `θ ∈ (0,π/2)`, where `cos θ ≠ 0`; the
statement `SmoothNbhd (bslOp α Ψ)` is *false* in general, precisely because `Real.tan` is
totalised at `θ = π/2` (cf. `Submission/Work/FTS/EllipticEst/Cert/FstarSmooth/Defs.lean`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.GbarSin

open scoped Real
open Work.FTS.EllipticEst (Q0)

/-- **`bslOp` is `C^∞` on the open quadrant**: if `Ψ` is smooth (indeed analytic) on a
neighbourhood of the closed quadrant, then the source `Work.Elliptic.bslOp α Ψ` belongs to
`Work.FTS.EllipticEst.SmoothOpen`, i.e. its uncurried form is `C^∞` on
`Q0 = (0,∞) × (0,π/2)` in the genuine smooth order `Work.Stability.smoothOrder`. -/
theorem SmoothOpen_bslOp (α : ℝ) {Ψ : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (Work.Elliptic.bslOp α Ψ)) Work.FTS.EllipticEst.Q0
  -- `Q0` sits inside the analyticity box of `SmoothNbhd`
  have hsub : Work.FTS.EllipticEst.Q0 ⊆
      Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
    intro p hp
    simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩
  -- analyticity on the box downgrades to smoothness on the quadrant
  have hQ0 : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
      Work.FTS.EllipticEst.Q0 := (h.of_le le_top).mono hsub
  -- the radial partials of `Ψ`
  have hpz1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pz Work.FTS.EllipticEst.isOpen_Q0 hQ0
  have hpz2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Work.FTS.EllipticEst.Q0 := by
    have hh := Work.FTS.LocData.contDiffOn_pz Work.FTS.EllipticEst.isOpen_Q0 hpz1
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hh
  -- the angular partials of `Ψ`
  have hpth1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pth Work.FTS.EllipticEst.isOpen_Q0 hQ0
  have hpth2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Work.FTS.EllipticEst.Q0 := by
    have hh := Work.FTS.LocData.contDiffOn_pth Work.FTS.EllipticEst.isOpen_Q0 hpth1
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hh
  -- `tan θ` is smooth on the quadrant (where `cos θ ≠ 0`)
  have htan : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin (n := Work.Stability.smoothOrder)).contDiffOn.comp
        (contDiffOn_snd (s := Work.FTS.EllipticEst.Q0)) (fun p _ => Set.mem_univ _)
    have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_cos (n := Work.Stability.smoothOrder)).contDiffOn.comp
        (contDiffOn_snd (s := Work.FTS.EllipticEst.Q0)) (fun p _ => Set.mem_univ _)
    have hdiv := hsin.div hcos (fun p hp => by
      simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hp.2.1, Real.pi_pos], by linarith [hp.2.2]⟩))
    exact hdiv.congr (fun p _ => Real.tan_eq_sin_div_cos p.2)
  -- the `L₀`-term `∂_θ(tan θ · Ψ)`
  have htanPsi : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => Real.tan θ * Ψ z θ)) Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun z θ => Real.tan θ * Ψ z θ)
        = fun p : ℝ × ℝ => Real.tan p.2 * Function.uncurry Ψ p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact htan.mul hQ0
  have hpthTanPsi : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pth Work.FTS.EllipticEst.isOpen_Q0 htanPsi
  -- the polynomial coefficients `-α²z²`, `-α(5+α)z` and the constant `6`
  have hcoef1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2)) Work.FTS.EllipticEst.Q0 := by
    have hh : ContDiff ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => α ^ 2 * p.1 ^ 2) :=
      (contDiff_const (c := α ^ 2)).mul ((contDiff_fst (E := ℝ) (F := ℝ)).pow 2)
    exact hh.neg.contDiffOn
  have hcoef2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * (5 + α) * p.1) Work.FTS.EllipticEst.Q0 :=
    ((contDiff_const (c := α * (5 + α))).mul (contDiff_fst (E := ℝ) (F := ℝ))).contDiffOn
  have h6 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 6 * Function.uncurry Ψ p) Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := (6 : ℝ)) : ContDiffOn ℝ _
      (fun _ : ℝ × ℝ => (6 : ℝ)) Work.FTS.EllipticEst.Q0).mul hQ0)
  -- assemble the four summands of `L(Ψ)`
  have hmain : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ =>
        -(α ^ 2 * p.1 ^ 2) * Function.uncurry (Work.Spaces.pzIter 2 Ψ) p
        - (α * (5 + α) * p.1) * Function.uncurry (Work.Spaces.pz Ψ) p
        + (-(Function.uncurry (Work.Spaces.pthIter 2 Ψ) p)
           + Function.uncurry (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) p
           - 6 * Function.uncurry Ψ p)) Work.FTS.EllipticEst.Q0 :=
    ((hcoef1.mul hpz2).sub (hcoef2.mul hpz1)).add
      (((hpth2.neg).add hpthTanPsi).sub h6)
  -- it is definitionally the uncurried `bslOp`
  refine hmain.congr (fun p _ => ?_)
  simp only [Work.Elliptic.bslOp, Work.Elliptic.Lzero, Function.uncurry]

end Work.FTS.EllipticEst.Cert.GbarSin
