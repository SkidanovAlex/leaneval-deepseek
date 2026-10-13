/-
# `Work.FTS.EllSol.ropBasic` — elementary facts for the `ℛ`-transfer on `EllClassO`

Small, dependency-light facts used by the assembly of `Work.FTS.EllSol.RopTransfer`:
the smoothness of `Ξ/sin 2θ` and of `ℛ(Ξ)` on the open quadrant, the vanishing of the residual
on the two angular boundary lines, the algebraic identity `Ξ = ellShift - Ḡ·sin 2θ`, and the two
smoothness-closure facts (`SmoothOpen_add`, `SmoothOpen_mul_sin_sq`) needed for the bounded
angular profiles.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- `sin 2θ` does not vanish on the open quadrant. -/
theorem sin_two_ne_zero_of_mem_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Real.sin (2 * p.2) ≠ 0 := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-- Sums of functions `C^∞` on the open quadrant are `C^∞` on the open quadrant. -/
theorem SmoothOpen_add_local {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h1 : Function.uncurry (fun z θ => f z θ + g z θ)
      = (Function.uncurry f) + (Function.uncurry g) := by funext p; rfl
  rw [h1]
  exact (Work.FTS.EllipticEst.SmoothOpen.forall hf n).add
    (Work.FTS.EllipticEst.SmoothOpen.forall hg n)

/-- Multiplication of a function `C^∞` on the open quadrant by the bounded smooth angular profile
`sin²θ` keeps it `C^∞` there. -/
theorem SmoothOpen_mul_sin_sq_local {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => Real.sin θ ^ 2 * f z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => Real.sin θ ^ 2 * f z θ)
      = fun p : ℝ × ℝ => Real.sin p.2 ^ 2 * f p.1 p.2 from rfl]
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_snd (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).sin).pow 2
  exact h1.mul hf

/-- The quotient of a function `C^∞` on the open quadrant by the non-vanishing smooth factor
`sin 2θ` is again `C^∞` on the open quadrant. -/
theorem smoothOpen_div_sin_local {Ξ : ℝ → ℝ → ℝ} (hΞ : Work.FTS.EllipticEst.SmoothOpen Ξ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Ξ z θ / Real.sin (2 * θ)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have huncurry : Function.uncurry (fun z θ => Ξ z θ / Real.sin (2 * θ))
      = fun p : ℝ × ℝ => Function.uncurry Ξ p / Real.sin (2 * p.2) := rfl
  rw [huncurry]
  have hnum : ContDiffOn ℝ n (Function.uncurry Ξ) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall hΞ n
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (2 : ℝ) * p.2) Work.FTS.EllipticEst.Q0 := by
      fun_prop
    exact h1.sin
  exact ContDiffOn.div hnum hden fun p hp => sin_two_ne_zero_of_mem_Q0 hp

/-- `ℛ(Ξ) = (2 sin θ·Ξ + α sin θ·z ∂_zΞ + cos θ·∂_θΞ)/cos θ` is `C^∞` on the open quadrant as
soon as `Ξ` is (the only apparent singularity `1/cos θ` is harmless there). -/
theorem smoothOpen_Rop_local {α : ℝ} {Ξ : ℝ → ℝ → ℝ}
    (hΞ : Work.FTS.EllipticEst.SmoothOpen Ξ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Rop α Ξ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hΞ ⊢
  have hun : Function.uncurry (Work.FTS.EllipticEst.Rop α Ξ)
      = (fun p : ℝ × ℝ => (2 * Real.sin p.2 * Ξ p.1 p.2
            + α * Real.sin p.2 * p.1 * Work.Spaces.pz Ξ p.1 p.2
            + Real.cos p.2 * Work.Spaces.pth Ξ p.1 p.2) / Real.cos p.2) := by
    funext p
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry, Work.FTS.EllipticEst.Rop]
  rw [hun]
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin p.2)
      Work.FTS.EllipticEst.Q0 := (contDiffOn_snd (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).sin
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos p.2)
      Work.FTS.EllipticEst.Q0 := (contDiffOn_snd (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).cos
  have hz : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 := contDiffOn_fst
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Spaces.pz Ξ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have h := Work.FTS.EllipticEst.SmoothOpen.pz (F := Ξ) hΞ
    rwa [Work.FTS.EllipticEst.SmoothOpen] at h
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Spaces.pth Ξ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have h := Work.FTS.EllipticEst.SmoothOpen.pth (F := Ξ) hΞ
    rwa [Work.FTS.EllipticEst.SmoothOpen] at h
  refine ContDiffOn.div ?_ hcos ?_
  · have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (Real.sin p.2 * Ξ p.1 p.2)) Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (2 : ℝ)) (s := Work.FTS.EllipticEst.Q0)).mul (hsin.mul hΞ)
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => α * (Real.sin p.2 * (p.1 * Work.Spaces.pz Ξ p.1 p.2)))
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := α)).mul (hsin.mul (hz.mul hpz))
    have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.cos p.2 * Work.Spaces.pth Ξ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := hcos.mul hpth
    refine ((h1.add h2).add h3).congr ?_
    intro p _
    ring
  · intro p hp
    have hθ := (Work.FTS.EllipticEst.mem_Q0.mp hp).2
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩)

/-- **`Ξ` vanishes identically on the two angular boundary lines** (it agrees there with `Ψ`,
which carries the Dirichlet data of the class). -/
theorem vanishTheta_EllResid {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.Spaces.VanishTheta (Work.Elliptic.EllResid α g Ψ) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [Work.Elliptic.EllResid]
    simp [h.sol.2.1 z]
  · rw [Work.Elliptic.EllResid]
    simp only [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
    simp [h.sol.2.2.1 z]

/-- **`Ξ = ellShift - Ḡ·sin 2θ`**: the exact algebraic identity relating the residual of
Theorem `RemovingL12` to the straightened unknown `V = ellShift α g Ψ = Ψ + Gsing α g·sin 2θ`
and the lower singular term `Ḡ = Gbar α g`. -/
theorem EllResid_eq_ellShift_sub_Gbar_point (α : ℝ) (g Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.EllResid α g Ψ z θ
      = (Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ))
        - Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
  rw [Work.Elliptic.EllResid, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
  ring

end Work.FTS.EllSol
