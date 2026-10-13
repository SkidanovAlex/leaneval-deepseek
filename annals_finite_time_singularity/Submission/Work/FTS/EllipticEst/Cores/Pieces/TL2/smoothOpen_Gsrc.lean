/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TL2.smoothOpen_Gsrc`: the angular source `Gsrc α G Φ` is `C^∞` on the open quadrant

The top-slot machinery at level `2` (`Cores/Pieces/TL2/sliceTopCore_twoD`,
`Cores/Pieces/TopSlotRhsDom`) differentiates the *angular source*

  `Gsrc α G Φ = G + α²z²∂_zzΦ + α(5+α)z∂_zΦ`

(`Work.FTS.EllipticEst.Mine.Gsrc`) in `θ`; for that one needs to know that it is `C^∞` on the
open quadrant `Q0 = (0,∞) × (0,π/2)`, which is what this module provides.

The point is that the weak hypothesis class `TT.EllWeakPos α k G Φ` does **not** ask for `G` to
be smooth; it only asks for the *equation* `bslOp α Φ = G` on `Q0`, for `Φ` smooth on `Q0` and
for the honesty (`HkMem`) of the two sides.  On `Q0`, however, the equation determines `G`
completely, and substituting it into `Gsrc` cancels the two radially differentiated terms:

  `Gsrc α G Φ = bslOp α Φ + α²z²∂_zzΦ + α(5+α)z∂_zΦ = Lzero Φ`  on `Q0`,

so the angular source agrees on the open quadrant with the `C^∞` function `Lzero Φ` (the
`α = 0` part of `bslOp`).  `SmoothOpen` only constrains `Q0`, so
`Cert.smoothOpen_congr_bsl` finishes the job.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Pieces.TL2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **`Lzero` preserves `C^∞` on the open quadrant.**

`Lzero Φ = -∂_θθΦ + ∂_θ(tan θ·Φ) - 6Φ` is built from `Φ`, its second `θ`-derivative and the
function `∂_θ(tan θ·Φ)`, together with the constant factor `6`; all of these are `C^∞` on `Q0`
whenever `Φ` is (`tan` is smooth there because `cos θ ≠ 0` for `0 < θ < π/2`). -/
theorem smoothOpen_Lzero_of_smoothOpen {Φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Φ) := by
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have htΦ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Φ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΦ
  -- `-∂_θθΦ + ∂_θ(tan θ·Φ) - 6Φ`, with the angular operators written as plain `∂_θ`-iterates
  have hcomp : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Spaces.pthIter 2 Φ z θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * Φ z θ) z θ - 6 * Φ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΦ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl htΦ 1))
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hΦ)
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl hcomp
    (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])

/-- **The angular source `Gsrc α G Φ` is `C^∞` on the open quadrant** for every datum of the
weak hypothesis class `EllWeakPos α k G Φ`.

Indeed, on the open quadrant `Q0` the elliptic law `bslOp α Φ = G` (component `1` of
`EllWeakPos`) determines `G`, and substituting it into `Gsrc` turns the source into the
`α = 0` part of the operator:

  `Gsrc α G Φ = G + α²z²∂_zzΦ + α(5+α)z∂_zΦ = bslOp α Φ + α²z²∂_zzΦ + α(5+α)z∂_zΦ = Lzero Φ`,

which is `C^∞` on `Q0` by `smoothOpen_Lzero_of_smoothOpen` (the smoothness of `Φ` on `Q0` is
component `6` of `EllWeakPos`).  `SmoothOpen` is a statement about `Q0` only, so the
congruence `Cert.smoothOpen_congr_bsl` transports the smoothness from `Lzero Φ` to
`Gsrc α G Φ`. -/
theorem smoothOpen_Gsrc {α : ℝ} {k : ℕ} {G Φ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k G Φ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Mine.Gsrc α G Φ) := by
  -- `Φ` is `C^∞` on the open quadrant, hence so is `Lzero Φ`
  have hΦ : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hL : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Φ) :=
    smoothOpen_Lzero_of_smoothOpen hΦ
  -- on `Q0` the source agrees with `Lzero Φ`
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl hL (fun z θ hz hθ0 hθ1 => ?_)
  have heq : Work.Elliptic.bslOp α Φ z θ = G z θ := h.eq z hz θ hθ0 hθ1
  simp only [Work.Elliptic.bslOp_apply, Work.FTS.EllipticEst.Mine.Gsrc] at heq ⊢
  rw [← heq]
  ring

end Work.FTS.EllipticEst.Cores.Pieces.TL2
