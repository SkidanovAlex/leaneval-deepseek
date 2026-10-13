import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Local vocabulary of the `∂_θ U`-transfer estimate (`ThetaU`)

This small module collects the definitions shared by the pieces of the proof of

  `Work.FTS.EllipticEst.ThetaU.pthU_EllResid_le`:

`| -3 ∂_θW - α z ∂_θ∂_zW |_{ℋ^k} ≤ C ( |F|_{ℋ^k} + |∂_θ∂_θW|_{ℋ^k} + α² |z²∂_zzΨ|_{ℋ^k} )`

for `W = EllResid α F Ψ` and elliptic data `EllHyp α k F Ψ`.  Nothing else lives here, so that
the pieces can import it without importing each other.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

/-- **The smoothness class of the transfer estimates.**  `G` is `C^n` for every `n` on the
product of the open half-line `(0,∞)` in `z` with an open neighbourhood of the closed angular
interval `[0,π/2]`.

This is deliberately *weaker* than `Work.Spaces.SmoothNbhd`, which asks for `ContDiffOn ℝ ⊤` on
`Ioi (-1) ×ˢ Ioo (-1) (π/2+1)`; in this Mathlib `⊤ : ℕ∞` is analyticity, so `SmoothNbhd` forces
analyticity in `z` down to `z = -1`, which the residual `Ψ + G_{\rm star}(z) sin 2θ` cannot
satisfy (`G_{\rm star} = -(1/(4α))L₁₂(F)` is only known to be smooth on `(0,∞)`).  The
`θ`-slices of the residual *are* analytic (a constant in `θ` times `sin 2θ` plus the analytic
`Ψ`), which is what the slice estimates need. -/
def SmoothOpenθ (G : ℝ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))

theorem SmoothOpenθ.mono {G : ℝ → ℝ → ℝ} (h : SmoothOpenθ G) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := h n

/-- The uncurried form of a `SmoothOpenθ` function is `C^n` at every point of
`(0,∞) × (-1, π/2+1)`. -/
theorem SmoothOpenθ.contDiffAt {G : ℝ → ℝ → ℝ} (h : SmoothOpenθ G) (n : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    ContDiffAt ℝ n (Function.uncurry G) (z, θ) :=
  (h n).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθ⟩)

/-- Each `θ`-slice of a `SmoothOpenθ` function is differentiable at every interior angle. -/
theorem SmoothOpenθ.differentiableAt_slice {G : ℝ → ℝ → ℝ} (h : SmoothOpenθ G) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    DifferentiableAt ℝ (fun θ' : ℝ => G z θ') θ :=
  ((h.contDiffAt 2 hz hθ).comp θ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
    (by norm_num)

/-- The two iterated slice derivatives of a `SmoothOpenθ` function agree: Clairaut. -/
theorem SmoothOpenθ.pz_pth_comm {G : ℝ → ℝ → ℝ} (h : SmoothOpenθ G) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.pz (Work.Spaces.pth G) z θ = Work.Spaces.pth (Work.Spaces.pz G) z θ :=
  Work.Spaces.pz_pth_comm (h.contDiffAt 2 hz hθ)

/-- Clairaut for `D_z∂_θ`: `D_z (∂_θG) = z · ∂_θ∂_zG` on the open quadrant. -/
theorem SmoothOpenθ.Dz_pth_eq {G : ℝ → ℝ → ℝ} (h : SmoothOpenθ G) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.Dz (Work.Spaces.pth G) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz G) z θ := by
  simp only [Work.Spaces.Dz]
  rw [h.pz_pth_comm hz hθ]

end Work.FTS.EllipticEst.ThetaU
