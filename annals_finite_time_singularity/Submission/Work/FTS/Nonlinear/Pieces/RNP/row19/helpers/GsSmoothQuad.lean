/-
# Row 19 helpers: `D_zF_*` is `C^∞` on the open quadrant

`Gs α = D_zF_*` is the product of the angular factor `α·Γ(θ)/c(α)` and the radial profile
`prof(z) = 2z(1-z)/(1+z)³` (`Gs_eq_prof`).  Both factors are `C^∞` on the open quadrant
(`contDiffOn_Gam_Ioo`, `smoothQuad_proff`), hence so is `Gs`.

This is the smoothness input of the interior Leibniz rules `DzIter_mul_quad` /
`mixed_mul_eq_smoothQuad` for the product `V(Φ̃_*)·D_zF_*`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_Vs0_mul_Gs_eq_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

/-- `Gs α = D_zF_* = (αΓ(θ)/c)·prof(z)` is `C^∞` on the open quadrant `z > -1`, `0 < θ < π/2`. -/
theorem smoothQuad_Gs_of_pos {α : ℝ} (hα : 0 < α) :
    Work.FTS.LocData.SmoothQuad (Gs α) := by
  have hGam : Work.FTS.LocData.SmoothQuad (fun _ θ => Work.Spaces.Gam α θ) :=
    Work.FTS.LocData.smoothQuad_of_snd (Work.FTS.LocData.contDiffOn_Gam_Ioo α)
  have hprof : Work.FTS.LocData.SmoothQuad proff := smoothQuad_proff
  have h1 : Work.FTS.LocData.SmoothQuad
      (fun z θ => (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * proff z θ)) :=
    Work.FTS.LocData.smoothQuad_const_mul _
      (Work.FTS.LocData.smoothQuad_mul hGam hprof)
  refine h1.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : (-1 : ℝ) < z := hp.1
  show Gs α z θ = (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * proff z θ)
  rw [Gs_eq_prof hα hz]
  simp only [prof, proff]
  ring

end Work.FTS.Nonlinear.Pieces.RNP.row19
