import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

theorem differentiableAt_Lhat_slice {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun t => Work.FTS.CoercivityFix.Lhat f t θ) z := by
  have hz' : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ2⟩
  -- the three slices: `f`, `D_z f = D_z¹ f` and `D_θ f = D_z⁰ D_θ¹ f`
  have hf : DifferentiableAt ℝ (fun t => f t θ) z :=
    hsm.differentiableAt_slice_mixed 0 0 hz' hθ'
  have hDz : DifferentiableAt ℝ (fun t => Work.Spaces.Dz f t θ) z :=
    hsm.differentiableAt_slice_DzIter 1 hz' hθ'
  have hDth : DifferentiableAt ℝ (fun t => Work.Spaces.Dth f t θ) z :=
    hsm.differentiableAt_slice_mixed 0 1 hz' hθ'
  have hne : 1 + z ≠ 0 := by positivity
  rw [show (fun t => Work.FTS.CoercivityFix.Lhat f t θ)
      = fun t => f t θ + Work.Spaces.Dz f t θ - 2 * f t θ / (1 + t)
          - 3 * Work.Spaces.Dth f t θ / (1 + t) from
      funext fun t => Work.FTS.CoercivityFix.Lhat_eq f t θ]
  exact ((((hf.add hDz).sub (((differentiableAt_const (2:ℝ)).mul hf).div
      ((differentiableAt_const (1:ℝ)).add differentiableAt_id) hne))).sub
    (((differentiableAt_const (3:ℝ)).mul hDth).div
      ((differentiableAt_const (1:ℝ)).add differentiableAt_id) hne))

end Work.FTS.CoercivityFix.Transfer
