import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

/-- Every iterate `D_θ^a f` of a function `f z θ = g θ` independent of `z` stays
independent of `z`. -/
theorem DthIter_angular_z_indep_aux (a : ℕ) (g : ℝ → ℝ) (z z' θ : ℝ) :
    Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ
      = Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z' θ := by
  induction a generalizing z z' θ with
  | zero => rfl
  | succ n ih =>
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    congr 1
    congr 1
    funext θ'
    exact ih z z' θ'

theorem DthIter_angular_z_indep (a : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) z θ
      = Work.Spaces.DthIter a (fun _ θ : ℝ => g θ) 0 θ :=
  DthIter_angular_z_indep_aux a g z 0 θ

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
