import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

/-- The `θ`-variable is a dummy for a function of `z` alone: every `D_z`-iterate of
`fun z _ => Φ z` is independent of `θ`.

`D_z = z ∂_z` and its iterates see only the `z`-variable, so applying `D_z^b` to a function
which does not depend on `θ` again produces a function which does not depend on `θ`.  The
proof is the immediate induction on `b`: at each step `deriv` is applied to the slice
`fun z' => DzIter b (fun z _ => Φ z) z' θ`, which by the induction hypothesis is independent
of `θ`. -/
theorem DzIter_zonly_theta_indep (Φ : ℝ → ℝ) (b : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter b (fun z _ : ℝ => Φ z) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => Φ z) z θ' := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [show (fun z' => Work.Spaces.DzIter b (fun z _ : ℝ => Φ z) z' θ)
          = (fun z' => Work.Spaces.DzIter b (fun z _ : ℝ => Φ z) z' θ') from
        funext fun z' => ih z']

theorem DzIter_radial_theta_indep (b : ℕ) (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => f z) z 0 :=
  DzIter_zonly_theta_indep f b z θ 0

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
