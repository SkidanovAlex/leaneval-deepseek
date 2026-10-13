import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- A `θ`-dependent function of `(z,θ)`, iterated by `D_θ = sin(2θ) ∂_θ`, depends only
on `θ` and its iterates agree with the one-dimensional iterates `Dth1Iter`. -/
theorem DthIter_slice (ψ : ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun z θ => ψ θ) z θ = Work.Elliptic.Dth1Iter i ψ θ := by
  induction i generalizing z θ with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ, Work.Elliptic.Dth1Iter_succ]
    have h : (fun θ' => Work.Spaces.DthIter n (fun z θ => ψ θ) z θ')
        = fun θ' => Work.Elliptic.Dth1Iter n ψ θ' := by
      funext θ'
      exact ih z θ'
    simp only [Work.Spaces.Dth, Work.Elliptic.Dth1, Work.Spaces.pth]
    rw [h]

end Work.Elliptic
