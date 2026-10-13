import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-- A `SmoothSlice` function stays smooth under every iterate of `D_θ = sin(2θ) ∂_θ`
on the interval `Iθ = (-1, π/2 + 1)`: the derivative of a `C^∞` function is again
`C^∞` on an open set, and multiplication by `sin(2θ)` preserves that. -/
private theorem Dth1Iter_contDiffOn_of_smoothSlice (n : ℕ) {f : ℝ → ℝ}
    (hf : Work.Elliptic.SmoothSlice f) :
    ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1Iter n f) (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
  induction n with
  | zero => simpa [Work.Elliptic.Dth1Iter, Work.Elliptic.SmoothSlice] using hf
  | succ n ih =>
    have hd : ContDiffOn ℝ ⊤ (deriv (Work.Elliptic.Dth1Iter n f))
        (Set.Ioo (-1) (Real.pi / 2 + 1)) := ih.deriv_of_isOpen isOpen_Ioo le_top
    simp only [Work.Elliptic.Dth1Iter_succ]
    unfold Work.Elliptic.Dth1
    fun_prop

theorem Dth1Iter_add_of_smooth (m : ℕ) {F G : ℝ → ℝ}
    (hF : Work.Elliptic.SmoothSlice F) (hG : Work.Elliptic.SmoothSlice G)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    Work.Elliptic.Dth1Iter m (fun θ => F θ + G θ) θ
      = Work.Elliptic.Dth1Iter m F θ + Work.Elliptic.Dth1Iter m G θ := by
  -- `Dth1Iter n` is additive on the open interval `Iθ`, where all smoothness holds.
  have key : ∀ n : ℕ, ∀ θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1),
      Work.Elliptic.Dth1Iter n (fun θ => F θ + G θ) θ
        = Work.Elliptic.Dth1Iter n F θ + Work.Elliptic.Dth1Iter n G θ := by
    intro n
    induction n with
    | zero => intro θ hθ; simp [Work.Elliptic.Dth1Iter]
    | succ n ih =>
      intro θ hθ
      -- both pieces are differentiable at `θ`, so `deriv` splits over the sum
      have hdiffF : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter n F) θ :=
        ((Dth1Iter_contDiffOn_of_smoothSlice n hF).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hdiffG : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter n G) θ :=
        ((Dth1Iter_contDiffOn_of_smoothSlice n hG).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      -- the two sides of the induction hypothesis agree near `θ`
      have heq : Work.Elliptic.Dth1Iter n (fun θ => F θ + G θ) =ᶠ[𝓝 θ]
          (Work.Elliptic.Dth1Iter n F + Work.Elliptic.Dth1Iter n G) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
        exact ih y hy
      calc Work.Elliptic.Dth1Iter (n + 1) (fun θ => F θ + G θ) θ
          = Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n (fun θ => F θ + G θ)) θ := rfl
        _ = Real.sin (2 * θ)
              * deriv (Work.Elliptic.Dth1Iter n F + Work.Elliptic.Dth1Iter n G) θ := by
              rw [heq.deriv_eq]
        _ = Real.sin (2 * θ)
              * (deriv (Work.Elliptic.Dth1Iter n F) θ + deriv (Work.Elliptic.Dth1Iter n G) θ) := by
              rw [deriv_add hdiffF hdiffG]
        _ = Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n F) θ
              + Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n G) θ := by
              rw [mul_add]
        _ = Work.Elliptic.Dth1Iter (n + 1) F θ + Work.Elliptic.Dth1Iter (n + 1) G θ := rfl

  exact key m θ hθ

end

end Work.FTS.EllipticEst.TT
