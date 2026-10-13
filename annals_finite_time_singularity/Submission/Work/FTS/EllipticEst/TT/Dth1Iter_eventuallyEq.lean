import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- `D_θ = sin(2θ) ∂_θ` respects eventual equality of the underlying functions. -/
theorem Dth1_eventuallyEq {F G : ℝ → ℝ} {θ : ℝ} (h : F =ᶠ[nhds θ] G) :
    Work.Elliptic.Dth1 F =ᶠ[nhds θ] Work.Elliptic.Dth1 G := by
  filter_upwards [h.deriv] with y hy
  simp only [Work.Elliptic.Dth1, hy]

/-- The iterates `Dth1Iter n` respect eventual equality of the underlying functions. -/
theorem Dth1Iter_eventuallyEq_aux (m : ℕ) {F G : ℝ → ℝ} {θ : ℝ} (h : F =ᶠ[nhds θ] G) :
    Work.Elliptic.Dth1Iter m F =ᶠ[nhds θ] Work.Elliptic.Dth1Iter m G := by
  induction m with
  | zero => simpa using h
  | succ n ih =>
      simpa using Dth1_eventuallyEq (F := Work.Elliptic.Dth1Iter n F)
        (G := Work.Elliptic.Dth1Iter n G) (θ := θ) ih

theorem Dth1Iter_eventuallyEq (m : ℕ) {F G : ℝ → ℝ} {θ : ℝ} (h : F =ᶠ[nhds θ] G) :
    Work.Elliptic.Dth1Iter m F θ = Work.Elliptic.Dth1Iter m G θ :=
  (Dth1Iter_eventuallyEq_aux m h).eq_of_nhds

end Work.FTS.EllipticEst.TT
