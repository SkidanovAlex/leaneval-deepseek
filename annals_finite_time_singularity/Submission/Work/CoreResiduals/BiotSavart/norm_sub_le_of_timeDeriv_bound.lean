import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.CoreResiduals.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **Mean value bound in time.**  If the slices `ω y ·` are differentiable on the convex set `I`
with the time derivative `∂ₜω y ·` bounded by `M₁ ≥ 0`, then `ω` is Lipschitz in `t` with constant
`M₁` on `I`.  Proof: the mean value inequality on a convex set
(`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`) applied to `f = ω y ·` with
`f' x = ContinuousLinearMap.toSpanSingleton ℝ (∂ₜω y x)` (`HasDerivAt.hasFDerivAt`), using that
`toSpanSingleton` is an isometry (`ContinuousLinearMap.toSpanSingletonCLE`). -/
theorem norm_sub_le_of_timeDeriv_bound {ω : Work.CoreResiduals.R3 → ℝ → Work.CoreResiduals.R3}
    {I : Set ℝ} {M₁ : ℝ} (hM₁ : 0 ≤ M₁) (hconv : Convex ℝ I)
    (hdc : ∀ t ∈ I, ∀ y : Work.CoreResiduals.R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    (hbdd : ∀ t ∈ I, ∀ y : Work.CoreResiduals.R3,
      ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ M₁) :
    ∀ t ∈ I, ∀ s ∈ I, ∀ y : Work.CoreResiduals.R3,
      ‖ω y t - ω y s‖ ≤ M₁ * |t - s| := by
  intro t ht s hs y
  have hdiff : ∀ x ∈ I, DifferentiableAt ℝ (fun r : ℝ => ω y r) x :=
    fun x hx => (hdc x hx y).differentiableAt
  have hbound : ∀ x ∈ I, ‖deriv (fun r : ℝ => ω y r) x‖ ≤ M₁ :=
    fun x hx => by
      rw [show deriv (fun r : ℝ => ω y r) x = FiniteTimeSingularity.timeDeriv ω y x from rfl]
      exact hbdd x hx y
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconv hs ht
  simpa using h

end Work.CoreResiduals.BiotSavart
