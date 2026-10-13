import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.bt_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- The angular integral identity behind the good term: the `L²`-integral of
`(∂_θ D_z³ f)² sin(2θ)^{2-γ}`, multiplied by `(w z)²`, is the `L²`-integral of the weighted
mixed derivative `(D_z³ D_θ f · W)²`.  This is the pointwise identity
`bt_mixed_weight_id` integrated against `dθ`. -/
theorem bt_integral_weight_id (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (∫ s in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.DzIter 3 f) z s) ^ 2
          * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2
      = ∫ s in Work.Spaces.Iθ,
          (Work.Spaces.mixed 3 1 f z s * Work.Spaces.Wt α z s) ^ 2 := by
  -- Pull the constant `(w z)^2` inside the integral.
  rw [← MeasureTheory.integral_mul_const]
  -- Integrands agree pointwise on `Iθ` by the pointwise weight identity.
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro s hs
  simp only
  have h := bt_mixed_weight_id hsm α z s hα hα1 hz hs
  rw [show Work.Spaces.pth (Work.Spaces.DzIter 3 f) z s ^ 2
          * Real.sin (2 * s) ^ (2 - Work.Spaces.gam α) * Work.Spaces.w z ^ 2
        = Work.Spaces.pth (Work.Spaces.DzIter 3 f) z s ^ 2 * Work.Spaces.w z ^ 2
          * Real.sin (2 * s) ^ (2 - Work.Spaces.gam α) by ring]
  exact h

end Work.Spaces
