import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-- For `u : Lp ℂ 2 μ`, the square of the `L²` norm is the integral of `‖u x‖ ^ 2`.

This is the `L²` norm identity, obtained from the inner product structure on `Lp ℂ 2 μ`
together with `integral_re`: since `‖u‖ ^ 2 = re ⟪u, u⟫` and `⟪u, u⟫ = ∫ x, ⟪u x, u x⟫`,
we can pull the real part under the integral, where `re ⟪u x, u x⟫ = ‖u x‖ ^ 2`. -/
theorem norm_sq_Lp_eq_integral {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (u : MeasureTheory.Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  calc ‖u‖ ^ 2 = RCLike.re (inner ℂ u u) := norm_sq_eq_re_inner u
    _ = RCLike.re (∫ x, inner ℂ (u x) (u x) ∂μ) := by rw [MeasureTheory.L2.inner_def]
    _ = ∫ x, RCLike.re (inner ℂ (u x) (u x)) ∂μ :=
        (integral_re (MeasureTheory.L2.integrable_inner u u)).symm
    _ = ∫ x, ‖u x‖ ^ 2 ∂μ := by simp_rw [← norm_sq_eq_re_inner]

end Work.Diff.STE
