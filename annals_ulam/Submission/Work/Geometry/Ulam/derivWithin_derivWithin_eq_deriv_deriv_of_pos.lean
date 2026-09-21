import Mathlib

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped ContDiff Pointwise Interval Topology

set_option autoImplicit false

/-- Interior within/global transport for the second derivative. -/
lemma derivWithin_derivWithin_eq_deriv_deriv_of_pos
    {R : ℝ → ℝ} {x : ℝ} (hx : 0 < x) (hx_lt : x < Real.pi / 2) :
    derivWithin (derivWithin R (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) x = deriv (deriv R) x := by
  have hmem : Set.Icc 0 (Real.pi / 2) ∈ 𝓝 x := Icc_mem_nhds hx hx_lt
  have h1 : derivWithin (derivWithin R (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) x =
      deriv (derivWithin R (Set.Icc 0 (Real.pi / 2))) x :=
    derivWithin_of_mem_nhds hmem
  rw [h1]
  have hev : derivWithin R (Set.Icc 0 (Real.pi / 2)) =ᶠ[𝓝 x] deriv R := by
    filter_upwards [Ioo_mem_nhds hx hx_lt] with y hy
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
  exact hev.deriv_eq

end Commons.Geometry.Ulam
