import Mathlib

namespace Work.WilE2

open Filter
open scoped Topology

/-- If `f a = 0`, `f` is differentiable at `a` with derivative `c`, and `f` is positive
on the open interval `(a, b)` to the right of `a`, then the derivative `c` at `a` is
nonnegative; since `c ≠ 0` it is strictly positive.

The reason is that on `(a, b)` the slope `slope f a x = (f x - f a) / (x - a)` is strictly
positive, and `HasDerivAt` makes it tend to `c` along the right-neighbourhood filter
`𝓝[>] a`; a limit of nonnegative values is nonnegative. -/
theorem deriv_left_pos_of_pos_on_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (ha : HasDerivAt f c a) (hfa : f a = 0) (hc : c ≠ 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) : 0 < c := by
  -- `(a, b)` is a right-neighbourhood of `a`
  have hmem : Set.Ioo a b ∈ nhdsWithin a (Set.Ioi a) := Ioo_mem_nhdsGT hab
  -- the slope tends to `c` along `𝓝[>] a`
  have htend : Tendsto (slope f a) (nhdsWithin a (Set.Ioi a)) (𝓝 c) :=
    ha.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a)
  -- on `(a, b)` the slope is nonnegative
  have hev : ∀ᶠ x in nhdsWithin a (Set.Ioi a), (0 : ℝ) ≤ slope f a x := by
    filter_upwards [hmem] with x hx
    have hxa : 0 < x - a := sub_pos.mpr hx.1
    have hfx : 0 < f x - f a := by rw [hfa, sub_zero]; exact hpos x hx
    rw [slope_def_module, smul_eq_mul]
    positivity
  -- hence `0 ≤ c`
  have hnonneg : 0 ≤ c := ge_of_tendsto htend hev
  exact lt_of_le_of_ne' hnonneg hc

end Work.WilE2
