import Mathlib

namespace Work.WilE2

/-- If `f` is positive on an open interval `(a, b)`, vanishes at the right endpoint
`b`, and has a derivative `d` at `b` that is nonzero, then that derivative is
negative.

Indeed the difference quotient `(f x - f b) / (x - b)` is positive-over-negative
hence `< 0` for every `x ∈ (a, b)`, so its limit `d` at `b` satisfies `d ≤ 0`;
combined with `d ≠ 0` this gives `d < 0`. -/
theorem deriv_right_neg_of_pos_on_Ioo {f : ℝ → ℝ} {a b d : ℝ} (hab : a < b)
    (hb : HasDerivAt f d b) (hfb : f b = 0) (hd : d ≠ 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) : d < 0 := by
  -- `HasDerivAt` gives the limit of the slope at `b` along `𝓝[≠] b`; restrict to the left.
  have htend : Filter.Tendsto (slope f b) (nhdsWithin b (Set.Iio b)) (nhds d) :=
    hb.tendsto_slope.mono_left (nhdsWithin_mono b (fun _ hx => ne_of_lt hx))
  -- `(a, b)` is a left-neighbourhood of `b`.
  have hmem : Set.Ioo a b ∈ (nhdsWithin b (Set.Iio b) : Filter ℝ) := by
    rw [Set.Ioo]
    exact Filter.inter_mem (nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hab)) self_mem_nhdsWithin
  -- On that neighbourhood the slope is `≤ 0`.
  have hevent : (slope f b) ≤ᶠ[nhdsWithin b (Set.Iio b)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmem] with x hx
    rw [slope_def_field, hfb]
    exact le_of_lt (div_neg_of_pos_of_neg (by linarith [hpos x hx]) (by linarith [hx.2]))
  -- Hence the limit `d` is `≤ 0`, and nonzero forces `d < 0`.
  exact lt_of_le_of_ne (le_of_tendsto_of_tendsto htend tendsto_const_nhds hevent) hd

end Work.WilE2
