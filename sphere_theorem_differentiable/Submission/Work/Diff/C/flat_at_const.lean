import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped ContDiff

/-- A smooth function `f : ℝ → ℝ` that is constant on the left half-line `(-∞, a]` has all its
iterated derivatives of order `≥ 1` vanishing at `a`. -/
theorem flat_at_const {f : ℝ → ℝ} {a c : ℝ} (hf : ContDiff ℝ ∞ f) (h : ∀ x ≤ a, f x = c)
    (k : ℕ) : iteratedDeriv (k + 1) f a = 0 := by
  -- `iteratedDeriv (k+1) f` is continuous (smoothness of `f`), and vanishes at every `x < a`
  -- because `f` is constant on a whole neighbourhood of such an `x`.  Passing to the limit
  -- along `(-∞, a) → a` (where the filter `𝓝[<] a` is nontrivial) gives the value `0` at `a`.
  have hcont : Continuous (iteratedDeriv (k + 1) f) := hf.continuous_iteratedDeriv (k + 1) (by simp)
  have hzero : ∀ x < a, iteratedDeriv (k + 1) f x = 0 := by
    intro x hx
    have hev : f =ᶠ[nhds x] fun _ => c := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact h y (le_of_lt hy)
    have h2 := (hev.iteratedDeriv (k + 1)).eq_of_nhds
    simpa [iteratedDeriv_const] using h2
  have h1 : Filter.Tendsto (iteratedDeriv (k + 1) f) (nhdsWithin a (Set.Iio a))
      (nhds (iteratedDeriv (k + 1) f a)) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (iteratedDeriv (k + 1) f) (nhdsWithin a (Set.Iio a)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hzero x hx).symm
  exact tendsto_nhds_unique h1 h2

end Work.Diff.C
