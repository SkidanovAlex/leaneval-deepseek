import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_band_sub_id_isLittleO

namespace Commons.NumberTheory.Chebyshev

/-- **Relative error form of the prime number theorem for `θ`.**

For every `δ > 0` and all sufficiently large `x`, the Chebyshev function
`θ x = Σ_{p ≤ x} log p` differs from `x` by at most a relative error `δ`:
`|θ x − x| ≤ δ · x`.  This is the `ε`-form of `θ x ∼ x`
(`Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_isLittleO`,
i.e. `θ x − x = o(x)`). -/
theorem theta_rel_error (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ x : ℝ, Y₀ ≤ x → |Chebyshev.theta x - x| ≤ δ * x := by
  have h := (Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_isLittleO.bound
    (c := δ)) hδ
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 h
  refine ⟨max Y₀ 0, fun x hx => ?_⟩
  have hxY : Y₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
  have h' := hY₀ x hxY

  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0] at h'

end Commons.NumberTheory.Chebyshev
