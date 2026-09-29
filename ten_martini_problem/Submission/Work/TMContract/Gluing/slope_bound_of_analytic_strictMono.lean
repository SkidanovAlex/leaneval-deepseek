import Mathlib
import Submission.Work.TMContract.Gluing.exists_deriv_pos_of_analytic_strictMono
import Submission.Work.TMContract.Gluing.slope_bound_of_deriv_pos_at_point

namespace Work.TMContract.Gluing

/-- **A uniform positive slope bound on a subinterval.**

Let `N : ℝ → ℝ` be real-analytic on the open interval `(a,b)` (`hN`) and strictly monotone
there (`hmono`). Then there is a nondegenerate closed subinterval `[c,d] ⊆ (a,b)` and a
constant `c₀ > 0` such that `N` grows at least linearly with rate `c₀` on `[c,d]`, i.e.
`c₀ * (y - x) ≤ N y - N x` whenever `x < y` both lie in `[c,d]`.

The proof is the gluing of two ingredients:
* `exists_deriv_pos_of_analytic_strictMono` produces an interior point `x₀` with
  `0 < deriv N x₀` (monotonicity forces `deriv N ≥ 0`, and a vanishing derivative on the
  connected open set `(a,b)` would force `N` to be constant there);
* `slope_bound_of_deriv_pos_at_point` turns continuity of `deriv N` at such a point into a
  subinterval on which `deriv N` stays bounded below by `deriv N x₀ / 2 > 0`, and applies the
  mean value theorem there. -/
theorem slope_bound_of_analytic_strictMono {N : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hN : AnalyticOnNhd ℝ N (Set.Ioo a b)) (hmono : StrictMonoOn N (Set.Ioo a b)) :
    ∃ c d c₀ : ℝ, a < c ∧ c < d ∧ d < b ∧ 0 < c₀ ∧
      ∀ x ∈ Set.Icc c d, ∀ y ∈ Set.Icc c d, x < y → c₀ * (y - x) ≤ N y - N x := by
  -- A strictly monotone analytic function has positive derivative at some interior point.
  obtain ⟨x₀, hx₀, hx₀pos⟩ := exists_deriv_pos_of_analytic_strictMono hab hN hmono
  -- The derivative of an analytic function is again analytic, hence continuous at `x₀`.
  exact slope_bound_of_deriv_pos_at_point hab hx₀ hx₀pos
    ((hN.deriv_of_isOpen isOpen_Ioo).continuousOn.continuousAt (isOpen_Ioo.mem_nhds hx₀))
    hN.continuousOn hN.differentiableOn

end Work.TMContract.Gluing
