import Mathlib
import Submission.Commons.Analysis.Complex.exterior_jensen

namespace Commons.Analysis.Complex

/-- The divisor of an analytic function `f` on an open-ish set `U` at a point `z ∈ U` equals the
order of vanishing `analyticOrderNatAt f z` (cast to `ℤ`), i.e. the multiplicity of the zero. This
is the reformulation of `MeromorphicOn.AnalyticOnNhd.divisor_apply` in terms of the natural-number
order `analyticOrderNatAt`. -/
lemma divisor_eq_analyticOrderNatAt_cast {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
  simp only [analyticOrderNatAt]
  cases h : analyticOrderAt f z with
  | top => simp
  | coe n => simp

/-- **Exterior Jensen formula, with the exterior zeros counted with multiplicity.** If `H` is holomorphic on `{z | 1 ≤ ‖z‖}`, tends to `L ≠ 0` at infinity and is nonzero on the unit circle, then `Real.log ‖L‖ + ∑ z ∈ S, (analyticOrderNatAt H z : ℝ) * Real.log ‖z‖` equals the circular average of `Real.log ‖H‖`; here `S` is the set of exterior zeros of `H`. Counting multiplicity is essential: the same statement with plain `Real.log ‖z‖` is false (`not_exterior_jensen`). Proof route: put `f w = H w⁻¹` (`f 0 = L`, removable singularity), apply Jensen's formula `AnalyticOnNhd.circleAverage_log_norm` to `f` on `closedBall 0 1`, and translate the divisor sum back. -/
theorem exterior_jensen_multiplicity (H : ℂ → ℂ) (L : ℂ)
    (hH : ∀ z : ℂ, 1 ≤ ‖z‖ → AnalyticAt ℂ H z)
    (hL : Filter.Tendsto H (Filter.comap (fun z : ℂ => ‖z‖) Filter.atTop) (nhds L))
    (hL0 : L ≠ 0)
    (hcirc : ∀ θ : ℝ, H (Complex.exp (θ * Complex.I)) ≠ 0)
    (S : Finset ℂ)
    (hS : ∀ z : ℂ, H z = 0 → 1 < ‖z‖ → z ∈ S)
    (hS' : ∀ z ∈ S, H z = 0 ∧ 1 < ‖z‖) :
    Real.log ‖L‖ + ∑ z ∈ S, (analyticOrderNatAt H z : ℝ) * Real.log ‖z‖
      = (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), Real.log ‖H (Complex.exp (θ * Complex.I))‖ := by
  -- The multiplicity-aware exterior Jensen formula stated as a `finsum` over the exterior
  -- divisor, from the commons.
  have hej := exterior_jensen H L hH hL hL0 hcirc
  have hH_an : AnalyticOnNhd ℂ H {z : ℂ | 1 < ‖z‖} := fun z hz => hH z (le_of_lt hz)
  -- Rewrite the exterior-divisor `finsum` as the finite sum over the (given, exact) zero set `S`.
  have hsum : (∑ᶠ z : ℂ, ((MeromorphicOn.divisor H {z : ℂ | 1 < ‖z‖}) z : ℝ) * Real.log ‖z‖)
      = ∑ z ∈ S, (analyticOrderNatAt H z : ℝ) * Real.log ‖z‖ := by
    rw [finsum_eq_sum_of_support_subset _ (s := S) ?hsub]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' : H z = 0 ∧ 1 < ‖z‖ := hS' z hz
    rw [divisor_eq_analyticOrderNatAt_cast hH_an hz'.2]
    push_cast
    ring
    -- The support of the summand is contained in `S`: outside `S` the exterior divisor vanishes.
    case hsub =>
      rw [Function.support_subset_iff]
      intro z hz
      by_contra hzS
      apply hz
      by_cases h1 : 1 < ‖z‖
      · -- In the exterior but not in `S`: `H z ≠ 0`, so the order (and hence the term) is `0`.
        have hHz : H z ≠ 0 := fun h0 => hzS (hS z h0 h1)
        have hord : analyticOrderNatAt H z = 0 := by
          rw [analyticOrderNatAt, (hH z (le_of_lt h1)).analyticOrderAt_eq_zero.mpr hHz]
          simp
        rw [divisor_eq_analyticOrderNatAt_cast hH_an h1, hord]
        simp
      · -- Inside the closed unit disc: the exterior divisor is zero there.
        have hz0 : (MeromorphicOn.divisor H {z : ℂ | 1 < ‖z‖}) z = 0 :=
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h1
        rw [hz0]
        simp
  rw [hsum] at hej
  exact hej

end Commons.Analysis.Complex
