import Mathlib
import Submission.Work.ZeroDensity.Montgomery.principalWindowFinsum_le_finset

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators

/-- The multiplicity-weighted `finsum` over the window `|Im ρ - t| ≤ 1` (with the value `0`
plugged in whenever the vanishing order is `0`) agrees with the same `finsum` carrying the extra
hypothesis `analyticOrderNatAt … ρ ≠ 0`; the two integrands differ only where both vanish. -/
private lemma windowIntegrand_eq (t : ℝ) :
    (fun ρ : ℂ =>
        if |ρ.im - t| ≤ 1 then ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0)
      = fun ρ : ℂ =>
        if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ |ρ.im - t| ≤ 1
          then ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0 := by
  funext ρ
  by_cases hz : analyticOrderNatAt completedRiemannZeta ρ = 0
  · rw [hz]; simp
  · by_cases hwin : |ρ.im - t| ≤ 1
    · rw [if_pos hwin, if_pos ⟨hz, hwin⟩]
    · rw [if_neg hwin, if_neg (fun h => hwin h.2)]

/-- The window integrand has finite support: its support is contained in the (finite) set of zeros
of `riemannZeta₁` of norm `< |t| + 2`, which in turn contains every zero of `Λ` of imaginary part
within distance `1` of `t`. -/
private lemma windowIntegrand_hasFiniteSupport (t : ℝ) :
    Function.HasFiniteSupport (fun ρ : ℂ =>
      if |ρ.im - t| ≤ 1 then ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0) := by
  classical
  rw [Function.HasFiniteSupport]
  obtain ⟨Z, hZ⟩ := Commons.NumberTheory.Zeta.zetaZeroBall (|t| + 2) (by positivity)
  refine (Z.filter (fun u => |u.im - t| ≤ 1)).finite_toSet.subset ?_
  intro ρ hρ
  rw [Function.mem_support] at hρ
  rw [Finset.mem_coe, Finset.mem_filter]
  by_cases hwin : |ρ.im - t| ≤ 1
  · refine ⟨?_, hwin⟩
    rw [if_pos hwin] at hρ
    have hord : analyticOrderNatAt completedRiemannZeta ρ ≠ 0 := by
      intro hz
      rw [hz] at hρ
      simp at hρ
    rw [hZ]
    have hΛ0 : completedRiemannZeta ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
    obtain ⟨hre0, hre1⟩ := Work.LinnikAreas.completedRiemannZeta_zero_strip hΛ0
    refine ⟨?_, ?_⟩
    · have him : |ρ.im| ≤ 1 + |t| := by
        have h1 : |ρ.im| ≤ |ρ.im - t| + |t| := by
          have := abs_add_le (ρ.im - t) t; simpa using this
        linarith
      have hre : |ρ.re| < 1 := by rw [abs_of_pos hre0]; exact hre1
      have hnorm : ‖ρ‖ < |t| + 2 := by
        have h1 := Complex.norm_le_abs_re_add_abs_im ρ
        linarith
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hnorm
    · have hordζ : analyticOrderNatAt riemannZeta₁ ρ ≠ 0 := by
        rw [← Work.LinnikAreas.FarRepel.ordNat_completedRiemannZeta_eq_zeta1 hre0 hre1]
        exact hord
      exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hordζ
  · rw [if_neg hwin] at hρ
    exact absurd rfl hρ

/-- **The unit-strip zero count of the completed Riemann zeta function.**  For every real `t` the
multiplicity-weighted number of zeros `ρ` of the completed Riemann zeta function `Λ` with
`|Im ρ - t| ≤ 1` is finite and is `≪ log(|t| + 2)`:

`∑ᶠ ρ, [|Im ρ - t| ≤ 1] · ord(ρ) ≤ C (log(|t| + 2) + 2)`.

The finiteness comes from `Commons.NumberTheory.Zeta.zetaZeroBall` (a zero of `Λ` lies in the open
strip `0 < Re < 1`, so with `|Im - t| ≤ 1` it lies in the ball of radius `|t| + 2`, and it is a
zero of `riemannZeta₁`), and the bound is
`Work.ZeroDensity.Montgomery.principalWindowFinsum_le_finset` together with
`Work.LinnikAreas.FarRepel.window1_count` (its constant `C` works). -/
theorem zetaStripCountBound :
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, Function.HasFiniteSupport (fun ρ : ℂ =>
        if |ρ.im - t| ≤ 1 then ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0)) ∧
      (∀ t : ℝ, (∑ᶠ ρ : ℂ,
          (if |ρ.im - t| ≤ 1 then ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) else 0))
        ≤ C * (Real.log (2 + |t|) + 2)) := by
  classical
  obtain ⟨C0, hC0pos, hC0⟩ := Work.LinnikAreas.FarRepel.window1_count
  refine ⟨C0, hC0pos, ?_, ?_⟩
  · intro t
    exact windowIntegrand_hasFiniteSupport t
  · intro t
    obtain ⟨S, hSwin, hSle⟩ := Work.ZeroDensity.Montgomery.principalWindowFinsum_le_finset t
    rw [windowIntegrand_eq t]
    exact hSle.trans (hC0 t S hSwin)

end Work.ZeroDensity.Ingham
