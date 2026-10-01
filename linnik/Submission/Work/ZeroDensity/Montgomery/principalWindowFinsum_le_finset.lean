import Mathlib
import Submission.Commons.NumberTheory.Zeta.zetaZeroBall
import Submission.Work.LinnikAreas.completedRiemannZeta_zero_strip
import Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound

namespace Work.ZeroDensity.Montgomery

/-- If the vanishing order of `f` at `z` is non-zero, then `f` vanishes at `z`. -/
private lemma eq_zero_of_analyticOrderNatAt_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (h : analyticOrderNatAt f z ≠ 0) : f z = 0 := by
  have h1 : analyticOrderAt f z ≠ 0 := by
    intro hh; exact h (by rw [analyticOrderNatAt, hh]; rfl)
  have h2 : ¬(¬ (AnalyticAt ℂ f z) ∨ f z ≠ 0) :=
    fun hh => h1 (analyticOrderAt_eq_zero.mpr hh)
  rw [not_or] at h2
  exact not_not.mp h2.2

/-- **The window sum over the zeros of `Λ = completedRiemannZeta` is a Finset sum.**  The
multiplicity-weighted number of zeros `ρ` of the completed Riemann zeta function `Λ` with
`|Im ρ - t| ≤ 1` (i.e. the finsum of the vanishing orders over that window) is bounded by the sum
of the vanishing orders of `Λ` over a finite set `S` of complex numbers all of which satisfy
`|Im u - t| ≤ 1`.

The finite set is obtained from `Commons.NumberTheory.Zeta.zetaZeroBall` (module
`Submission.Commons.NumberTheory.Zeta.zetaZeroBall`): the zeros of the entire completion
`riemannZeta₁` of `(s-1)ζ(s)` in the closed ball of radius `|t| + 2` form a `Finset`; one filters
it by the window condition.  Every zero counted by the finsum lies in that ball: it lies in the
open strip `0 < Re < 1` by `Work.LinnikAreas.completedRiemannZeta_zero_strip` (module
`Submission.Work.LinnikAreas.completedRiemannZeta_zero_strip`), so
`‖ρ‖ ^ 2 < 1 + (|t| + 1) ^ 2 ≤ (|t| + 2) ^ 2`, and it is a zero of `riemannZeta₁` because
`Work.LinnikAreas.FarRepel.ordNat_completedRiemannZeta_eq_zeta1` (module
`Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound`) identifies the vanishing orders of `Λ`
and `ζ₁` in the strip.  Finally `finsum_eq_sum_of_support_subset` (Mathlib) converts the finsum
into the Finset sum. -/
theorem principalWindowFinsum_le_finset (t : ℝ) :
    ∃ S : Finset ℂ, (∀ u ∈ S, |u.im - t| ≤ 1) ∧
      (∑ᶠ ρ : ℂ, (if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ |ρ.im - t| ≤ 1
          then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0))
        ≤ ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) := by
  classical
  obtain ⟨Z, hZ⟩ := Commons.NumberTheory.Zeta.zetaZeroBall (|t| + 2) (by positivity)
  refine ⟨Z.filter (fun u => |u.im - t| ≤ 1), ?_, ?_⟩
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · set F : ℂ → ℝ := fun ρ =>
      if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ |ρ.im - t| ≤ 1
        then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0 with hF
    have hsupp : Function.support F ⊆ ↑(Z.filter (fun u => |u.im - t| ≤ 1)) := by
      intro ρ hρ
      rw [Function.mem_support] at hρ
      by_cases hc : analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ |ρ.im - t| ≤ 1
      · obtain ⟨hord, hwin⟩ := hc
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨?_, hwin⟩
        rw [hZ]
        have hΛ0 : completedRiemannZeta ρ = 0 := eq_zero_of_analyticOrderNatAt_ne_zero hord
        obtain ⟨hre0, hre1⟩ := Work.LinnikAreas.completedRiemannZeta_zero_strip hΛ0
        refine ⟨?_, ?_⟩
        · -- `ρ` lies in the closed ball of radius `|t| + 2`
          have him : |ρ.im| ≤ 1 + |t| := by
            have h1 : |ρ.im| ≤ |ρ.im - t| + |t| := by
              have := abs_add_le (ρ.im - t) t
              simpa using this
            linarith
          have hre : |ρ.re| < 1 := by rw [abs_of_pos hre0]; exact hre1
          have hnorm : ‖ρ‖ < |t| + 2 := by
            have h1 := Complex.norm_le_abs_re_add_abs_im ρ
            linarith
          simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hnorm
        · -- `ρ` is a zero of `riemannZeta₁`
          have hordζ : analyticOrderNatAt riemannZeta₁ ρ ≠ 0 := by
            rw [← Work.LinnikAreas.FarRepel.ordNat_completedRiemannZeta_eq_zeta1 hre0 hre1]
            exact hord
          exact eq_zero_of_analyticOrderNatAt_ne_zero hordζ
      · have hzero : F ρ = 0 := by rw [hF]; simp [if_neg hc]
        exact absurd hzero hρ
    calc (∑ᶠ ρ : ℂ, (if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ |ρ.im - t| ≤ 1
            then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0))
        = ∑ᶠ ρ : ℂ, F ρ := by rw [hF]
      _ = ∑ ρ ∈ Z.filter (fun u => |u.im - t| ≤ 1), F ρ :=
            finsum_eq_sum_of_support_subset F hsupp
      _ ≤ ∑ ρ ∈ Z.filter (fun u => |u.im - t| ≤ 1),
            ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [hF]
          beta_reduce
          by_cases hc : analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ |ρ.im - t| ≤ 1
          · rw [if_pos hc]
          · rw [if_neg hc]
            exact Nat.cast_nonneg _

end Work.ZeroDensity.Montgomery
