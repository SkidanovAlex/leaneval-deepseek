import Mathlib
import Submission.Work.ZeroDensity.Montgomery.principalWindowFinsum_le_finset

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- **Local zero count for the Riemann zeta function**: the multiplicity-weighted number of
non-trivial zeros of `ζ` in the closed unit disk around a point `a` with `0 ≤ Re a ≤ 1` is
`≪ log(‖a‖ + 2)`.  This is Jensen's formula applied to the entire completion `Ξ` of `ζ` (whose
zeros are exactly the non-trivial zeros of `ζ`, with multiplicity), together with the growth
bound `Ξ(σ+it) ≪ (|t|+2)^{C}`; the nontrivial zeros of `ζ` are the zeros of
`completedRiemannZeta` away from `0` and `1`. -/
theorem localZeroCountZeta :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℂ), 0 ≤ a.re → a.re ≤ 1 →
      (∑ᶠ ρ : ℂ, (if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ ‖ρ - a‖ ≤ 1
        then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0))
        ≤ C * (Real.log (‖a‖ + 2) + 1) := by
  classical
  obtain ⟨C0, hC0pos, hC0⟩ := Work.LinnikAreas.FarRepel.window1_count
  refine ⟨2 * C0, by positivity, ?_⟩
  intro a _ha0 _ha1
  -- Every zero counted lies in the unit window `|Im z - Im a| ≤ 1`; the window count is
  -- `window1_count`.
  obtain ⟨Z, hZ⟩ := Commons.NumberTheory.Zeta.zetaZeroBall (|a.im| + 2) (by positivity)
  set S : Finset ℂ := Z.filter (fun u => |u.im - a.im| ≤ 1) with hS
  have hwin : (∑ᶠ ρ : ℂ, (if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ ‖ρ - a‖ ≤ 1
      then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0))
      ≤ ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) := by
    set F : ℂ → ℝ := fun ρ => if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ ‖ρ - a‖ ≤ 1
      then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0 with hF
    have hsupp : Function.support F ⊆ ↑S := by
      intro ρ hρ
      rw [Function.mem_support] at hρ
      by_cases hc : analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ ‖ρ - a‖ ≤ 1
      · obtain ⟨hord, hdist⟩ := hc
        rw [Finset.mem_coe, hS, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [hZ]
          have hΛ0 : completedRiemannZeta ρ = 0 :=
            apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
          obtain ⟨hre0, hre1⟩ := Work.LinnikAreas.completedRiemannZeta_zero_strip hΛ0
          refine ⟨?_, ?_⟩
          · have him1 : |ρ.im - a.im| ≤ ‖ρ - a‖ := by
              have h := Complex.abs_im_le_norm (ρ - a)
              simpa [Complex.sub_im] using h
            have him2 : |ρ.im| ≤ |ρ.im - a.im| + |a.im| := by
              have h := abs_add_le (ρ.im - a.im) a.im
              simpa using h
            have him3 : |ρ.im| ≤ 1 + |a.im| := by linarith
            have hre : |ρ.re| < 1 := by rw [abs_of_pos hre0]; exact hre1
            have hnorm : ‖ρ‖ < |a.im| + 2 := by
              have h := Complex.norm_le_abs_re_add_abs_im ρ
              linarith
            simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hnorm
          · have hordζ : analyticOrderNatAt riemannZeta₁ ρ ≠ 0 := by
              rw [← Work.LinnikAreas.FarRepel.ordNat_completedRiemannZeta_eq_zeta1 hre0 hre1]
              exact hord
            exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hordζ
        · have h := Complex.abs_im_le_norm (ρ - a)
          have him1 : |ρ.im - a.im| ≤ ‖ρ - a‖ := by simpa [Complex.sub_im] using h
          linarith
      · have hzero : F ρ = 0 := by rw [hF]; simp [if_neg hc]
        exact absurd hzero hρ
    calc (∑ᶠ ρ : ℂ, (if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ ‖ρ - a‖ ≤ 1
            then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0))
        = ∑ᶠ ρ : ℂ, F ρ := by rw [hF]
      _ = ∑ ρ ∈ S, F ρ := finsum_eq_sum_of_support_subset F hsupp
      _ ≤ ∑ ρ ∈ S, ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro ρ _
          rw [hF]
          beta_reduce
          by_cases hc : analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ ‖ρ - a‖ ≤ 1
          · rw [if_pos hc]
          · rw [if_neg hc]
            exact Nat.cast_nonneg _
  refine hwin.trans (le_trans (hC0 a.im S ?_) ?_)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · have him : |a.im| ≤ ‖a‖ := Complex.abs_im_le_norm a
    have hlog : 0 ≤ Real.log (‖a‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg a])
    have hle : Real.log (2 + |a.im|) ≤ Real.log (‖a‖ + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (2 + |a.im|) + 2 ≤ 2 * (Real.log (‖a‖ + 2) + 1) := by linarith
    calc C0 * (Real.log (2 + |a.im|) + 2)
        ≤ C0 * (2 * (Real.log (‖a‖ + 2) + 1)) :=
          mul_le_mul_of_nonneg_left h2 hC0pos.le
      _ = 2 * C0 * (Real.log (‖a‖ + 2) + 1) := by ring

end Work.ZeroDensity.Ingham
