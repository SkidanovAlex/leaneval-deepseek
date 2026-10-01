import Mathlib
import Submission.Work.ZeroDensity.Zeta.ZetaZeroDefs
import Submission.Commons.NumberTheory.Zeta.zetaZeroBall
import Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators

/-- If the vanishing order of `f` at `z` is non-zero, then `f` vanishes at `z`. -/
private lemma eq_zero_of_analyticOrderNatAt_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (h : analyticOrderNatAt f z ≠ 0) : f z = 0 := by
  have h1 : analyticOrderAt f z ≠ 0 := by
    intro hh; exact h (by rw [analyticOrderNatAt, hh]; rfl)
  have h2 : ¬(¬ (AnalyticAt ℂ f z) ∨ f z ≠ 0) :=
    fun hh => h1 (analyticOrderAt_eq_zero.mpr hh)
  rw [not_or] at h2
  exact not_not.mp h2.2

/-- **The zeros of `Λ` in a window form a finite set, and the `finsum` over the window is its
Finset sum.**  For `σ ≥ 1/2` and `T ≥ 2` there is a `Finset S : Finset ℂ` whose elements are
exactly the zeros of the completed Riemann zeta function in the rectangle `σ ≤ Re ≤ 1`,
`|Im| ≤ T`, and over which the multiplicity-weighted count `zetaZeroCount σ T` is the ordinary
Finset sum of the vanishing orders.

(The finite set is obtained from `Commons.NumberTheory.Zeta.zetaZeroBall (T + 2)`: every zero of
`Λ` lies in the open strip `0 < Re < 1` by `Work.LinnikAreas.completedRiemannZeta_zero_strip`, so
in the window it has `‖ρ‖ < T + 2` and, being a zero of `riemannZeta₁`
(`Work.LinnikAreas.FarRepel.ordNat_completedRiemannZeta_eq_zeta1`), it lies in that ball.  Then
`finsum_eq_sum_of_support_subset` converts the `finsum` into the Finset sum.) -/
theorem zetaWindowZerosFinset (σ T : ℝ) (hσ : 1 / 2 ≤ σ) (hT : 2 ≤ T) :
    ∃ S : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ S ↔ analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧
        σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T) ∧
      Work.ZeroDensity.Zeta.zetaZeroCount σ T
        = ∑ ρ ∈ S, ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) := by
  classical
  obtain ⟨Z, hZ⟩ := Commons.NumberTheory.Zeta.zetaZeroBall (T + 2) (by linarith)
  set S : Finset ℂ := Z.filter (fun u => analyticOrderNatAt completedRiemannZeta u ≠ 0 ∧
    σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T) with hSdef
  have hmem : ∀ ρ : ℂ, ρ ∈ S ↔ analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧
      σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T := by
    intro ρ
    rw [hSdef, Finset.mem_filter, hZ]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨hord, hσρ, hρ1, him⟩
      have hΛ : completedRiemannZeta ρ = 0 :=
        eq_zero_of_analyticOrderNatAt_ne_zero hord
      obtain ⟨h0, h1⟩ := Work.LinnikAreas.completedRiemannZeta_zero_strip hΛ
      have hordζ : analyticOrderNatAt riemannZeta₁ ρ ≠ 0 := by
        rw [← Work.LinnikAreas.FarRepel.ordNat_completedRiemannZeta_eq_zeta1 h0 h1]
        exact hord
      refine ⟨⟨?_, ?_⟩, hord, hσρ, hρ1, him⟩
      · simp only [Metric.mem_closedBall, dist_zero_right]
        have hre : |ρ.re| < 1 := by rw [abs_of_pos h0]; exact h1
        have hnorm : ‖ρ‖ < T + 2 := by
          have h1' := Complex.norm_le_abs_re_add_abs_im ρ
          linarith
        exact le_of_lt hnorm
      · exact eq_zero_of_analyticOrderNatAt_ne_zero hordζ
  refine ⟨S, hmem, ?_⟩
  set F : ℂ → ℝ := fun ρ => if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0 with hF
  have hcount : Work.ZeroDensity.Zeta.zetaZeroCount σ T = ∑ᶠ ρ : ℂ, F ρ := by
    rw [Work.ZeroDensity.Zeta.zetaZeroCount, hF]
  have hsupp : Function.support F ⊆ ↑S := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    · have hord : analyticOrderNatAt completedRiemannZeta ρ ≠ 0 := by
        intro hzero
        exact hρ (by rw [hF]; simp [hzero])
      exact (hmem ρ).mpr ⟨hord, hc⟩
    · exact absurd (by rw [hF]; simp [if_neg hc]) hρ
  calc Work.ZeroDensity.Zeta.zetaZeroCount σ T
      = ∑ᶠ ρ : ℂ, F ρ := hcount
    _ = ∑ ρ ∈ S, F ρ := finsum_eq_sum_of_support_subset F hsupp
    _ = ∑ ρ ∈ S, ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [hF]
        have hw := (hmem ρ).mp hρ
        simp only [if_pos hw.2]

end Work.ZeroDensity.Ingham
