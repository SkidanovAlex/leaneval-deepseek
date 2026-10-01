import Mathlib
import Submission.Work.LinnikAreas.FarRepel.XiAnnulusDefs
import Submission.Work.LinnikAreas.DhK.XiAux

namespace Work.LinnikAreas.FarRepel

open scoped Classical BigOperators

/-- Pointwise domination of the ball-restricted annulus mass of `Ξ` by the ball divisor of `Ξ`.

For `u` inside the ball of radius `ρ`, the annulus mass is either `0` or the multiplicity of `u`
as a zero of `Ξ` (the divisor over the larger ball `‖u‖ ≤ R'`), which equals the divisor over the
ball of radius `ρ` since `u` lies in both balls; outside the ball the indicator vanishes. -/
lemma indicator_xiAnnulusMass_le_divisor (R R' : ℝ) (ρ : ℝ) (u : ℂ) :
    Set.indicator (Metric.closedBall (0 : ℂ) ρ) (xiAnnulusMass R R') u ≤
      (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
        (Metric.closedBall (0 : ℂ) ρ)) u : ℤ) : ℝ) := by
  classical
  rw [Set.indicator_apply]
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) ρ
  · rw [if_pos hu, xiAnnulusMass]
    by_cases h : R < ‖u‖
    · rw [if_pos h]
      by_cases hb : u ∈ Metric.closedBall (0 : ℂ) R'
      · have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
          (f := Work.LinnikAreas.DhK.Xi)
          (Work.LinnikAreas.DhK.Xi_analyticOnNhd
            (Metric.closedBall (0 : ℂ) ρ ∪ Metric.closedBall (0 : ℂ) R')) hu hb
        rw [heq]
      · rw [xi_divisor_eq_zero_of_not_mem hb]
        simp only [Int.cast_zero]
        exact xi_divisor_real_nonneg ρ u
    · rw [if_neg h]
      exact xi_divisor_real_nonneg ρ u
  · rw [if_neg hu]
    exact xi_divisor_real_nonneg ρ u

theorem xiAnnulusMass_count_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ R R' : ℝ, 2 ≤ R → R ≤ R' → ∀ ρ : ℝ, 2 ≤ ρ →
      (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0 : ℂ) ρ) (xiAnnulusMass R R') u)
        ≤ c * ρ * Work.LinnikAreas.DhK.xiL ρ := by
  classical
  obtain ⟨c0, hc0, hcount⟩ := Work.LinnikAreas.DhK.Xi_zeroCount_L
  refine ⟨c0, hc0, ?_⟩
  intro R R' hR2 hRR' ρ hρ2
  -- The ball-restricted annulus mass has finite support.
  have hfin_g : Function.HasFiniteSupport
      (fun u : ℂ => Set.indicator (Metric.closedBall (0 : ℂ) ρ) (xiAnnulusMass R R') u) := by
    refine (xiAnnulusMass_finiteSupport R R').subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hf
    apply hu
    by_cases hm : u ∈ Metric.closedBall (0 : ℂ) ρ
    · rwa [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm]
  -- Dominate termwise by the divisor of `Ξ` over the ball of radius `ρ`.
  have hstep1 : (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0 : ℂ) ρ) (xiAnnulusMass R R') u)
      ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall (0 : ℂ) ρ)) u : ℤ) : ℝ) :=
    finsum_le_finsum' hfin_g (xiDivisorReal_finiteSupport ρ)
      (fun u => indicator_xiAnnulusMass_le_divisor (R := R) (R' := R') ρ u)
  -- Apply the Jensen zero-count bound for `Ξ` in the `xiL` scale.
  exact le_trans hstep1 (hcount ρ hρ2)

end Work.LinnikAreas.FarRepel
