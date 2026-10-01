import Mathlib
import Submission.Work.LinnikAreas.ownRepelNW.RectFreeImports

namespace Work.LinnikAreas.ownRepelNW

open scoped BigOperators

theorem orderSum_invSq_bound_of_count {c : ℝ} (hc : 0 ≤ c) : ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ), AnalyticOnNhd ℂ F Set.univ → ∀ q : ℝ, 0 ≤ q → (∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ → (∑ᶠ u : ℂ, (((MeromorphicOn.divisor F (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + q + 2)) → ∀ s : ℂ, ∀ S : Finset ℂ, ∑ u ∈ S, (analyticOrderNatAt F u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)) ≤ C * (Real.log (2 + ‖s‖) + q + 2) := by
  obtain ⟨C1, hC1pos, hC1gen⟩ :=
    Commons.Analysis.Asymptotics.invSq_zeroSum_of_count_uniform (c := c) hc
  refine ⟨C1, hC1pos, ?_⟩
  intro F hF q hq hcnt s S
  set ρ0 : ℝ := 1 + ∑ u ∈ S, ‖u‖ with hρ0
  have hSρ : ∀ u ∈ S, ‖u‖ ≤ ρ0 := by
    intro u hu
    have h1 : ‖u‖ ≤ ∑ v ∈ S, ‖v‖ :=
      Finset.single_le_sum (f := fun v : ℂ => ‖v‖) (fun v _ => norm_nonneg v) hu
    rw [hρ0]; linarith
  set m : ℂ → ℝ :=
    fun u => (((MeromorphicOn.divisor F (Metric.closedBall 0 ρ0)) u : ℤ) : ℝ) with hm
  have hmnn : ∀ u : ℂ, 0 ≤ m u := by
    intro u
    rw [hm]
    exact Int.cast_nonneg
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hF.mono (Set.subset_univ _)) u)
  have hmfin : Function.HasFiniteSupport m := by
    have hd_fin : Function.HasFiniteSupport
        (fun u : ℂ => MeromorphicOn.divisor F (Metric.closedBall 0 ρ0) u) :=
      (MeromorphicOn.divisor F (Metric.closedBall 0 ρ0)).finiteSupport
        (isCompact_closedBall 0 ρ0)
    have hcast : Function.HasFiniteSupport
        (fun u : ℂ => (((MeromorphicOn.divisor F (Metric.closedBall 0 ρ0)) u : ℤ) : ℝ)) :=
      hd_fin.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h
        exact hu (by rw [h]; simp))
    simpa [hm] using hcast
  have hcount' : ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall a ρ) m u)
        ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + q + 2) := by
    intro a ρ hρ
    have h1 : (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall a ρ) m u)
        ≤ (∑ᶠ u : ℂ, (((MeromorphicOn.divisor F (Metric.closedBall a ρ)) u : ℤ) : ℝ)) := by
      simpa [hm] using
        Commons.Analysis.Complex.indicator_divisorBall_le_divisorBallFinsum F hF ρ0 a ρ
    exact h1.trans (hcnt a ρ hρ)
  have hstep2 := hC1gen q hq m hmnn hmfin hcount' s
  have hstep1 := Commons.Analysis.Complex.finset_orderSum_le_divisorFinsum F hF ρ0 s S hSρ
  exact hstep1.trans (by simpa [hm] using hstep2)

end Work.LinnikAreas.ownRepelNW
