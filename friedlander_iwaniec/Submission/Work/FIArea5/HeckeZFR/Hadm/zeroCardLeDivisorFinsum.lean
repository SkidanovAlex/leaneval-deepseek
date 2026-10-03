import Mathlib
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset

namespace Work.FIArea5.HeckeZFR.Hadm

/-- The `untop₀` of `ENat.map (Nat.cast : ℕ → ℤ)` is the `toNat`. -/
lemma untop₀_enatMap_natCast (n : ℕ∞) :
    (ENat.map (Nat.cast : ℕ → ℤ) n).untop₀ = (n.toNat : ℤ) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe m => simp

theorem zeroCardLeDivisorFinsum (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ) (hne : ∃ z : ℂ, Λ z ≠ 0)
    (B : ℝ) :
    ∀ hZ : ({u : ℂ | Λ u = 0 ∧ ‖u‖ ≤ B} : Set ℂ).Finite,
      ((hZ.toFinset.card : ℝ) ≤
        ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 B)) u : ℝ)) := by
  classical
  intro hZ
  set U : Set ℂ := Metric.closedBall (0 : ℂ) B with hU
  have han : AnalyticOnNhd ℂ Λ U := fun z _ => hDiff.analyticAt z
  -- The analytic order of `Λ` is finite at every point.
  have htop : ∀ z : ℂ, analyticOrderAt Λ z ≠ ⊤ := by
    obtain ⟨w, hw⟩ := hne
    have hw' : analyticOrderAt Λ w ≠ ⊤ := by
      rw [(hDiff.analyticAt w).analyticOrderAt_eq_zero.mpr hw]
      exact ENat.zero_ne_top
    intro z
    exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
      (U := Set.univ) (fun a _ => hDiff.analyticAt a) isPreconnected_univ
      (Set.mem_univ w) (Set.mem_univ z) hw'
  -- Pointwise description of the divisor on the closed ball.
  have hdiv_eq : ∀ u ∈ U,
      (MeromorphicOn.divisor Λ U) u = (analyticOrderNatAt Λ u : ℤ) := by
    intro u hu
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply han hu]
    exact untop₀_enatMap_natCast _
  -- The divisor vanishes away from the zeros of `Λ` inside the closed ball.
  have hzero_off : ∀ u : ℂ, u ∉ ({u : ℂ | Λ u = 0 ∧ ‖u‖ ≤ B} : Set ℂ) →
      (MeromorphicOn.divisor Λ U) u = 0 := by
    intro u hu
    by_cases hle : ‖u‖ ≤ B
    · have hΛu : Λ u ≠ 0 := fun h0 => hu ⟨h0, hle⟩
      have huU : u ∈ U := by
        rw [hU, Metric.mem_closedBall, dist_zero_right]
        exact hle
      rw [hdiv_eq u huU]
      have h0 : analyticOrderNatAt Λ u = 0 := by
        by_contra h
        exact hΛu (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
      rw [h0]
      simp
    · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _
        (by
          rw [hU, Metric.mem_closedBall]
          intro h
          exact hle (by rwa [dist_zero_right] at h))
  -- The real-valued divisor is supported on the zeros inside the closed ball.
  have hsupp : Function.support (fun u : ℂ => ((MeromorphicOn.divisor Λ U) u : ℝ))
      ⊆ (hZ.toFinset : Set ℂ) := by
    intro u hu
    have hu' : ((MeromorphicOn.divisor Λ U) u : ℝ) ≠ 0 := hu
    by_cases hmem : u ∈ ({u : ℂ | Λ u = 0 ∧ ‖u‖ ≤ B} : Set ℂ)
    · rw [Set.Finite.coe_toFinset]
      exact hmem
    · exfalso
      refine hu' ?_
      rw [hzero_off u hmem]
      norm_num
  rw [finsum_eq_finsetSum_of_support_subset
      (fun u : ℂ => ((MeromorphicOn.divisor Λ U) u : ℝ)) (s := hZ.toFinset) hsupp]
  calc (hZ.toFinset.card : ℝ)
      = ∑ u ∈ hZ.toFinset, (1 : ℝ) := by simp
    _ ≤ ∑ u ∈ hZ.toFinset, ((MeromorphicOn.divisor Λ U) u : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [Set.Finite.mem_toFinset] at hu
        simp only [Set.mem_ofPred_eq] at hu
        have huU : u ∈ U := by
          rw [hU, Metric.mem_closedBall, dist_zero_right]
          exact hu.2
        rw [hdiv_eq u huU]
        have hne0 : analyticOrderAt Λ u ≠ 0 :=
          (hDiff.analyticAt u).analyticOrderAt_ne_zero.mpr hu.1
        have hpos : 1 ≤ analyticOrderNatAt Λ u := by
          rw [Nat.one_le_iff_ne_zero]
          intro h
          have h' : (analyticOrderAt Λ u).toNat = 0 := by
            simpa [analyticOrderNatAt] using h
          rw [ENat.toNat_eq_zero] at h'
          rcases h' with h' | h'
          · exact hne0 h'
          · exact htop u h'
        exact_mod_cast hpos

end Work.FIArea5.HeckeZFR.Hadm
