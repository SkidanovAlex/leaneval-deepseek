import Mathlib
import Submission.Work.ZeroFreeTables.P3.AnnulusDiffDefs

namespace Work.ZeroFreeTables.P3

open scoped Classical BigOperators

theorem annulusMass_count_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ R R' : ℝ, 2 ≤ R → R ≤ R' → ∀ ρ : ℝ, 2 ≤ ρ →
      (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0 : ℂ) ρ) (annulusMass χ R R') u)
        ≤ c * ρ * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) := by
  rcases Commons.NumberTheory.Linnik.completedL_ballZeroCount χ hχ hχprim with ⟨c0, hc0⟩
  refine ⟨2 * max c0 0, by positivity, ?_⟩
  intro R R' hR2 hRR' ρ hρ2
  have hρ1 : 1 ≤ ρ := by linarith
  -- The indicator of the ball, weighted by the annulus mass, has finite support.
  have hfin_g : Function.HasFiniteSupport
      (fun u : ℂ => Set.indicator (Metric.closedBall (0 : ℂ) ρ) (annulusMass χ R R') u) := by
    refine (annulusMass_finiteSupport χ hχ R R').subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hf
    apply hu
    by_cases hm : u ∈ Metric.closedBall (0 : ℂ) ρ
    · rwa [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm]
  have hfin_h : Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) ρ)) u : ℤ) : ℝ)) :=
    Commons.NumberTheory.Linnik.divisor_real_finiteSupport χ hχ 0 ρ
  -- Dominate termwise by the divisor over the ball.
  have hstep1 : (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0 : ℂ) ρ) (annulusMass χ R R') u)
      ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) ρ)) u : ℤ) : ℝ) :=
    finsum_le_finsum' hfin_g hfin_h (fun u => indicator_annulusMass_le_divisor χ hχ hRR' ρ u)
  -- Zero-count bound of the completed L-function in the ball of radius `ρ`.
  have hstep2' : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) ρ)) u : ℤ) : ℝ))
      ≤ c0 * (ρ + 1) * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) := by
    simpa using hc0 0 ρ hρ1
  have hX0 : (0:ℝ) ≤ Real.log (ρ + 2) + Real.log (N : ℝ) + 2 := by
    have h1 : (0:ℝ) ≤ Real.log (ρ + 2) := Real.log_nonneg (by linarith)
    have h2 := Commons.NumberTheory.Linnik.log_N_nonneg (N := N)
    linarith
  have hM0 : (0:ℝ) ≤ max c0 0 := le_max_right _ _
  have hc0M : c0 ≤ max c0 0 := le_max_left _ _
  have hρρ : ρ + 1 ≤ 2 * ρ := by linarith
  have hmul : (ρ + 1) * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2)
      ≤ (2 * ρ) * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) :=
    mul_le_mul_of_nonneg_right hρρ hX0
  have hprod : c0 * ((ρ + 1) * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2))
      ≤ (max c0 0) * ((2 * ρ) * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2)) :=
    mul_le_mul hc0M hmul (mul_nonneg (by linarith : (0:ℝ) ≤ ρ + 1) hX0) hM0
  -- Absorb the factor `ρ + 1` into `2 ρ`.
  have hfinal : c0 * (ρ + 1) * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) ≤
      (2 * max c0 0) * ρ * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) := by
    calc
      c0 * (ρ + 1) * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2)
          = c0 * ((ρ + 1) * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2)) := by ring
      _ ≤ (max c0 0) * ((2 * ρ) * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2)) := hprod
      _ = (2 * max c0 0) * ρ * (Real.log (ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  exact le_trans (le_trans hstep1 hstep2') hfinal

end Work.ZeroFreeTables.P3
