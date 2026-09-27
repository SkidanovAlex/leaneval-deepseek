import Mathlib
import Submission.Work.EQ.Fatou.ParsevalAux
import Submission.Work.EQ.Fatou.integral_partialSum_normSq
import Submission.Work.EQ.Fatou.tendsto_integral_partialSum_normSq

namespace Work.EQ.Fatou

open Complex MeasureTheory Filter

theorem integral_normSq_eq_tsum {h : ℂ → ℂ} {a : ℕ → ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hR : ρ < R)
    (ha : ∀ z ∈ Metric.ball (0:ℂ) R, HasSum (fun n => a n * z^n) (h z)) :
    ∫ θ in (0:ℝ)..2 * Real.pi, ‖h (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖ ^ 2
      = 2 * Real.pi * ∑' n : ℕ, ‖a n‖ ^ 2 * ρ ^ (2 * n) := by
  have hsum : Summable (fun n => ‖a n‖^2 * ρ^(2*n)) :=
    (summable_norm_mul_pow hρ hR (fun z hz => ⟨h z, ha z hz⟩)).2
  have hT : Tendsto (fun N => ∑ n ∈ Finset.range N, ‖a n‖^2 * ρ^(2*n)) atTop
      (nhds (∑' n : ℕ, ‖a n‖^2 * ρ^(2*n))) := hsum.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun N => 2 * Real.pi * ∑ n ∈ Finset.range N, ‖a n‖^2 * ρ^(2*n)) atTop
      (nhds (2 * Real.pi * ∑' n : ℕ, ‖a n‖^2 * ρ^(2*n))) :=
    hT.const_mul (2 * Real.pi)
  have hfun : (fun N => ∫ θ in (0:ℝ)..2 * Real.pi,
        ‖∑ n ∈ Finset.range N, a n * (ρ * Complex.exp ((θ:ℂ) * Complex.I))^n‖^2)
      = fun N => 2 * Real.pi * ∑ n ∈ Finset.range N, ‖a n‖^2 * ρ^(2*n) := by
    funext N
    exact integral_partialSum_normSq a ρ N
  have hE := tendsto_integral_partialSum_normSq hρ hR ha
  rw [hfun] at hE
  exact tendsto_nhds_unique hE h2

end Work.EQ.Fatou
