import Mathlib

set_option linter.unusedVariables false

namespace Work.NN.Core

open MeasureTheory Filter ENNReal

/-- Dominated-convergence statement for the `L²`-type energy of a family of
vector-valued functions on `Fin n → ℂ`, which all vanish outside the ball of
radius `ρ` and are uniformly bounded by `B`. -/
theorem tendsto_lintegral_data {n : ℕ} {F : ℕ → Fin n → (Fin n → ℂ) → ℂ}
    {f : Fin n → (Fin n → ℂ) → ℂ} {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB0 : 0 ≤ B)
    (hFm : ∀ m j, Measurable (F m j))
    (hFs : ∀ m j w, ρ ≤ ‖w‖ → F m j w = 0)
    (hB : ∀ m j w, ‖F m j w‖ ≤ B)
    (hconv : ∀ j w, Filter.Tendsto (fun m => F m j w) Filter.atTop (nhds (f j w))) :
    Filter.Tendsto
      (fun m => ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖F m j z‖ ^ 2))
      Filter.atTop (nhds (∫⁻ z : Fin n → ℂ,
        (∑ j : Fin n, ENNReal.ofReal ‖f j z‖ ^ 2))) := by
  classical
  -- The uniform bound for the integrand, valid on the support.
  set c : ℝ≥0∞ := (n : ℝ≥0∞) * ENNReal.ofReal B ^ 2 with hc
  have hcne : c ≠ ∞ := by
    rw [hc]
    apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top n
    · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  -- Dominated convergence with the bound `c` on the ball of radius `ρ`
  -- (outside of which every `F m j` vanishes).
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence
    ((Metric.ball 0 ρ).indicator fun _ => c) ?_ ?_ ?_ ?_
  · -- Measurability of the integrands.
    intro m
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (ENNReal.measurable_ofReal.comp ((hFm m j).norm)).pow_const 2
  · -- Pointwise domination by the bound.
    intro m
    filter_upwards with z
    by_cases hz : z ∈ Metric.ball (0 : Fin n → ℂ) ρ
    · simp only [Set.indicator_of_mem hz]
      have hsum : (∑ j : Fin n, ENNReal.ofReal ‖F m j z‖ ^ 2)
          ≤ ∑ _j : Fin n, ENNReal.ofReal B ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hB m j z)) 2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      simpa only [hc] using hsum
    · rw [Set.indicator_of_notMem hz]
      have hz' : ρ ≤ ‖z‖ := by
        simp only [Metric.mem_ball, dist_zero_right, not_lt] at hz
        exact hz
      have h0 : ∀ j, F m j z = 0 := fun j => hFs m j z hz'
      simp [h0]
  · -- The bound has finite integral (the ball has finite measure).
    rw [lintegral_indicator_const measurableSet_ball]
    exact ENNReal.mul_ne_top hcne (ne_of_lt measure_ball_lt_top)
  · -- Pointwise convergence of the integrands.
    filter_upwards with z
    refine tendsto_finsetSum Finset.univ fun j _ => ?_
    have hcont : ContinuousAt (fun u : ℂ => ENNReal.ofReal ‖u‖ ^ 2) (f j z) :=
      ((ENNReal.continuous_pow 2).comp
        (ENNReal.continuous_ofReal.comp continuous_norm)).continuousAt
    exact hcont.tendsto.comp (hconv j z)

end Work.NN.Core
