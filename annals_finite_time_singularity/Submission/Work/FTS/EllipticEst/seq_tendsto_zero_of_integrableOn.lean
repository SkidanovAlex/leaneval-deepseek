import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Have

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Filter
open scoped Topology ENNReal

/-- An integrable function on `(0,∞)` assumes values tending to `0` along a sequence tending to
`∞`: for every `k` the set `{z ∈ (k,∞) : |g z| ≥ 1/k}` has finite measure (otherwise the integral
of `|g|` would diverge), so its complement in `(k,∞)` is non-empty. -/
theorem seq_tendsto_zero_of_integrableOn {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Ioi (0 : ℝ))) :
    ∃ u : ℕ → ℝ, Filter.Tendsto u Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun k : ℕ => g (u k)) Filter.atTop (nhds (0 : ℝ)) := by
  have hfin : ∫⁻ x in Set.Ioi (0 : ℝ), ‖g x‖ₑ < ∞ := hg.2
  -- For each `n`, some `x > n` has `‖g x‖ < 1/(n+1)`; otherwise `‖g‖ ≥ 1/(n+1)` on the
  -- (infinite-measure) set `(n,∞)`, forcing the integral of `‖g‖` over `(0,∞)` to diverge.
  have hne : ∀ n : ℕ, ∃ x : ℝ, (n : ℝ) < x ∧ ‖g x‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    simp only [Real.norm_eq_abs] at h
    have hc : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h3 : ∫⁻ x in Set.Ioi (n : ℝ), ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤
        ∫⁻ x in Set.Ioi (n : ℝ), ‖g x‖ₑ := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro x hx
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (h x hx)
    rw [setLIntegral_const, Real.volume_Ioi,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc))] at h3
    have htop : ∫⁻ x in Set.Ioi (0 : ℝ), ‖g x‖ₑ = ⊤ :=
      le_antisymm le_top (le_trans h3 (lintegral_mono_set fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢
        exact lt_of_le_of_lt (Nat.cast_nonneg n) hx))
    rw [htop] at hfin
    exact (lt_irrefl ⊤) hfin
  set u : ℕ → ℝ := fun n => Classical.choose (hne n)
  have hu_gt : ∀ n : ℕ, (n : ℝ) < u n := fun n => (Classical.choose_spec (hne n)).1
  have hu_abs : ∀ n : ℕ, ‖g (u n)‖ < 1 / ((n : ℝ) + 1) :=
    fun n => (Classical.choose_spec (hne n)).2
  refine ⟨u, ?_, ?_⟩
  · rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    refine ⟨N, fun n hn => ?_⟩
    have hb : b < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
    exact le_of_lt (lt_trans hb (hu_gt n))
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N : ℝ) + 1)
      have : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hn
      linarith
    rw [dist_eq_norm, sub_zero]
    linarith [hu_abs n, hle, hN]

end Work.FTS.EllipticEst
