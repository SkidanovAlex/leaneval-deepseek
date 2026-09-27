import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

open Filter _root_.Topology

/-- Two local sections of `ψ₁` through distinct points of `H0` with the same base value take
distinct values on a small ball around that base value.

If the two sections agreed arbitrarily close to the base value `c = q.2.1 = q'.2.1`, continuity
of the sections at `c` (`IsSection.continuousAt`) would force `q = f c = g c = q'`, against the
assumption `q ≠ q'`.  Hence the agreement set does not accumulate at `c`, and since `c` itself is
not in it the agreement set stays away from a small ball around `c`. -/
theorem sections_distinct {a : ℝ} {h : ℂ → ℂ} {q q' : ChainData} {f g : ℂ → ChainData}
    {ρ ρ' : ℝ} (hq : q ∈ H0 a h) (hq' : q' ∈ H0 a h) (hne : q ≠ q') (h1 : q.2.1 = q'.2.1)
    (hf : IsSection a h f q ρ) (hg : IsSection a h g q' ρ') :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ ∧ ε ≤ ρ' ∧ ∀ u ∈ Metric.ball q.2.1 ε, f u ≠ g u := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ ε, 0 < ε → ε ≤ ρ → ε ≤ ρ' → ∃ u ∈ ball q.2.1 ε, f u = g u`
  have hmin : 0 < min ρ ρ' := lt_min hf.1 hg.1
  -- radii tending to `0`, all `≤ ρ` and `≤ ρ'`
  let e : ℕ → ℝ := fun n => min ρ ρ' * (1 / 2 : ℝ) ^ n
  have he_pos : ∀ n, 0 < e n := fun n => by
    simp only [e]; exact mul_pos hmin (pow_pos (by norm_num) n)
  have he_le_ρ : ∀ n, e n ≤ ρ := fun n => by
    simp only [e]
    calc min ρ ρ' * (1 / 2 : ℝ) ^ n ≤ min ρ ρ' * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hmin.le
      _ = min ρ ρ' := by ring
      _ ≤ ρ := min_le_left _ _
  have he_le_ρ' : ∀ n, e n ≤ ρ' := fun n => by
    simp only [e]
    calc min ρ ρ' * (1 / 2 : ℝ) ^ n ≤ min ρ ρ' * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hmin.le
      _ = min ρ ρ' := by ring
      _ ≤ ρ' := min_le_right _ _
  have he_tend : Tendsto e atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := min ρ ρ')).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
    simpa [e] using hh
  -- choose points `u n` in the ball of radius `e n` where the two sections agree
  choose u hu using fun n => hcon (e n) (he_pos n) (he_le_ρ n) (he_le_ρ' n)
  -- `u n → q.2.1`
  have hu_tend : Tendsto u atTop (𝓝 q.2.1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he_tend
      (fun n => dist_nonneg) (fun n => ?_)
    exact le_of_lt (Metric.mem_ball.mp (hu n).1)
  -- both sections are continuous at the base value, so `f (u n) → f q.2.1` and `g (u n) → g q.2.1`
  have hg_cont : ContinuousAt g q.2.1 := by rw [h1]; exact hg.continuousAt
  have hf_tend : Tendsto (fun n => f (u n)) atTop (𝓝 (f q.2.1)) :=
    Filter.Tendsto.comp hf.continuousAt hu_tend
  have hg_tend : Tendsto (fun n => g (u n)) atTop (𝓝 (g q.2.1)) :=
    Filter.Tendsto.comp hg_cont hu_tend
  have h_eq_fun : (fun n => f (u n)) = (fun n => g (u n)) := funext (fun n => (hu n).2)
  rw [h_eq_fun] at hf_tend
  have hfg : f q.2.1 = g q.2.1 := tendsto_nhds_unique hf_tend hg_tend
  -- hence `q = f q.2.1 = g q.2.1 = g q'.2.1 = q'`, contradiction
  exact hne (by rw [← hf.2.1, hfg, h1, hg.2.1])

end Work.EQ
