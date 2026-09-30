import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

open Filter

/-- For every `δ > 0` there is a large `B ≥ 8` with `(1 + B²/2) * exp(-B²/2) ≤ δ`.
This is the elementary fact that `(1 + t) * exp(-t) → 0` along the parabola `t = B²/2`. -/
theorem exists_B_tail (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 8 ≤ B ∧ (1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 2)) ≤ δ := by
  -- `B ↦ B²/2` tends to `atTop`
  have hsq : Filter.Tendsto (fun B : ℝ => B ^ 2 / 2) Filter.atTop Filter.atTop := by
    have h : Filter.Tendsto (fun B : ℝ => B * B) Filter.atTop Filter.atTop :=
      tendsto_id.atTop_mul_atTop₀ tendsto_id
    have h2 := (tendsto_const_mul_atTop_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)).mpr h
    refine h2.congr' ?_
    filter_upwards with B
    ring
  -- the two summands tend to `0`
  have h1 : Filter.Tendsto (fun B : ℝ => (B ^ 2 / 2) * Real.exp (-(B ^ 2 / 2)))
      Filter.atTop (nhds 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hsq
    simpa [Function.comp_def, pow_one] using this
  have h2 : Filter.Tendsto (fun B : ℝ => Real.exp (-(B ^ 2 / 2))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq
  have hadd : Filter.Tendsto
      (fun B : ℝ => (B ^ 2 / 2) * Real.exp (-(B ^ 2 / 2)) + Real.exp (-(B ^ 2 / 2)))
      Filter.atTop (nhds 0) := by
    simpa using h1.add h2
  -- hence the whole expression tends to `0`
  have hmain : Filter.Tendsto (fun B : ℝ => (1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 2)))
      Filter.atTop (nhds 0) := by
    refine hadd.congr' ?_
    filter_upwards with B
    ring
  -- pick a point where it is below `δ` and at least `8`
  have hevent : ∀ᶠ B : ℝ in Filter.atTop,
      (1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 2)) < δ := by
    simpa only [Set.mem_Iio] using hmain.eventually (Iio_mem_nhds hδ)
  obtain ⟨B, hBlt, hBge⟩ := (hevent.and (eventually_ge_atTop 8)).exists
  exact ⟨B, hBge, le_of_lt hBlt⟩

end Work.BMF.mr_core
