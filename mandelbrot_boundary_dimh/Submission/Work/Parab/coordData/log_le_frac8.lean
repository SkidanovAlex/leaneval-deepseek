import Mathlib

namespace Work.Parab.coordData

/-- `log` is dominated by any positive multiple of the identity, with an explicit threshold:
for every real `c` there is `M ≥ 1` with `c * (1 + log (2 + t)) ≤ t / 8` for all `t ≥ M`. -/
theorem log_le_frac8 (c : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t : ℝ, M ≤ t → c * (1 + Real.log (2 + t)) ≤ t / 8 := by
  -- Step 1: the map `t ↦ (1 + log (2 + t)) / t` tends to `0` at `+∞`.
  have hlim : Filter.Tendsto (fun t : ℝ => (1 + Real.log (2 + t)) / t) Filter.atTop (nhds 0) := by
    have hlog : Filter.Tendsto (fun t : ℝ => Real.log (2 + t) / t) Filter.atTop (nhds 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (2:ℝ) (f := fun t : ℝ => t)
          Filter.tendsto_id)
      refine h.congr' ?_
      filter_upwards with t
      simp only [Function.comp_apply, pow_one, one_mul]
      rw [show (t + 2) + -2 = t by ring, show 2 + t = t + 2 by ring]
    have hinv : Filter.Tendsto (fun t : ℝ => (1:ℝ)/t) Filter.atTop (nhds 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    have hsum : Filter.Tendsto (fun t : ℝ => Real.log (2 + t)/t + 1/t) Filter.atTop (nhds 0) := by
      have := hlog.add hinv
      simpa using this
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
    field_simp
    ring
  rcases le_or_gt c 0 with hc | hc
  · -- For `c ≤ 0` the left side is nonpositive while `t / 8 ≥ 0`.
    refine ⟨2, by norm_num, ?_⟩
    intro t ht
    have hlog0 : 0 ≤ 1 + Real.log (2 + t) := by
      have h2 : (1:ℝ) ≤ 2 + t := by linarith
      have := Real.log_nonneg h2
      linarith
    have h1 : c * (1 + Real.log (2 + t)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hlog0
    have h2 : (0:ℝ) ≤ t/8 := by linarith
    linarith
  · -- For `c > 0`, use the limit to get `(1 + log (2 + t))/t < 1/(8c)` eventually.
    have hpos : (0:ℝ) < 1/(8*c) := by positivity
    have hev : ∀ᶠ t : ℝ in Filter.atTop, (1 + Real.log (2 + t))/t < 1/(8*c) :=
      hlim.eventually (Iio_mem_nhds hpos)
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max a 1, le_max_right _ _, ?_⟩
    intro t ht
    have hta : a ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : (1:ℝ) ≤ t := le_trans (le_max_right _ _) ht
    have htpos : (0:ℝ) < t := by linarith
    have hLt : 1 + Real.log (2 + t) < t/(8*c) := by
      have h := ha t hta
      rw [div_lt_iff₀ htpos] at h
      simpa [one_div, div_eq_inv_mul, mul_comm] using h
    have hmul := mul_lt_mul_of_pos_left hLt hc
    have hsimp : c * (t/(8*c)) = t/8 := by
      field_simp
    rw [hsimp] at hmul
    linarith

end Work.Parab.coordData
