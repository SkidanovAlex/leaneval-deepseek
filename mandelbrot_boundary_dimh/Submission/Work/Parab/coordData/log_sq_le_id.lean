import Mathlib

namespace Work.Parab.coordData

theorem log_sq_le_id (c : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t : ℝ, M ≤ t → c * (1 + Real.log (2 + t)) ^ 2 ≤ t := by
  -- Step 1: the map `t ↦ (1 + log (2 + t))^2 / t` tends to `0` at `+∞`.
  have hlim : Filter.Tendsto (fun t : ℝ => (1 + Real.log (2 + t)) ^ 2 / t)
      Filter.atTop (nhds 0) := by
    -- `log^2` term
    have h2 : Filter.Tendsto (fun t : ℝ => Real.log (2 + t) ^ 2 / t)
        Filter.atTop (nhds 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 2 one_ne_zero).comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (2:ℝ) (f := fun t : ℝ => t)
          Filter.tendsto_id)
      refine h.congr' ?_
      filter_upwards with t
      simp only [Function.comp_apply, one_mul]
      rw [show t + 2 + -2 = t by ring, show 2 + t = t + 2 by ring]
    -- `log` term
    have h1 : Filter.Tendsto (fun t : ℝ => Real.log (2 + t) / t)
        Filter.atTop (nhds 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (2:ℝ) (f := fun t : ℝ => t)
          Filter.tendsto_id)
      refine h.congr' ?_
      filter_upwards with t
      simp only [Function.comp_apply, pow_one, one_mul]
      rw [show t + 2 + -2 = t by ring, show 2 + t = t + 2 by ring]
    -- `1 / t` term
    have hinv : Filter.Tendsto (fun t : ℝ => (1:ℝ) / t) Filter.atTop (nhds 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    have hsum := (h2.add (h1.const_mul 2)).add hinv
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
    field_simp
    ring
  rcases le_or_gt c 0 with hc | hc
  · -- For `c ≤ 0` the left side is nonpositive while `t ≥ 1 ≥ 0`.
    refine ⟨1, le_refl 1, fun t ht => ?_⟩
    have ht0 : (0:ℝ) ≤ t := le_trans zero_le_one ht
    have hsq : (0:ℝ) ≤ (1 + Real.log (2 + t)) ^ 2 := sq_nonneg _
    have hle := mul_nonpos_of_nonpos_of_nonneg hc hsq
    linarith
  · -- For `c > 0`, use the limit to get `(1 + log (2 + t))^2 / t < 1/c` eventually.
    have hpos : (0:ℝ) < 1 / c := by positivity
    have hev : ∀ᶠ t : ℝ in Filter.atTop, (1 + Real.log (2 + t)) ^ 2 / t < 1 / c :=
      hlim.eventually (Iio_mem_nhds hpos)
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max a 1, le_max_right _ _, ?_⟩
    intro t ht
    have hta : a ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : (1:ℝ) ≤ t := le_trans (le_max_right _ _) ht
    have htpos : (0:ℝ) < t := by linarith
    have hLt : (1 + Real.log (2 + t)) ^ 2 < t / c := by
      have h := ha t hta
      rw [div_lt_iff₀ htpos] at h
      rwa [show (1 / c) * t = t / c by ring] at h
    have hmul := mul_lt_mul_of_pos_left hLt hc
    have hcancel : c * (t / c) = t := by field_simp
    linarith [hmul, hcancel.le, hcancel.ge]

end Work.Parab.coordData
