import Mathlib

namespace Work.Pert.pert2v2

/-- For `a > 0` and `t ≥ 0` one has `t ^ 2 * exp (-(a * t)) ≤ 2 / a ^ 2`.

The quadratic Taylor bound `exp u ≥ 1 + u + u ^ 2 / 2` (`Real.sum_le_exp_of_nonneg`)
applied at `u = a * t` gives `exp (a * t) ≥ (a * t) ^ 2 / 2`, and multiplying by
`exp (-(a * t))` turns this into `(a ^ 2 / 2) * (t ^ 2 * exp (-(a * t))) ≤ 1`. -/
lemma sq_mul_exp_neg_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-(a * t)) ≤ 2 / a ^ 2 := by
  have hat : 0 ≤ a * t := mul_nonneg ha.le ht
  have hquad : (a * t) ^ 2 / 2 ≤ Real.exp (a * t) := by
    have h := Real.sum_le_exp_of_nonneg hat 3
    simp [Finset.sum_range_succ, Nat.factorial] at h
    linarith [h]
  have h1 : ((a * t) ^ 2 / 2) * Real.exp (-(a * t)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hquad (Real.exp_pos (-(a * t))).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    exact h
  have h3 : 0 < a ^ 2 / 2 := by positivity
  have h2 : (t ^ 2 * Real.exp (-(a * t))) * (a ^ 2 / 2) ≤ 1 := by
    have he : (t ^ 2 * Real.exp (-(a * t))) * (a ^ 2 / 2)
        = ((a * t) ^ 2 / 2) * Real.exp (-(a * t)) := by ring
    rw [he]; exact h1
  have hle : t ^ 2 * Real.exp (-(a * t)) ≤ 1 / (a ^ 2 / 2) := (le_div_iff₀ h3).mpr h2
  calc t ^ 2 * Real.exp (-(a * t)) ≤ 1 / (a ^ 2 / 2) := hle
    _ = 2 / a ^ 2 := by field_simp

/-- Geometric drift bookkeeping.  With `H ≥ 1000 * max 1 M / κ ^ 2`, the accumulated drift
`3 H M exp (-(55/64) κ H)` is at most `1/64`.

The proof substitutes `s = κ H`: the hypothesis gives `1000 * max 1 M ≤ κ s`, hence
`H = s / κ ≤ s ^ 2 / (1000 * max 1 M)`, and it remains to bound
`(3 M / (1000 * max 1 M)) * (s ^ 2 * exp (-(55/64) s))`.  Since `M ≤ max 1 M` the first
factor is at most `3/1000`, and `sq_mul_exp_neg_le` bounds the second by `2 / (55/64) ^ 2`. -/
theorem drift_geom_small {M κ H : ℝ} (hM : 0 < M) (hκ : 0 < κ)
    (hH : 1000 * max 1 M / κ ^ 2 ≤ H) :
    3 * H * (M * Real.exp (-(55 / 64) * (κ * H))) ≤ 1 / 64 := by
  have hκ2 : (0:ℝ) < κ^2 := by positivity
  have hA1 : (1:ℝ) ≤ max 1 M := le_max_left _ _
  have hAM : M ≤ max 1 M := le_max_right _ _
  have hApos : (0:ℝ) < max 1 M := lt_of_lt_of_le one_pos hA1
  have hCpos : (0:ℝ) < 1000 * max 1 M := by positivity
  -- the hypothesis, cleared of the division
  have hCH : 1000 * max 1 M ≤ H * κ^2 := (div_le_iff₀ hκ2).mp hH
  have hHpos : (0:ℝ) < H := lt_of_lt_of_le (div_pos hCpos hκ2) hH
  -- `H` is controlled by `(κ H) ^ 2 / (1000 * max 1 M)`
  have hHle : H ≤ (κ * H)^2 / (1000 * max 1 M) := by
    rw [le_div_iff₀ hCpos]
    nlinarith [hCH, hHpos]
  -- exponential decay of the squared argument
  have hexp_le : (κ * H)^2 * Real.exp (-(55 / 64) * (κ * H)) ≤ 2 / (55/64)^2 := by
    have h := sq_mul_exp_neg_le (a := 55/64) (t := κ * H) (by norm_num) (by positivity)
    simpa only [← neg_mul] using h
  -- the mass prefactor
  have hMC : 3 * M / (1000 * max 1 M) ≤ 3 / 1000 := by
    have h1 : M / (1000 * max 1 M) ≤ (max 1 M) / (1000 * max 1 M) :=
      div_le_div_of_nonneg_right hAM hCpos.le
    have h2 : (max 1 M) / (1000 * max 1 M) = 1 / 1000 := by
      field_simp [hApos.ne']
    have h3 : 3 * M / (1000 * max 1 M) = 3 * (M / (1000 * max 1 M)) := by ring
    rw [h3]
    linarith
  calc 3 * H * (M * Real.exp (-(55 / 64) * (κ * H)))
      = 3 * M * Real.exp (-(55 / 64) * (κ * H)) * H := by ring
    _ ≤ 3 * M * Real.exp (-(55 / 64) * (κ * H)) * ((κ * H)^2 / (1000 * max 1 M)) :=
        mul_le_mul_of_nonneg_left hHle (by positivity)
    _ = (3 * M / (1000 * max 1 M)) * ((κ * H)^2 * Real.exp (-(55 / 64) * (κ * H))) := by ring
    _ ≤ (3 / 1000) * ((κ * H)^2 * Real.exp (-(55 / 64) * (κ * H))) :=
        mul_le_mul_of_nonneg_right hMC (by positivity)
    _ ≤ (3 / 1000) * (2 / (55/64)^2) := mul_le_mul_of_nonneg_left hexp_le (by norm_num)
    _ ≤ 1 / 64 := by norm_num

end Work.Pert.pert2v2
