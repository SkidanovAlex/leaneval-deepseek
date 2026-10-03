import Mathlib

namespace Work.FIArea5.S16Hecke

/-- Scalar inequality: for `x ≥ 0` and `α ≥ 1/2`,
`(x/(x+1))^α ≤ (x+3/2)/(x+α+3/2)`. -/
lemma ratio_alpha_le (α x : ℝ) (hα : 1 / 2 ≤ α) (hx : 0 ≤ x) :
    (x / (x + 1)) ^ α ≤ (x + 3 / 2) / (x + α + 3 / 2) := by
  have hα0 : 0 ≤ α := by linarith
  have hαne : α ≠ 0 := by linarith
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rw [← hx0, zero_div, Real.zero_rpow hαne]
    positivity
  · have hu : 0 < (x + 1) / x := by positivity
    have hL : (x / (x + 1)) ^ α = (((x + 1) / x) ^ α)⁻¹ := by
      rw [show x / (x + 1) = ((x + 1) / x)⁻¹ by rw [inv_div],
          Real.inv_rpow (le_of_lt hu)]
    have hR : (x + 3 / 2) / (x + α + 3 / 2) = (1 + α / (x + 3 / 2))⁻¹ := by
      have hden : (x + α + 3 / 2) / (x + 3 / 2) = 1 + α / (x + 3 / 2) := by
        rw [show x + α + 3 / 2 = (x + 3 / 2) + α by ring, add_div,
            div_self (ne_of_gt (by linarith : (0 : ℝ) < x + 3 / 2))]
      rw [← hden, inv_div]
    rw [hL, hR]
    rw [inv_le_inv₀ (Real.rpow_pos_of_pos hu α) (by positivity)]
    have hx1 : (0 : ℝ) < x + 1 := by linarith
    have hlog : (1 : ℝ) / (x + 1) ≤ Real.log ((x + 1) / x) := by
      have h1 : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by
        rw [inv_div]
        field_simp
        ring
      linarith [Real.one_sub_inv_le_log_of_pos hu]
    have h3 : α / (x + 1) ≤ Real.log ((x + 1) / x) * α := by
      have := mul_le_mul_of_nonneg_right hlog hα0
      rwa [one_div, inv_mul_eq_div] at this
    calc 1 + α / (x + 3 / 2) ≤ 1 + α / (x + 1) := by
          have hdx : x + 1 ≤ x + 3 / 2 := by linarith
          have hpos : 0 < x + 1 := hx1
          have hh := div_le_div_of_nonneg_left hα0 hpos hdx
          linarith
      _ ≤ Real.exp (α / (x + 1)) := by
          linarith [Real.add_one_le_exp (α / (x + 1))]
      _ ≤ Real.exp (Real.log ((x + 1) / x) * α) := Real.exp_le_exp_of_le h3
      _ = ((x + 1) / x) ^ α := (Real.rpow_def_of_pos hu α).symm

/-- Scalar inequality: for `x ≥ 0`, `T ≥ 0`, `α ≥ 1/2`,
`(x+3/2)/(x+α+3/2) ≤ sqrt((T²+(x+3/2)²)/(T²+(x+α+3/2)²))`. -/
lemma ratio_sqrt_le (α T x : ℝ) (hα : 1 / 2 ≤ α) (_hT : 0 ≤ T) (hx : 0 ≤ x) :
    (x + 3 / 2) / (x + α + 3 / 2) ≤
      Real.sqrt ((T ^ 2 + (x + 3 / 2) ^ 2) / (T ^ 2 + (x + α + 3 / 2) ^ 2)) := by
  have hα0 : 0 ≤ α := by linarith
  have hc : 0 < x + 3 / 2 := by linarith
  have hd : 0 < x + α + 3 / 2 := by linarith
  have hcd : x + 3 / 2 ≤ x + α + 3 / 2 := by linarith
  have hsq : (x + 3 / 2) ^ 2 ≤ (x + α + 3 / 2) ^ 2 := by
    nlinarith [hc, hcd]
  have hstep : (x + 3 / 2) ^ 2 / (x + α + 3 / 2) ^ 2 ≤
      (T ^ 2 + (x + 3 / 2) ^ 2) / (T ^ 2 + (x + α + 3 / 2) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (x + α + 3 / 2) ^ 2)
          (by positivity : (0:ℝ) < T ^ 2 + (x + α + 3 / 2) ^ 2)]
    nlinarith [sq_nonneg T, hsq]
  calc (x + 3 / 2) / (x + α + 3 / 2)
      = Real.sqrt ((x + 3 / 2) ^ 2 / (x + α + 3 / 2) ^ 2) := by
        rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ (x + 3 / 2) ^ 2),
            Real.sqrt_sq (le_of_lt hc), Real.sqrt_sq (le_of_lt hd)]
    _ ≤ Real.sqrt ((T ^ 2 + (x + 3 / 2) ^ 2) / (T ^ 2 + (x + α + 3 / 2) ^ 2)) :=
        Real.sqrt_le_sqrt hstep

/-- The key scalar estimate: for `x ≥ 0`, `T ≥ 0`, `α ≥ 1/2`,
`(x/(x+1))^α ≤ sqrt((T²+(x+1+1/2)²)/(T²+(x+1+α+1/2)²))`. -/
lemma key_le (α T x : ℝ) (hα : 1 / 2 ≤ α) (hT : 0 ≤ T) (hx : 0 ≤ x) :
    (x / (x + 1)) ^ α ≤
      Real.sqrt ((T ^ 2 + (x + 1 + 1 / 2) ^ 2) / (T ^ 2 + (x + 1 + α + 1 / 2) ^ 2)) := by
  have h1 : x + 1 + 1 / 2 = x + 3 / 2 := by ring
  have h2 : x + 1 + α + 1 / 2 = x + α + 3 / 2 := by ring
  rw [h1, h2]
  linarith [ratio_alpha_le α x hα hx, ratio_sqrt_le α T x hα hT hx]

theorem gammaRatioSeqMono (α T : ℝ) (hα : 1 / 2 ≤ α) (hT : 0 ≤ T) (n : ℕ) :
    (n : ℝ) ^ α * Finset.prod (Finset.range (n + 1))
        (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)))
      ≤ (n + 1 : ℝ) ^ α * Finset.prod (Finset.range (n + 1 + 1))
        (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2))) := by
  set g : ℕ → ℝ := fun j => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)) with hg
  have hPnn : 0 ≤ ∏ j ∈ Finset.range (n + 1), g j :=
    Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _)
  have hb : ((n : ℝ) / ((n : ℝ) + 1)) ^ α ≤ g (n + 1) := by
    simp only [hg, Nat.cast_add, Nat.cast_one]
    exact key_le α T (n : ℝ) hα hT (Nat.cast_nonneg n)
  have hkey : (n : ℝ) ^ α ≤ ((n : ℝ) + 1) ^ α * g (n + 1) := by
    have h1 : (n : ℝ) = ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1)) := by
      exact (mul_div_cancel₀ (n : ℝ) (by positivity : ((n : ℝ) + 1) ≠ 0)).symm
    calc (n : ℝ) ^ α
        = (((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1))) ^ α := by conv_lhs => rw [h1]
      _ = ((n : ℝ) + 1) ^ α * ((n : ℝ) / ((n : ℝ) + 1)) ^ α :=
            Real.mul_rpow (by positivity) (by positivity)
      _ ≤ ((n : ℝ) + 1) ^ α * g (n + 1) :=
            mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by positivity) α)
  have hgoal : (n : ℝ) ^ α * ∏ j ∈ Finset.range (n + 1), g j
      ≤ ((n : ℝ) + 1) ^ α * ((∏ j ∈ Finset.range (n + 1), g j) * g (n + 1)) := by
    calc (n : ℝ) ^ α * ∏ j ∈ Finset.range (n + 1), g j
        ≤ (((n : ℝ) + 1) ^ α * g (n + 1)) * ∏ j ∈ Finset.range (n + 1), g j :=
          mul_le_mul_of_nonneg_right hkey hPnn
      _ = ((n : ℝ) + 1) ^ α * ((∏ j ∈ Finset.range (n + 1), g j) * g (n + 1)) := by ring
  rw [Finset.prod_range_succ g (n + 1)]
  exact hgoal

end Work.FIArea5.S16Hecke
