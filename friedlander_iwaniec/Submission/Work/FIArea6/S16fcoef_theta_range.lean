import Mathlib

namespace Work.FIArea6

/-- Termwise bound: `(1+x^2)^{-1} ≤ 2/(1+x)^2` for `x ≥ 0`.  It is equivalent to
`(1+x)^2 ≤ 2(1+x^2)`, i.e. to `(1-x)^2 ≥ 0`. -/
lemma one_add_sq_inv_le (x : ℝ) (hx : 0 ≤ x) :
    (1 + x ^ 2)⁻¹ ≤ 2 / (1 + x) ^ 2 := by
  have key : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith [sq_nonneg (1 - x)]
  have hA : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hB : (0 : ℝ) < (1 + x) ^ 2 := by
    have : (0 : ℝ) < 1 + x := by linarith
    positivity
  rw [inv_eq_one_div]
  have e1 : 1 / (1 + x ^ 2) = (1 + x) ^ 2 / ((1 + x) ^ 2 * (1 + x ^ 2)) := by field_simp
  have e2 : 2 / (1 + x) ^ 2 = (2 * (1 + x ^ 2)) / ((1 + x) ^ 2 * (1 + x ^ 2)) := by field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key (le_of_lt (mul_pos hB hA))

/-- Telescoping step: `2/(1+θ(i+1))^2 ≤ (2/θ)·((1+θ i)^{-1} - (1+θ(i+1))^{-1})`, since
the right-hand side equals `2/((1+θ i)(1+θ(i+1)))` and `1+θ i ≤ 1+θ(i+1)`. -/
lemma telesc_step (θ : ℝ) (hθ : 0 < θ) (i : ℕ) :
    2 / (1 + θ * (((i + 1 : ℕ)) : ℝ)) ^ 2
      ≤ (2 / θ) * ((1 + θ * (i : ℝ))⁻¹ - (1 + θ * (((i + 1 : ℕ)) : ℝ))⁻¹) := by
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hi1 : (((i + 1 : ℕ)) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [hi1]
  have hb : (0 : ℝ) < 1 + θ * ((i : ℝ) + 1) := by
    nlinarith [mul_nonneg (le_of_lt hθ) hi]
  have hba : 1 + θ * ((i : ℝ) + 1) = (1 + θ * (i : ℝ)) + θ := by ring
  rw [inv_eq_one_div, inv_eq_one_div, hba]
  field_simp
  nlinarith [sq_nonneg θ]

theorem S16fcoef_theta_range {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (L : ℕ) :
    θ * ∑ n ∈ Finset.range (L + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹ ≤ 5 := by
  have hterm1 : ∀ n : ℕ, (1 + (θ * (n : ℝ)) ^ 2)⁻¹ ≤ 2 / (1 + θ * (n : ℝ)) ^ 2 := by
    intro n
    exact one_add_sq_inv_le (θ * (n : ℝ)) (mul_nonneg (le_of_lt hθ) (Nat.cast_nonneg n))
  have htel : ∑ i ∈ Finset.range L, 2 / (1 + θ * (((i + 1 : ℕ)) : ℝ)) ^ 2 ≤ 2 / θ := by
    have hs : ∑ i ∈ Finset.range L, 2 / (1 + θ * (((i + 1 : ℕ)) : ℝ)) ^ 2
            ≤ ∑ i ∈ Finset.range L,
                (2 / θ) * ((1 + θ * (i : ℝ))⁻¹ - (1 + θ * (((i + 1 : ℕ)) : ℝ))⁻¹) :=
      Finset.sum_le_sum (fun i _ => telesc_step θ hθ i)
    have hcalc : ∑ i ∈ Finset.range L,
                (2 / θ) * ((1 + θ * (i : ℝ))⁻¹ - (1 + θ * (((i + 1 : ℕ)) : ℝ))⁻¹)
               = (2 / θ) * ((1 + θ * (((0 : ℕ)) : ℝ))⁻¹ - (1 + θ * ((L : ℕ) : ℝ))⁻¹) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub']
    have hbound : (2 / θ) * ((1 + θ * (((0 : ℕ)) : ℝ))⁻¹ - (1 + θ * ((L : ℕ) : ℝ))⁻¹) ≤ 2 / θ := by
      have hg0 : (1 + θ * (((0 : ℕ)) : ℝ))⁻¹ = 1 := by norm_num
      have hgL : 0 < (1 + θ * ((L : ℕ) : ℝ))⁻¹ := by
        apply inv_pos.mpr; positivity
      rw [hg0]
      have hle1 : (1 - (1 + θ * ((L : ℕ) : ℝ))⁻¹) ≤ 1 := by linarith
      have h2θ : (0 : ℝ) ≤ 2 / θ := by positivity
      calc (2 / θ) * (1 - (1 + θ * ((L : ℕ) : ℝ))⁻¹) ≤ (2 / θ) * 1 :=
            mul_le_mul_of_nonneg_left hle1 h2θ
        _ = 2 / θ := by ring
    linarith [hs, hcalc, hbound]
  have hsum : ∑ n ∈ Finset.range (L + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹ ≤ 2 + 2 / θ := by
    have h1 : ∑ n ∈ Finset.range (L + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹
            ≤ ∑ n ∈ Finset.range (L + 1), 2 / (1 + θ * (n : ℝ)) ^ 2 :=
      Finset.sum_le_sum (fun n _ => hterm1 n)
    have h2 : ∑ n ∈ Finset.range (L + 1), 2 / (1 + θ * (n : ℝ)) ^ 2 ≤ 2 + 2 / θ := by
      rw [Finset.sum_range_succ' (fun n : ℕ => 2 / (1 + θ * (n : ℝ)) ^ 2) L]
      have hf0 : 2 / (1 + θ * ((↑(0 : ℕ) : ℝ))) ^ 2 = 2 := by norm_num
      rw [hf0]
      linarith [htel]
    linarith [h1, h2]
  have hfin : θ * (2 + 2 / θ) ≤ 5 := by
    have e : θ * (2 + 2 / θ) = 2 * θ + 2 := by field_simp
    rw [e]; linarith
  calc θ * ∑ n ∈ Finset.range (L + 1), (1 + (θ * (n : ℝ)) ^ 2)⁻¹
      ≤ θ * (2 + 2 / θ) := mul_le_mul_of_nonneg_left hsum (le_of_lt hθ)
    _ ≤ 5 := hfin

end Work.FIArea6
