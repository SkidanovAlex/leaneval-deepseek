import Mathlib

namespace Work.ZeroFreeTables.P9

/-- For `0 ≤ x ≤ 1/2` we have `1 + x ≤ 12 (1 - x)^3`. -/
lemma one_add_le_twelve_mul_cube {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/2) :
    1 + x ≤ 12 * (1 - x)^3 := by
  have h1 : (0 : ℝ) ≤ 1 - 2 * x := by linarith
  have h2 : (0 : ℝ) ≤ 6 * x^2 - 15 * x + 11 := by nlinarith [sq_nonneg x]
  have key : 12 * (1 - x)^3 - (1 + x) = (1 - 2 * x) * (6 * x^2 - 15 * x + 11) := by ring
  linarith [mul_nonneg h1 h2]

/-- Solving the linear relation satisfied by `∑ k^2 x^k`. -/
lemma sq_geom_solve {x S : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/2)
    (hrel : S = x * (S + 2 * (x / (1 - x)^2) + (1 - x)⁻¹)) :
    S = x * (1 + x) / (1 - x)^3 := by
  have hpos : 0 < 1 - x := by linarith
  have h1x : (1 : ℝ) - x ≠ 0 := ne_of_gt hpos
  rw [eq_div_iff (pow_ne_zero 3 h1x)]
  have h := hrel
  field_simp [h1x] at h
  ring_nf at h ⊢
  linarith [h]

theorem tsum_sq_mul_geometric_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/2) :
    (∑' k : ℕ, (k : ℝ)^2 * x^k) ≤ 12 * x := by
  have hx1 : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]; linarith
  have hpos : 0 < 1 - x := by linarith
  have hS : Summable (fun n : ℕ => (n : ℝ)^2 * x^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hx1
  have hS1 : Summable (fun n : ℕ => (n : ℝ) * x^n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx1).summable
  have hSg : Summable (fun n : ℕ => x^n) :=
    (hasSum_geometric_of_norm_lt_one hx1).summable
  have hshift : (∑' n : ℕ, (n : ℝ)^2 * x^n)
      = ∑' n : ℕ, ((n : ℝ) + 1)^2 * x^(n + 1) := by
    have h := hS.tsum_eq_zero_add
    simpa using h
  have hinner : (∑' n : ℕ, ((n : ℝ) + 1)^2 * x^n)
      = (∑' n : ℕ, (n : ℝ)^2 * x^n) + 2 * (∑' n : ℕ, (n : ℝ) * x^n)
          + (∑' n : ℕ, x^n) := by
    calc (∑' n : ℕ, ((n : ℝ) + 1)^2 * x^n)
        = ∑' n : ℕ, ((n : ℝ)^2 * x^n + (2 * ((n : ℝ) * x^n) + x^n)) :=
          tsum_congr (fun n => by ring)
      _ = (∑' n : ℕ, (n : ℝ)^2 * x^n) + (∑' n : ℕ, (2 * ((n : ℝ) * x^n) + x^n)) :=
          Summable.tsum_add hS ((hS1.mul_left 2).add hSg)
      _ = (∑' n : ℕ, (n : ℝ)^2 * x^n)
            + (2 * (∑' n : ℕ, (n : ℝ) * x^n) + (∑' n : ℕ, x^n)) := by
          rw [Summable.tsum_add (hS1.mul_left 2) hSg, tsum_mul_left]
      _ = (∑' n : ℕ, (n : ℝ)^2 * x^n) + 2 * (∑' n : ℕ, (n : ℝ) * x^n)
            + (∑' n : ℕ, x^n) := by ring
  have hsplit : (∑' n : ℕ, ((n : ℝ) + 1)^2 * x^(n + 1))
      = x * ((∑' n : ℕ, (n : ℝ)^2 * x^n) + 2 * (x / (1 - x)^2) + (1 - x)⁻¹) := by
    have hcongr : ∀ n : ℕ, ((n : ℝ) + 1)^2 * x^(n + 1) = x * (((n : ℝ) + 1)^2 * x^n) := by
      intro n; rw [pow_succ]; ring
    rw [tsum_congr hcongr, tsum_mul_left, hinner,
        tsum_coe_mul_geometric_of_norm_lt_one hx1, tsum_geometric_of_norm_lt_one hx1]
  have hval : (∑' n : ℕ, (n : ℝ)^2 * x^n) = x * (1 + x) / (1 - x)^3 :=
    sq_geom_solve hx0 hx (hshift.trans hsplit)
  rw [hval]
  have h12 : (1 + x) / (1 - x)^3 ≤ 12 := by
    rw [div_le_iff₀ (pow_pos hpos 3)]
    exact one_add_le_twelve_mul_cube hx0 hx
  calc x * (1 + x) / (1 - x)^3 = x * ((1 + x) / (1 - x)^3) := by ring
    _ ≤ x * 12 := mul_le_mul_of_nonneg_left h12 hx0
    _ = 12 * x := by ring

end Work.ZeroFreeTables.P9
