import Mathlib

namespace Work.NumberTheory.Chen.APSwitchUpper

/-!
# The upper bound `logPad2_L1_upper`

For `2 ≤ u ≤ 4` we must bound the logarithmic factor `log (3 / (u - 1))` from above by
the truncation of the series `log ((1+x)/(1-x)) = 2 ∑_{k ≥ 0} x^{2k+1}/(2k+1)`
(where the tail is majorised by a geometric series).

Setting `x = (4 - u) / (u + 2)` one has `0 ≤ x ≤ 1/2` and
`(1 + x)/(1 - x) = 6 / (2 (u - 1)) = 3 / (u - 1)`, so the whole statement reduces to the
purely analytic inequality `logPad2_aux`.

Mathlib provides the power series `Real.hasSum_log_sub_log_of_abs_lt_one`, so the only
work is to compare the tail of that non-negative series with the geometric series
`∑ (2/5) x^5 (x^2)^k = (2/5) x^5 / (1 - x^2)`.
-/

/-- For `0 ≤ x ≤ 1/2`, the logarithm `log ((1+x)/(1-x))` is bounded above by the first
three terms of its Taylor expansion plus a geometric majorant of the remainder. -/
private lemma logPad2_aux (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.log ((1 + x) / (1 - x)) ≤
      2 * x + (2 / 3 : ℝ) * x ^ 3 + (2 / 5 : ℝ) * x ^ 5 / (1 - x ^ 2) := by
  have hxlt : |x| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have hx2 : x ^ 2 < 1 := by nlinarith [hx0, hx1]
  have hx2nn : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  rw [Real.log_div (by linarith) (by linarith)]
  have hAux := Real.hasSum_log_sub_log_of_abs_lt_one (x := x) hxlt
  set f : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) with hf
  have hS : HasSum f (Real.log (1 + x) - Real.log (1 - x)) := hAux
  have hsum : Summable f := hS.summable
  set g : ℕ → ℝ := fun k => (2 / 5 : ℝ) * x ^ 5 * (x ^ 2) ^ k with hg
  have hg_sum : Summable g := by
    have hgeom : Summable (fun k : ℕ => (x ^ 2) ^ k) :=
      summable_geometric_of_lt_one hx2nn hx2
    have hh := hgeom.mul_left ((2 / 5 : ℝ) * x ^ 5)
    rwa [hg]
  have hf2_sum : Summable (fun k : ℕ => f (k + 2)) := (summable_nat_add_iff 2).2 hsum
  have hgc : ∀ k : ℕ, f (k + 2) ≤ g k := by
    intro k
    have hk : (0 : ℝ) < 2 * ((k + 2 : ℕ) : ℝ) + 1 := by positivity
    have hle1 : (1 : ℝ) / (2 * ((k + 2 : ℕ) : ℝ) + 1) ≤ 1 / 5 := by
      rw [div_le_div_iff₀ hk (by norm_num)]
      push_cast
      linarith
    have hexp : x ^ (2 * (k + 2) + 1) = x ^ 5 * (x ^ 2) ^ k := by
      have h1 : 2 * (k + 2) + 1 = 2 * k + 5 := by ring
      rw [h1, pow_add, pow_mul]; ring
    rw [hf, hg]
    calc (2 : ℝ) * (1 / (2 * ((k + 2 : ℕ) : ℝ) + 1)) * x ^ (2 * (k + 2) + 1)
        ≤ 2 * (1 / 5) * (x ^ 5 * (x ^ 2) ^ k) := by
          rw [hexp]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hle1 (by norm_num)) le_rfl
            (mul_nonneg (pow_nonneg hx0 5) (pow_nonneg hx2nn k)) (by norm_num)
      _ = (2 / 5 : ℝ) * x ^ 5 * (x ^ 2) ^ k := by ring
  have hmono : ∑' k : ℕ, f (k + 2) ≤ ∑' k : ℕ, g k :=
    Summable.tsum_le_tsum hgc hf2_sum hg_sum
  have hgval : ∑' k : ℕ, g k = (2 / 5 : ℝ) * x ^ 5 / (1 - x ^ 2) := by
    rw [hg, tsum_mul_left, tsum_geometric_of_lt_one hx2nn hx2]
    ring
  have hS_eq : Real.log (1 + x) - Real.log (1 - x) =
      2 * x + (2 / 3 : ℝ) * x ^ 3 + ∑' k : ℕ, f (k + 2) := by
    rw [← hS.tsum_eq, ← hsum.sum_add_tsum_nat_add 2]
    have h2' : ∑ i ∈ Finset.range 2, f i = 2 * x + (2 / 3 : ℝ) * x ^ 3 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have hf0 : f 0 = 2 * x := by simp [f]
      have hf1 : f 1 = (2 / 3 : ℝ) * x ^ 3 := by norm_num [f]
      rw [hf0, hf1]
    rw [h2']
  rw [hS_eq, ← hgval]
  linarith [hmono]

theorem logPad2_L1_upper (u : ℝ) (h2 : 2 ≤ u) (h4 : u ≤ 4) :
    Real.log (3 / (u - 1)) ≤ 2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3
      + (2 / 5 : ℝ) * ((4 - u) / (u + 2)) ^ 5 / (1 - ((4 - u) / (u + 2)) ^ 2) := by
  have hx0 : 0 ≤ (4 - u) / (u + 2) := by
    apply div_nonneg <;> linarith
  have hx1 : (4 - u) / (u + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < u + 2) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hkey := logPad2_aux ((4 - u) / (u + 2)) hx0 hx1
  have hlog : Real.log (3 / (u - 1)) =
      Real.log ((1 + (4 - u) / (u + 2)) / (1 - (4 - u) / (u + 2))) := by
    congr 1
    have e1 : (1 : ℝ) + (4 - u) / (u + 2) = 6 / (u + 2) := by field_simp; ring
    have e2 : (1 : ℝ) - (4 - u) / (u + 2) = 2 * (u - 1) / (u + 2) := by field_simp; ring
    rw [e1, e2]
    field_simp
    ring
  rw [hlog]
  exact hkey

end Work.NumberTheory.Chen.APSwitchUpper
