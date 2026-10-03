import Mathlib

namespace Work.FIArea4

/-- For `a > 0` and `2^n ≤ 2R`:
`∑_{j ≤ n} (2^j)^a ≤ (2^a/(2^a-1)) (2R)^a`.

The summands are the geometric progression `(2^a)^j`; the closed form
`∑_{j≤n} (2^a)^j = ((2^a)^{n+1}-1)/(2^a-1)` is bounded by
`(2^a)^{n+1}/(2^a-1) = (2^a/(2^a-1)) (2^a)^n`, and `(2^a)^n = (2^n)^a ≤ (2R)^a`
by monotonicity of `x ↦ x^a` on `[0,∞)` together with the hypothesis. -/
lemma sum_rpow_two_pow_le (a : ℝ) (ha : 0 < a) (n R : ℕ)
    (h : (2:ℝ)^n ≤ 2*(R:ℝ)) :
    ∑ j ∈ Finset.range (n+1), ((2:ℝ)^j)^a
      ≤ ((2:ℝ)^a / ((2:ℝ)^a - 1)) * (2*(R:ℝ))^a := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  -- every summand expands to a power of the fixed ratio `2^a`
  have hterm : ∀ j ∈ Finset.range (n+1), ((2:ℝ)^j)^a = ((2:ℝ)^a)^j := fun j _ => by
    calc ((2:ℝ)^j)^a = ((2:ℝ)^(j:ℝ))^a := by rw [Real.rpow_natCast]
      _ = (2:ℝ)^((j:ℝ)*a) := by rw [Real.rpow_mul h2]
      _ = (2:ℝ)^(a*(j:ℝ)) := by ring_nf
      _ = ((2:ℝ)^a)^(j:ℝ) := by rw [Real.rpow_mul h2]
      _ = ((2:ℝ)^a)^j := by rw [Real.rpow_natCast]
  rw [Finset.sum_congr rfl hterm]
  set r : ℝ := (2:ℝ)^a with hr
  have hr1 : 1 < r := by rw [hr]; exact Real.one_lt_rpow (by norm_num) ha
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hrm : 0 < r - 1 := by linarith
  -- the essential numerical input, the hypothesis `2^n ≤ 2R`
  have hkey : r^n ≤ (2*(R:ℝ))^a := by
    have hrn : r^n = ((2:ℝ)^n)^a := by
      rw [hr]
      calc ((2:ℝ)^a)^n = ((2:ℝ)^a)^(n:ℝ) := by rw [Real.rpow_natCast]
        _ = (2:ℝ)^(a*(n:ℝ)) := by rw [Real.rpow_mul h2]
        _ = (2:ℝ)^((n:ℝ)*a) := by ring_nf
        _ = ((2:ℝ)^(n:ℝ))^a := by rw [Real.rpow_mul h2]
        _ = ((2:ℝ)^n)^a := by rw [Real.rpow_natCast]
    rw [hrn]
    exact Real.rpow_le_rpow (by positivity) h ha.le
  rw [geom_sum_eq (ne_of_gt hr1) (n+1)]
  calc (r^(n+1) - 1)/(r-1) ≤ r^(n+1)/(r-1) := by
        apply div_le_div_of_nonneg_right _ hrm.le
        linarith [pow_nonneg hr0.le (n+1)]
    _ ≤ (r/(r-1)) * (2*(R:ℝ))^a := by
        have h2' : r^(n+1) ≤ r * (2*(R:ℝ))^a := by
          rw [pow_succ']
          exact mul_le_mul_of_nonneg_left hkey hr0.le
        calc r^(n+1)/(r-1) ≤ (r * (2*(R:ℝ))^a)/(r-1) :=
              div_le_div_of_nonneg_right h2' hrm.le
          _ = (r/(r-1)) * (2*(R:ℝ))^a := by ring

end Work.FIArea4
