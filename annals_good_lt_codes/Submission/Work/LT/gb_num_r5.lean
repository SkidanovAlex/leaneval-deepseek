import Mathlib
import Submission.Work.LT.gb_num_defs

namespace Work.LT

/-- `((2:ℝ)^(-k/8))^8 = 2^(-k)` for a real exponent `k`. -/
lemma two_rpow_pow8 (k : ℝ) : ((2:ℝ)^(-k/8))^8 = (2:ℝ)^(-k) := by
  rw [← Real.rpow_natCast ((2:ℝ)^(-k/8)) 8, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

/-- If `1 ≤ 2^k * c^8` and `0 ≤ c`, then `2^(-k/8) ≤ c`: raising the desired inequality to the
8th power reduces it to `2^(-k) ≤ c^8`. -/
lemma rpow_neg_div_eight_le (k : ℕ) (c : ℝ) (hc : 0 ≤ c) (h : 1 ≤ (2:ℝ)^k * c^8) :
    (2:ℝ) ^ (-(k:ℝ)/8) ≤ c := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hpos : (0:ℝ) < (2:ℝ)^k := by positivity
  have hk : (2:ℝ)^(-(k:ℝ)) ≤ c^8 := by
    rw [Real.rpow_neg h2, Real.rpow_natCast]
    have h' : (1:ℝ) / (2:ℝ)^k ≤ c^8 := (div_le_iff₀ hpos).mpr (by rw [mul_comm]; exact h)
    rwa [one_div] at h'
  have hgoal : ((2:ℝ)^(-(k:ℝ)/8))^8 ≤ c^8 := by
    rw [two_rpow_pow8]; exact hk
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg h2 _) hc (by norm_num : (8:ℕ) ≠ 0)).mp hgoal

/-- `5/8 ≤ 2^(-5/8)`. -/
lemma five_eighths_le : (5:ℝ)/8 ≤ (2:ℝ)^(-(5:ℝ)/8) := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hx : (0:ℝ) ≤ (5:ℝ)/8 := by norm_num
  have hgoal : ((5:ℝ)/8)^8 ≤ ((2:ℝ)^(-(5:ℝ)/8))^8 := by
    rw [two_rpow_pow8 (5:ℝ), Real.rpow_neg h2]
    norm_num [Real.rpow_natCast]
  exact (pow_le_pow_iff_left₀ hx (Real.rpow_nonneg h2 _) (by norm_num : (8:ℕ) ≠ 0)).mp hgoal

lemma gbNumE_5_1 : gbNumE 5 1 = -(23:ℝ)/8 := by norm_num [gbNumE, gbNumC]
lemma gbNumE_5_2 : gbNumE 5 2 = -(14:ℝ)/8 := by norm_num [gbNumE, gbNumC]
lemma gbNumE_5_3 : gbNumE 5 3 = -(45:ℝ)/8 := by norm_num [gbNumE, gbNumC]
lemma gbNumE_5_4 : gbNumE 5 4 = -(28:ℝ)/8 := by norm_num [gbNumE, gbNumC]
lemma gbNumE_5_5 : gbNumE 5 5 = -(51:ℝ)/8 := by norm_num [gbNumE, gbNumC]

/-- Expansion of a sum over `Finset.Icc 1 5`. -/
lemma sum_expand (f : ℕ → ℝ) :
    (∑ m ∈ (Finset.Icc 1 5 : Finset ℕ), f m) = f 1 + f 2 + f 3 + f 4 + f 5 := by
  have hset : (Finset.Icc 1 5 : Finset ℕ) = ({1,2,3,4,5} : Finset ℕ) := by decide
  rw [hset]
  simp [Finset.sum_insert, show (1:ℕ) ∉ ({2,3,4,5}:Finset ℕ) by decide,
        show (2:ℕ) ∉ ({3,4,5}:Finset ℕ) by decide,
        show (3:ℕ) ∉ ({4,5}:Finset ℕ) by decide,
        show (4:ℕ) ∉ ({5}:Finset ℕ) by decide]
  ring

/-- Numerical bound for `r = 5`: the sum of the five terms `2^(gbNumE 5 m)`, `m = 1..5`, is at
most `2^(-5/8)`. Here `gbNumE 5 m = ((5-4)/8)*m + k(m)*(m-k(m)) - 5*k(m) + 2` with `k(m) = (m+1)/2`,
so the five exponents are `-23/8, -7/4, -45/8, -7/2, -51/8`; the sum is about `0.5543 ≤ 0.6484 = 2^(-5/8)`.
Suggested route: bound `2^(-23/8) ≤ 9/64`, `2^(-7/4) ≤ 3/10`, `2^(-45/8) ≤ 13/640`,
`2^(-7/2) ≤ 141/1600`, `2^(-51/8) ≤ 1/80` (e.g. `2^(-23/8) = 2^(-3)*2^(1/8)` and `2^(1/8) ≤ 9/8` via
`Real.rpow_le_rpow_iff`), sum these to `1797/3200 ≤ 5/8`, and `5/8 ≤ 2^(-5/8)`. -/
theorem gb_num_r5 :
    (∑ m ∈ (Finset.Icc 1 5 : Finset ℕ), (2:ℝ) ^ gbNumE 5 m) ≤ (2:ℝ) ^ (-(5:ℝ)/8) := by
  rw [sum_expand]
  have h1 : (2:ℝ)^(gbNumE 5 1) ≤ 9/64 := by
    rw [gbNumE_5_1]; exact rpow_neg_div_eight_le 23 (9/64) (by norm_num) (by norm_num)
  have h2 : (2:ℝ)^(gbNumE 5 2) ≤ 3/10 := by
    rw [gbNumE_5_2]; exact rpow_neg_div_eight_le 14 (3/10) (by norm_num) (by norm_num)
  have h3 : (2:ℝ)^(gbNumE 5 3) ≤ 13/640 := by
    rw [gbNumE_5_3]; exact rpow_neg_div_eight_le 45 (13/640) (by norm_num) (by norm_num)
  have h4 : (2:ℝ)^(gbNumE 5 4) ≤ 9/100 := by
    rw [gbNumE_5_4]; exact rpow_neg_div_eight_le 28 (9/100) (by norm_num) (by norm_num)
  have h5 : (2:ℝ)^(gbNumE 5 5) ≤ 1/80 := by
    rw [gbNumE_5_5]; exact rpow_neg_div_eight_le 51 (1/80) (by norm_num) (by norm_num)
  have h58 := five_eighths_le
  linarith [h1, h2, h3, h4, h5, h58]

end Work.LT
