import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- Summability over `ℕ` of the positive half of the majorant
`n ↦ (1 + |a n|)^{-2}` (`a > 0`). -/
private lemma summable_rpow_inv_two_nat (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => (1 + |a * ((n : ℤ) : ℝ)|) ^ (-(2 : ℝ))) := by
  -- `n ↦ (a n + 1)^{-2} = a^{-2} · ((n + a^{-1})^2)^{-1}`, a shifted `p`-series with `p = 2 > 1`.
  have hbase : Summable (fun n : ℕ => (((n : ℝ) + a⁻¹) ^ 2)⁻¹) := by
    have h := (Real.summable_one_div_nat_add_rpow a⁻¹ 2).mpr (by norm_num)
    refine h.congr fun n => ?_
    simp only [one_div, Real.rpow_two, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + a⁻¹)]
  refine (hbase.mul_left ((a^2)⁻¹)).congr fun n => ?_
  rw [Int.cast_natCast, abs_of_nonneg (by positivity : (0:ℝ) ≤ a * (n:ℝ))]
  have h1 : (0:ℝ) < 1 + a * (n:ℝ) := by positivity
  have ha' : a ≠ 0 := ne_of_gt ha
  rw [Real.rpow_neg (le_of_lt h1), Real.rpow_two,
      show (1 + a * (n:ℝ)) = a * ((n:ℝ) + a⁻¹) by field_simp; ring, mul_pow, mul_inv]

/-- Summability over `ℕ` of the negative half of the majorant,
`n ↦ (1 + |a (-(n+1))|)^{-2} = (1 + a(n+1))^{-2}` (`a > 0`). -/
private lemma summable_rpow_inv_two_neg (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => (1 + |a * (((-(↑n + 1) : ℤ)) : ℝ)|) ^ (-(2 : ℝ))) := by
  -- `n ↦ (a (n+1) + 1)^{-2} = a^{-2} · ((n + (1 + a^{-1}))^2)^{-1}`.
  have hbase : Summable (fun n : ℕ => ((((n : ℝ) + 1) + a⁻¹) ^ 2)⁻¹) := by
    have h := (Real.summable_one_div_nat_add_rpow (1 + a⁻¹) 2).mpr (by norm_num)
    refine h.congr fun n => ?_
    simp only [one_div, Real.rpow_two,
      show (n : ℝ) + (1 + a⁻¹) = ((n : ℝ) + 1) + a⁻¹ by ring,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n : ℝ) + 1) + a⁻¹)]
  refine (hbase.mul_left ((a^2)⁻¹)).congr fun n => ?_
  rw [Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast, mul_neg, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ a * ((n:ℝ) + 1))]
  have h1 : (0:ℝ) < 1 + a * ((n:ℝ) + 1) := by positivity
  have ha' : a ≠ 0 := ne_of_gt ha
  rw [Real.rpow_neg (le_of_lt h1), Real.rpow_two,
      show (1 + a * ((n:ℝ) + 1)) = a * (((n:ℝ)+1) + a⁻¹) by field_simp; ring, mul_pow, mul_inv]

/-- The majorant `l ↦ (1 + |a l|)^{-2}` is summable over `ℤ` for `a > 0`.

Proof route: the substitution `ℤ ≃ ℕ ⊕ ℕ` (`Equiv.intEquivNatSumNat`, sending `n ≥ 0` to `Sum.inl n`
and `-(n+1)` to `Sum.inr n`) together with `Summable.tsum_sum` reduces this to the two `ℕ`-series
`∑_n (1 + a n)^{-2}` and `∑_n (1 + a(n+1))^{-2}`, and these converge by the integral test
`AntitoneOn.summable_of_integrableOn_Ioi_zero` applied to `t ↦ (1 + a t)^{-2}` (which is antitone,
nonnegative and integrable on `(0,∞)`). -/
theorem int_summable_rpow_inv_two (a : ℝ) (ha : 0 < a) :
    Summable (fun l : ℤ => (1 + |a * (l : ℝ)|) ^ (-(2 : ℝ))) :=
  -- Split the `ℤ`-sum into its nonnegative and strictly negative halves.
  Summable.of_nat_of_neg_add_one (summable_rpow_inv_two_nat a ha)
    (summable_rpow_inv_two_neg a ha)

end Work.BourgainPlan.IonescuWainger
