import Mathlib

namespace Work.LT

/-- `w! ≥ (w/e)^w`, i.e. `w^w / w! ≤ e^w`, from the degree-`w` term of the
exponential series. -/
lemma pow_div_factorial_le_exp (w : ℕ) :
    (w : ℝ) ^ w / (w.factorial : ℝ) ≤ Real.exp w := by
  have hsum := Real.sum_le_exp_of_nonneg (x := (w : ℝ)) (by positivity) (w + 1)
  have hmem : w ∈ Finset.range (w + 1) := Finset.mem_range.mpr (Nat.lt_succ_self w)
  have hnonneg : ∀ i ∈ Finset.range (w + 1),
      0 ≤ (w : ℝ) ^ i / (i.factorial : ℝ) := by
    intro i _
    positivity
  exact (Finset.single_le_sum hnonneg hmem).trans hsum

/-- `(n choose w) ≤ (n e / w)^w` for `w > 0`. -/
theorem gb_choose_le_exp_pow (n w : ℕ) (hw : 0 < w) :
    (n.choose w : ℝ) ≤ ((n : ℝ) * Real.exp 1 / w) ^ w := by
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  -- Step 1: `n.choose w ≤ n^w / w!`.
  have hchoose : (n.choose w : ℝ) ≤ (n : ℝ) ^ w / (w.factorial : ℝ) :=
    Nat.choose_le_pow_div w n
  -- Step 2: `w^w / w! ≤ (e)^w`.
  have hfact : (w : ℝ) ^ w / (w.factorial : ℝ) ≤ (Real.exp 1) ^ w := by
    have h := pow_div_factorial_le_exp w
    have hexp : Real.exp (w : ℝ) = (Real.exp 1) ^ w := by
      rw [← Real.exp_nat_mul 1 w]
      norm_num
    rwa [hexp] at h
  -- Step 3: divide by `w^w` to get `1/w! ≤ e^w / w^w`.
  have hle1 : (1 : ℝ) / (w.factorial : ℝ) ≤ (Real.exp 1) ^ w / (w : ℝ) ^ w := by
    have hww : (w : ℝ) ^ w ≠ 0 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hfact
      (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (w : ℝ) ^ w))
    calc (1 : ℝ) / (w.factorial : ℝ)
        = ((w : ℝ) ^ w)⁻¹ * ((w : ℝ) ^ w / (w.factorial : ℝ)) := by
          field_simp
      _ ≤ ((w : ℝ) ^ w)⁻¹ * (Real.exp 1) ^ w := hmul
      _ = (Real.exp 1) ^ w / (w : ℝ) ^ w := by
          field_simp
  calc (n.choose w : ℝ)
      ≤ (n : ℝ) ^ w / (w.factorial : ℝ) := hchoose
    _ = (n : ℝ) ^ w * ((1 : ℝ) / (w.factorial : ℝ)) := by ring
    _ ≤ (n : ℝ) ^ w * ((Real.exp 1) ^ w / (w : ℝ) ^ w) :=
        mul_le_mul_of_nonneg_left hle1 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ w)
    _ = ((n : ℝ) * Real.exp 1 / w) ^ w := by
        rw [div_pow, mul_pow, mul_div_assoc]

end Work.LT
