import Mathlib

namespace Work.KMTContract

/-- A sequence on `ℤ` decaying like `j^{-2}` is absolutely summable.

The comparison sequence is `∑_n 1/(n+1)^2 < ∞` (the `p`-series with `p = 2`); the decisive point
is that on `ℤ` the "positive" and "negative" halves of the index set are both shifts of `ℕ`, and
the majorant `1 / (1 + |j|)^2` is unchanged when `j ↦ -j`. -/
theorem kernel_l1_of_decay {c : ℤ → ℂ} {C : ℝ}
    (hdec : ∀ j : ℤ, ‖c j‖ ≤ C / (1 + |(j : ℝ)|) ^ 2) :
    Summable (fun j : ℤ => ‖c j‖) := by
  -- The comparison series `∑_{n} 1/(n+1)^2` converges.
  have hnat : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
    have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hps
      simpa [Nat.cast_add, Nat.cast_one] using h
    simpa [add_comm] using hshift
  -- Transfer to `ℤ` using the decomposition of `ℤ` into `ℕ` and `-ℕ`.
  have hbase : Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
    refine Summable.of_nat_of_neg ?_ ?_
    · refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hnat
      · positivity
      · have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        simp [abs_of_nonneg hn]
    · refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hnat
      · positivity
      · have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        simp [abs_of_nonneg hn]
  -- Multiply by the constant `C`.
  have hmaj : Summable (fun j : ℤ => C * (1 / (1 + |(j : ℝ)|) ^ 2)) := hbase.mul_left C
  -- Comparison of `‖c j‖` with the majorant.
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
  exact (hdec j).trans (le_of_eq (mul_one_div C _).symm)

end Work.KMTContract
