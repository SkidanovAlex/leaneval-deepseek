import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The elementary estimate `z^n ≤ (1+z)^n` for `z ≥ 0`. -/
private lemma z_pow_le_one_add {z : ℝ} (hz : 0 < z) (n : ℕ) : z ^ n ≤ (1 + z) ^ n :=
  pow_le_pow_left₀ (le_of_lt hz) (by linarith) n

/-- The single bound that the hypothesis `hA` provides, in the form in which it is used:
`|(1+z)^3 z^j A_j| ≤ 6000 Λ` for every `j ≤ m`.  Indeed `z ≤ 1+z` gives
`(1+z)^3 z^j ≤ (1+z)^{j+3}`. -/
private lemma term_bound {m : ℕ} {z Λ : ℝ} (hz : 0 < z) (A : ℕ → ℝ)
    (hA : ∀ j ≤ m, |(1 + z) ^ (j + 3) * A j| ≤ 6000 * Λ) {j : ℕ} (hj : j ≤ m) :
    |(1 + z) ^ 3 * z ^ j * A j| ≤ 6000 * Λ := by
  have hz3 : (0 : ℝ) ≤ (1 + z) ^ 3 := by positivity
  have hle : (1 + z) ^ 3 * z ^ j ≤ (1 + z) ^ (j + 3) := by
    calc (1 + z) ^ 3 * z ^ j ≤ (1 + z) ^ 3 * (1 + z) ^ j :=
          mul_le_mul_of_nonneg_left (z_pow_le_one_add hz j) hz3
      _ = (1 + z) ^ (j + 3) := by rw [← pow_add, Nat.add_comm]
  calc |(1 + z) ^ 3 * z ^ j * A j|
      = (1 + z) ^ 3 * z ^ j * |A j| := by
        rw [abs_mul, abs_mul]
        rw [abs_of_nonneg hz3, abs_of_nonneg (pow_nonneg (le_of_lt hz) j)]
    _ ≤ (1 + z) ^ (j + 3) * |A j| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ = |(1 + z) ^ (j + 3) * A j| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ (j + 3))]
    _ ≤ 6000 * Λ := hA j hj

/-- Since `w z = (1+z)²/z²`, the factor `(1+z) · w z · z^m` is `(1+z)³ z^{m-2}` for `m ≥ 2`;
together with the bracket `z² A_m + 2m z A_{m-1} + m(m-1) A_{m-2}` this produces a sum of the
three monomials `(1+z)³ z^j A_j` with `j = m, m-1, m-2`, each of which is bounded by `6000 Λ`.
For `m ≤ 1` the coefficients of the two lower terms vanish, so only the `j = m` term survives.
In all cases `m ≤ 4` the sum of the coefficients is at most `21`, giving the constant `200000`. -/
theorem radial_arith {m : ℕ} (hm : m ≤ 4) {z Λ : ℝ} (hz : 0 < z) (hΛ : 0 ≤ Λ)
    (A : ℕ → ℝ) (hA : ∀ j ≤ m, |(1 + z) ^ (j + 3) * A j| ≤ 6000 * Λ) :
    |(1 + z) * Work.Spaces.w z * z ^ m * (z ^ 2 * A m + (2 * (m : ℝ)) * z * A (m - 1)
        + ((m : ℝ) * ((m : ℝ) - 1)) * A (m - 2))| ≤ 200000 * Λ := by
  interval_cases m
  · -- m = 0 : only the top term survives, `(1+z) w z · z² A₀ = (1+z)³ A₀`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 0 * (z ^ 2 * A 0 + 2 * (((0:ℕ):ℝ)) * z * A (0 - 1)
        + (((0:ℕ):ℝ)) * ((((0:ℕ):ℝ)) - 1) * A (0 - 2)) = (1 + z) ^ 3 * A 0 := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have h := term_bound hz A hA (j := 0) (by norm_num)
    simp only [pow_zero, mul_one] at h
    linarith
  · -- m = 1 : `(1+z)³ (z A₁ + 2 A₀)`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 1 * (z ^ 2 * A 1 + 2 * (((1:ℕ):ℝ)) * z * A (1 - 1)
        + (((1:ℕ):ℝ)) * ((((1:ℕ):ℝ)) - 1) * A (1 - 2))
        = (1 + z) ^ 3 * z * A 1 + 2 * ((1 + z) ^ 3 * A 0) := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have hX : |(1 + z) ^ 3 * z * A 1| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 1) (by norm_num)
      simpa [pow_one] using h
    have hY : |2 * ((1 + z) ^ 3 * A 0)| ≤ 12000 * Λ := by
      have h0 : |(1 + z) ^ 3 * A 0| ≤ 6000 * Λ := by
        have h := term_bound hz A hA (j := 0) (by norm_num)
        simpa using h
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    calc |(1 + z) ^ 3 * z * A 1 + 2 * ((1 + z) ^ 3 * A 0)|
        ≤ |(1 + z) ^ 3 * z * A 1| + |2 * ((1 + z) ^ 3 * A 0)| := abs_add_le _ _
      _ ≤ 6000 * Λ + 12000 * Λ := add_le_add hX hY
      _ ≤ 200000 * Λ := by linarith
  · -- m = 2 : `(1+z)³ (z² A₂ + 4 z A₁ + 2 A₀)`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 2 * (z ^ 2 * A 2 + 2 * (((2:ℕ):ℝ)) * z * A (2 - 1)
        + (((2:ℕ):ℝ)) * ((((2:ℕ):ℝ)) - 1) * A (2 - 2)) =
        (1 + z) ^ 3 * z ^ 2 * A 2 + 4 * ((1 + z) ^ 3 * z * A 1)
          + 2 * ((1 + z) ^ 3 * A 0) := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have h2 : |(1 + z) ^ 3 * z ^ 2 * A 2| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 2) (by norm_num); simpa using h
    have h1 : |(1 + z) ^ 3 * z * A 1| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 1) (by norm_num); simpa [pow_one] using h
    have h0 : |(1 + z) ^ 3 * A 0| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 0) (by norm_num); simpa using h
    have h4 : |4 * ((1 + z) ^ 3 * z * A 1)| ≤ 24000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]; linarith
    have h2' : |2 * ((1 + z) ^ 3 * A 0)| ≤ 12000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
    calc |(1 + z) ^ 3 * z ^ 2 * A 2 + 4 * ((1 + z) ^ 3 * z * A 1) + 2 * ((1 + z) ^ 3 * A 0)|
        ≤ |(1 + z) ^ 3 * z ^ 2 * A 2| + |4 * ((1 + z) ^ 3 * z * A 1)|
            + |2 * ((1 + z) ^ 3 * A 0)| := abs_add_three _ _ _
      _ ≤ 6000 * Λ + 24000 * Λ + 12000 * Λ := add_le_add (add_le_add h2 h4) h2'
      _ ≤ 200000 * Λ := by linarith
  · -- m = 3 : `(1+z)³ z (z² A₃ + 6 z A₂ + 6 A₁)`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 3 * (z ^ 2 * A 3 + 2 * (((3:ℕ):ℝ)) * z * A (3 - 1)
        + (((3:ℕ):ℝ)) * ((((3:ℕ):ℝ)) - 1) * A (3 - 2)) =
        (1 + z) ^ 3 * z ^ 3 * A 3 + 6 * ((1 + z) ^ 3 * z ^ 2 * A 2)
          + 6 * ((1 + z) ^ 3 * z * A 1) := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have h3 : |(1 + z) ^ 3 * z ^ 3 * A 3| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 3) (by norm_num); simpa using h
    have h2 : |(1 + z) ^ 3 * z ^ 2 * A 2| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 2) (by norm_num); simpa using h
    have h1 : |(1 + z) ^ 3 * z * A 1| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 1) (by norm_num); simpa [pow_one] using h
    have h6a : |6 * ((1 + z) ^ 3 * z ^ 2 * A 2)| ≤ 36000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]; linarith
    have h6b : |6 * ((1 + z) ^ 3 * z * A 1)| ≤ 36000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]; linarith
    calc |(1 + z) ^ 3 * z ^ 3 * A 3 + 6 * ((1 + z) ^ 3 * z ^ 2 * A 2)
            + 6 * ((1 + z) ^ 3 * z * A 1)|
        ≤ |(1 + z) ^ 3 * z ^ 3 * A 3| + |6 * ((1 + z) ^ 3 * z ^ 2 * A 2)|
            + |6 * ((1 + z) ^ 3 * z * A 1)| := abs_add_three _ _ _
      _ ≤ 6000 * Λ + 36000 * Λ + 36000 * Λ := add_le_add (add_le_add h3 h6a) h6b
      _ ≤ 200000 * Λ := by linarith
  · -- m = 4 : `(1+z)³ z² (z² A₄ + 8 z A₃ + 12 A₂)`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 4 * (z ^ 2 * A 4 + 2 * (((4:ℕ):ℝ)) * z * A (4 - 1)
        + (((4:ℕ):ℝ)) * ((((4:ℕ):ℝ)) - 1) * A (4 - 2)) =
        (1 + z) ^ 3 * z ^ 4 * A 4 + 8 * ((1 + z) ^ 3 * z ^ 3 * A 3)
          + 12 * ((1 + z) ^ 3 * z ^ 2 * A 2) := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have h4 : |(1 + z) ^ 3 * z ^ 4 * A 4| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 4) (by norm_num); simpa using h
    have h3 : |(1 + z) ^ 3 * z ^ 3 * A 3| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 3) (by norm_num); simpa using h
    have h2 : |(1 + z) ^ 3 * z ^ 2 * A 2| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 2) (by norm_num); simpa using h
    have h8 : |8 * ((1 + z) ^ 3 * z ^ 3 * A 3)| ≤ 48000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]; linarith
    have h12 : |12 * ((1 + z) ^ 3 * z ^ 2 * A 2)| ≤ 72000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]; linarith
    calc |(1 + z) ^ 3 * z ^ 4 * A 4 + 8 * ((1 + z) ^ 3 * z ^ 3 * A 3)
            + 12 * ((1 + z) ^ 3 * z ^ 2 * A 2)|
        ≤ |(1 + z) ^ 3 * z ^ 4 * A 4| + |8 * ((1 + z) ^ 3 * z ^ 3 * A 3)|
            + |12 * ((1 + z) ^ 3 * z ^ 2 * A 2)| := abs_add_three _ _ _
      _ ≤ 6000 * Λ + 48000 * Λ + 72000 * Λ := add_le_add (add_le_add h4 h8) h12
      _ ≤ 200000 * Λ := by linarith

end Work.Elliptic
