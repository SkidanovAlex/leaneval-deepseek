import Mathlib

namespace Work.FIArea7

/-- Auxiliary "potential" function: its consecutive differences telescope the summand
`(b + i)^2 r^i`, so its value at `0` dominates the partial sums. -/
noncomputable def geomPot (b r : ℝ) (n : ℕ) : ℝ :=
  ((1 / (1 - r)) * (n : ℝ) ^ 2 + (2 * b / (1 - r) + 2 * r / (1 - r) ^ 2) * (n : ℝ)
      + (r * (1 + r) / (1 - r) ^ 3 + 2 * b * r / (1 - r) ^ 2 + b ^ 2 / (1 - r))) * r ^ n

/-- The finite sum of `(b+i)^2 r^i` is bounded by the value of the "potential" at `0`,
i.e. by the limit of the geometric series with quadratic weight. -/
private lemma geom_sum_telescope (b r : ℝ) (hb : 0 ≤ b) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), (b + (i : ℝ)) ^ 2 * r ^ i
      ≤ r * (1 + r) / (1 - r) ^ 3 + 2 * b * r / (1 - r) ^ 2 + b ^ 2 / (1 - r) := by
  have hstep : ∀ n : ℕ, (b + (n : ℝ)) ^ 2 * r ^ n = geomPot b r n - geomPot b r (n + 1) := by
    intro n
    simp only [geomPot]
    rw [pow_succ]
    have hx : (1 : ℝ) - r ≠ 0 := by linarith
    push_cast
    field_simp
    ring
  have hsum : ∑ i ∈ Finset.range (M + 1), (b + (i : ℝ)) ^ 2 * r ^ i
      = ∑ i ∈ Finset.range (M + 1), (geomPot b r i - geomPot b r (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hstep i
  rw [hsum, Finset.sum_range_sub']
  have h0 : geomPot b r 0
      = r * (1 + r) / (1 - r) ^ 3 + 2 * b * r / (1 - r) ^ 2 + b ^ 2 / (1 - r) := by
    simp [geomPot]
  have hnn : 0 ≤ geomPot b r (M + 1) := by
    simp only [geomPot]
    positivity
  rw [h0]
  linarith

/-- The value of the quadratic-weighted geometric series is bounded by the
explicit expression appearing in the target statement. -/
private lemma geom_coeff_bound (b r : ℝ) (hb : 2 ≤ b) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r * (1 + r) / (1 - r) ^ 3 + 2 * b * r / (1 - r) ^ 2 + b ^ 2 / (1 - r)
      ≤ b ^ 4 * (1 / (4 * (1 - r)) + r / (4 * (1 - r) ^ 2)
          + r * (1 + r) / (16 * (1 - r) ^ 3)) := by
  have hx : (0 : ℝ) < 1 - r := by linarith
  have hfacA : b ^ 4 - 16 * (b - 1) ^ 2 = (b - 2) ^ 2 * (b ^ 2 + 4 * b - 4) := by ring
  have hfacB : b ^ 4 - 16 * (2 * b - 3) = (b - 2) ^ 2 * (b ^ 2 + 4 * b + 12) := by ring
  have hA : (0 : ℝ) ≤ b ^ 4 - 16 * (b - 1) ^ 2 := by
    rw [hfacA]; nlinarith [sq_nonneg (b - 2), hb]
  have hB : (0 : ℝ) ≤ b ^ 4 - 16 * (2 * b - 3) := by
    rw [hfacB]; nlinarith [sq_nonneg (b - 2), hb]
  have hC : (0 : ℝ) ≤ 2 * b ^ 4 - 32 := by nlinarith [hb]
  have hiden : b ^ 4 * (1 / (4 * (1 - r)) + r / (4 * (1 - r) ^ 2)
          + r * (1 + r) / (16 * (1 - r) ^ 3))
      - (r * (1 + r) / (1 - r) ^ 3 + 2 * b * r / (1 - r) ^ 2 + b ^ 2 / (1 - r))
      = ((b ^ 4 - 16 * (b - 1) ^ 2) * (1 - r) ^ 2 + (b ^ 4 - 16 * (2 * b - 3)) * (1 - r)
          + (2 * b ^ 4 - 32)) / (16 * (1 - r) ^ 3) := by
    field_simp
    ring
  have hnum : 0 ≤ (b ^ 4 - 16 * (b - 1) ^ 2) * (1 - r) ^ 2
      + (b ^ 4 - 16 * (2 * b - 3)) * (1 - r) + (2 * b ^ 4 - 32) := by
    have h1 := mul_nonneg hA (sq_nonneg (1 - r))
    have h2 := mul_nonneg hB (le_of_lt hx)
    linarith [h1, h2, hC]
  have hpos : 0 ≤ b ^ 4 * (1 / (4 * (1 - r)) + r / (4 * (1 - r) ^ 2)
          + r * (1 + r) / (16 * (1 - r) ^ 3))
      - (r * (1 + r) / (1 - r) ^ 3 + 2 * b * r / (1 - r) ^ 2 + b ^ 2 / (1 - r)) := by
    rw [hiden]
    exact div_nonneg hnum (by positivity)
  linarith [hpos]

lemma geom_pow_sum_bound (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (a M : ℕ) (ha : 1 ≤ a) :
    ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * r ^ i
      ≤ (((a + 1 : ℕ) : ℝ)) ^ 4 *
        (1 / (4 * (1 - r)) + r / (4 * (1 - r) ^ 2) + r * (1 + r) / (16 * (1 - r) ^ 3)) := by
  set b : ℝ := ((a + 1 : ℕ) : ℝ) with hbdef
  have hb2 : 2 ≤ b := by
    rw [hbdef]
    exact_mod_cast (by omega : 2 ≤ a + 1)
  have hb0 : 0 ≤ b := by linarith
  have hcast : ∀ i : ℕ, (((a + i + 1 : ℕ) : ℝ)) = b + (i : ℝ) := by
    intro i
    rw [hbdef]
    push_cast
    ring
  calc ∑ i ∈ Finset.range (M + 1), (((a + i + 1 : ℕ) : ℝ)) ^ 2 * r ^ i
      = ∑ i ∈ Finset.range (M + 1), (b + (i : ℝ)) ^ 2 * r ^ i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcast i]
    _ ≤ r * (1 + r) / (1 - r) ^ 3 + 2 * b * r / (1 - r) ^ 2 + b ^ 2 / (1 - r) :=
        geom_sum_telescope b r hb0 hr0 hr1 M
    _ ≤ b ^ 4 * (1 / (4 * (1 - r)) + r / (4 * (1 - r) ^ 2)
          + r * (1 + r) / (16 * (1 - r) ^ 3)) :=
        geom_coeff_bound b r hb2 hr0 hr1
    _ = (((a + 1 : ℕ) : ℝ)) ^ 4 *
          (1 / (4 * (1 - r)) + r / (4 * (1 - r) ^ 2)
            + r * (1 + r) / (16 * (1 - r) ^ 3)) := by
        rw [hbdef]

end Work.FIArea7
