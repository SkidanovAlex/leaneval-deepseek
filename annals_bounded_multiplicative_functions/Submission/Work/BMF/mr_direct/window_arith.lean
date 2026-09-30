import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Purely numerical estimate behind the short-interval averaging argument.

For `X ≥ 16` and `K ≥ 0`, with `a = ⌊2X⌋₊` and `b = ⌈X⌉₊`, one has
`(a + (b - 1)) * (1/a + 1/b) ≤ 6`.  Indeed `2b - 3 ≤ a ≤ 2b` and `b ≥ 16`, so
`a² - 4ab + b² = (a - 2b + 3)(a - 2b - 3) + 9 - 3b² ≤ 0`, which is equivalent
to the claim after multiplying by the positive quantity `ab`. -/
theorem window_arith (X K : ℝ) (hX : 16 ≤ X) (hK : 0 ≤ K) :
    K * (((⌊2 * X⌋₊ : ℕ) : ℝ) + (((⌈X⌉₊ : ℕ) : ℝ) - 1)) *
      (1 / (((⌊2 * X⌋₊ : ℕ) : ℝ)) + 1 / (((⌈X⌉₊ : ℕ) : ℝ))) ≤ 6 * K := by
  set a : ℝ := ((⌊2 * X⌋₊ : ℕ) : ℝ) with ha_def
  set b : ℝ := ((⌈X⌉₊ : ℕ) : ℝ) with hb_def
  have hX0 : 0 ≤ X := by linarith
  have ha_le : a ≤ 2 * X := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ 2 * X by linarith)
    rwa [← ha_def] at h
  have ha_gt : 2 * X < a + 1 := by
    have h := Nat.lt_floor_add_one (2 * X)
    rwa [← ha_def] at h
  have hb_ge : X ≤ b := by
    have h := Nat.le_ceil X
    rwa [← hb_def] at h
  have hb_lt : b < X + 1 := by
    have h := Nat.ceil_lt_add_one hX0
    rwa [← hb_def] at h
  have hb16 : (16 : ℝ) ≤ b := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  -- `2 * b - 3 ≤ a`, since `b < X + 1` and `2 * X < a + 1`
  have h1 : 0 ≤ a - (2 * b - 3) := by linarith
  have h2 : a - (2 * b + 3) ≤ 0 := by linarith
  have h3 : 9 - 3 * b ^ 2 ≤ 0 := by nlinarith
  have hfac : a ^ 2 - 4 * a * b + b ^ 2 =
      (a - (2 * b - 3)) * (a - (2 * b + 3)) + (9 - 3 * b ^ 2) := by ring
  have hf : a ^ 2 - 4 * a * b + b ^ 2 ≤ 0 := by
    have hm := mul_nonpos_of_nonneg_of_nonpos h1 h2
    rw [hfac]; linarith
  have key : (a + (b - 1)) * (1 / a + 1 / b) ≤ 6 := by
    have hab : (a + (b - 1)) * (1 / a + 1 / b) = ((a + b - 1) * (a + b)) / (a * b) := by
      field_simp; ring
    rw [hab]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hf, ha0, hb0]
  have hfin : K * (a + (b - 1)) * (1 / a + 1 / b) ≤ 6 * K := by
    have h := mul_le_mul_of_nonneg_left key hK
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  exact hfin

end Work.BMF.mr_direct
