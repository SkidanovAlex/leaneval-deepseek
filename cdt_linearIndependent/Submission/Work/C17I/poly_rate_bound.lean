import Mathlib

/-!
# A polynomial-times-geometric rate bound

For `0 < r ≤ 45/16` the sequence `n ↦ (n+3)^3 * r^n` is bounded by a constant
multiple of `4^n`.  Equivalently, with `q = r/4 ≤ 45/64`, the sequence
`n ↦ (n+3)^3 * q^n` is bounded, and we exhibit the explicit constant `100`.

The key step is that `F n = (n+3)^3 * (45/64)^n` is non-increasing for `n ≥ 6`
(the ratio `F (n+1) / F n = ((n+4)/(n+3))^3 * (45/64) ≤ (10/9)^3 * (45/64 < 1`),
while the finitely many values `F 0, …, F 6` are all `< 100`.
-/

namespace Work.C17I

private noncomputable def polyR_F (n : ℕ) : ℝ := ((n : ℝ) + 3) ^ 3 * (45 / 64) ^ n

/-- One step of the monotonicity of `polyR_F` from `6` on. -/
private lemma polyR_F_step (m : ℕ) (hm : 6 ≤ m) : polyR_F (m + 1) ≤ polyR_F m := by
  have hkey : ((m : ℝ) + 4) ^ 3 * (45 / 64) ≤ ((m : ℝ) + 3) ^ 3 := by
    have hm' : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hle : (m : ℝ) + 4 ≤ (10 / 9) * ((m : ℝ) + 3) := by linarith
    have h0 : (0 : ℝ) ≤ (m : ℝ) + 4 := by linarith
    have hcube : ((m : ℝ) + 4) ^ 3 ≤ ((10 / 9) * ((m : ℝ) + 3)) ^ 3 :=
      pow_le_pow_left₀ h0 hle 3
    have hc : ((10 / 9 : ℝ)) ^ 3 * (45 / 64) ≤ 1 := by norm_num
    calc ((m : ℝ) + 4) ^ 3 * (45 / 64)
        ≤ ((10 / 9) * ((m : ℝ) + 3)) ^ 3 * (45 / 64) :=
          mul_le_mul_of_nonneg_right hcube (by norm_num)
      _ = (((10 / 9 : ℝ) ^ 3) * (45 / 64)) * ((m : ℝ) + 3) ^ 3 := by ring
      _ ≤ 1 * ((m : ℝ) + 3) ^ 3 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ((m : ℝ) + 3) ^ 3 := by ring
  have hnn : (0 : ℝ) ≤ (45 / 64) ^ m := by positivity
  show (((m + 1 : ℕ) : ℝ) + 3) ^ 3 * (45 / 64) ^ (m + 1) ≤ ((m : ℝ) + 3) ^ 3 * (45 / 64) ^ m
  rw [pow_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  calc (((m : ℝ) + 1) + 3) ^ 3 * ((45 / 64) ^ m * (45 / 64))
      = (((m : ℝ) + 4) ^ 3 * (45 / 64)) * (45 / 64) ^ m := by ring
    _ ≤ ((m : ℝ) + 3) ^ 3 * (45 / 64) ^ m := mul_le_mul_of_nonneg_right hkey hnn

/-- `polyR_F n ≤ 100` for every `n`. -/
private lemma polyR_F_le (n : ℕ) : polyR_F n ≤ 100 := by
  rcases le_or_gt n 6 with hn | hn
  · interval_cases n <;> norm_num [polyR_F]
  · have hstep : ∀ m ≥ 6, polyR_F m ≤ polyR_F 6 → polyR_F (m + 1) ≤ polyR_F 6 := by
      intro m hm ih
      exact le_trans (polyR_F_step m hm) ih
    have hmono : polyR_F n ≤ polyR_F 6 := Nat.le_induction (le_refl _) hstep n (le_of_lt hn)
    have h6 : polyR_F 6 ≤ 100 := by norm_num [polyR_F]
    exact le_trans hmono h6

/-- `(n+3)^3 * q^n ≤ 100` whenever `0 ≤ q ≤ 45/64`. -/
private lemma polyR_geom_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 45 / 64) (n : ℕ) :
    ((n : ℝ) + 3) ^ 3 * q ^ n ≤ 100 := by
  have h : q ^ n ≤ (45 / 64) ^ n := pow_le_pow_left₀ hq0 hq1 n
  calc ((n : ℝ) + 3) ^ 3 * q ^ n ≤ ((n : ℝ) + 3) ^ 3 * (45 / 64) ^ n :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 100 := polyR_F_le n

theorem poly_rate_bound (r : ℝ) (hr : 0 < r) (hr4 : r ≤ 45 / 16) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ((n : ℝ) + 3) ^ 3 * r ^ n ≤ C * 4 ^ n := by
  refine ⟨100, by norm_num, fun n => ?_⟩
  have hq0 : 0 ≤ r / 4 := by linarith
  have hq1 : r / 4 ≤ 45 / 64 := by linarith
  have hb : ((n : ℝ) + 3) ^ 3 * (r / 4) ^ n ≤ 100 := polyR_geom_bound (r / 4) hq0 hq1 n
  have hrpow : r ^ n = 4 ^ n * (r / 4) ^ n := by
    rw [← mul_pow, show (4 : ℝ) * (r / 4) = r by ring]
  have hT : (0 : ℝ) ≤ 4 ^ n := by positivity
  calc ((n : ℝ) + 3) ^ 3 * r ^ n
      = 4 ^ n * (((n : ℝ) + 3) ^ 3 * (r / 4) ^ n) := by rw [hrpow]; ring
    _ ≤ 4 ^ n * 100 := mul_le_mul_of_nonneg_left hb hT
    _ = 100 * 4 ^ n := by ring

end Work.C17I
