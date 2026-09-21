import Mathlib

set_option linter.unusedVariables false

/-!
# Lipschitz bound for `φ ↦ (y² - φ²)^n * √(y² - φ²)`

For `n ≥ 1`, `|y| ≤ M` and real `φ₁ φ₂`,

`|(y² - φ₁²)^n √(y² - φ₁²) - (y² - φ₂²)^n √(y² - φ₂²)| ≤ (2n+1) M^{2n} |φ₁ - φ₂|`.

This is the Lipschitz estimate for the integrand of the volume moment `(A)` of the odd case
(`Work.OddCurve.momentA`) as a function of the cutting slope.  The exponent `n + 1/2` in the
natural formulation is handled through `Real.rpow`: writing `g φ = max (y² - φ²) 0`, the
integrand is exactly `(g φ) ^ (n + 1/2)`, and the mean-value bound for `x ↦ x ^ r` (`r ≥ 1`)
together with the Lipschitz bound `|g φ₁ - g φ₂| ≤ 2 |y| |φ₁ - φ₂|` gives the result.

The proof of the mean-value bound for `x ^ r` is Bernoulli's inequality
(`one_add_mul_self_le_rpow_one_add`); no derivative of `Real.rpow` is needed.
-/

namespace Work.OddCurve

/-- **Mean-value-type bound for `x ↦ x ^ r`.**  For `r ≥ 1` and `0 ≤ b ≤ a`,
`a ^ r - b ^ r ≤ r * a ^ (r - 1) * (a - b)`.  Proof: `b / a ^ r ≥ 1 + r * (b/a - 1)` is
Bernoulli's inequality, and rewriting `a ^ r * (b/a) ^ r = b ^ r` gives the claim. -/
lemma rpow_sub_rpow_le_mul {r a b : ℝ} (hr : 1 ≤ r) (hb : 0 ≤ b) (hba : b ≤ a) :
    a ^ r - b ^ r ≤ r * a ^ (r - 1) * (a - b) := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < r)
  rcases eq_or_lt_of_le (le_trans hb hba) with ha | ha
  · have hb0 : b = 0 := by linarith
    rw [hb0, ← ha]
    simp [Real.zero_rpow hr0]
  have hs : -1 ≤ (b - a) / a := by
    rw [le_div_iff₀ ha]; linarith
  have hbase : 1 + (b - a) / a = b / a := by
    field_simp
    ring
  have hber : 1 + r * ((b - a) / a) ≤ (b / a) ^ r := by
    have h := one_add_mul_self_le_rpow_one_add hs hr
    rwa [hbase] at h
  have har : 0 < a ^ r := Real.rpow_pos_of_pos ha r
  have hmul := mul_le_mul_of_nonneg_left hber har.le
  have hbr : a ^ r * (b / a) ^ r = b ^ r := by
    rw [← Real.mul_rpow ha.le (div_nonneg hb ha.le), mul_div_cancel₀ b ha.ne']
  rw [hbr] at hmul
  have hmul' : a ^ r * a + r * a ^ r * (b - a) ≤ b ^ r * a := by
    have h := mul_le_mul_of_nonneg_right hmul ha.le
    have e : a ^ r * (1 + r * ((b - a) / a)) * a = a ^ r * a + r * a ^ r * (b - a) := by
      field_simp
    rwa [e] at h
  rw [Real.rpow_sub_one ha.ne' r]
  have hgoal : r * (a ^ r / a) * (a - b) = r * a ^ r * (a - b) / a := by ring
  rw [hgoal, le_div_iff₀ ha]
  nlinarith [hmul']

/-- Two-sided form of `rpow_sub_rpow_le_mul`: for `r ≥ 1` and `a, b ≥ 0`,
`|a ^ r - b ^ r| ≤ r * (max a b) ^ (r - 1) * |a - b|`. -/
lemma abs_rpow_sub_rpow_le {r a b : ℝ} (hr : 1 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a ^ r - b ^ r| ≤ r * max a b ^ (r - 1) * |a - b| := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  rcases le_total a b with h | h
  · have hle : a ^ r ≤ b ^ r := Real.rpow_le_rpow ha h hr0
    rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr hle), abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [rpow_sub_rpow_le_mul hr ha h]
  · have hle : b ^ r ≤ a ^ r := Real.rpow_le_rpow hb h hr0
    rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonneg (sub_nonneg.mpr h)]
    exact rpow_sub_rpow_le_mul hr hb h

/-- The integrand as a real power: `(y² - φ²)^n √(y² - φ²) = (max (y² - φ²) 0) ^ (n + 1/2)`. -/
lemma radn_eq_max_rpow {n : ℕ} (y φ : ℝ) :
    (y ^ 2 - φ ^ 2) ^ n * Real.sqrt (y ^ 2 - φ ^ 2)
      = (max (y ^ 2 - φ ^ 2) 0) ^ ((n : ℝ) + 1 / 2) := by
  rcases lt_trichotomy (y ^ 2 - φ ^ 2) 0 with h | h | h
  · rw [max_eq_right h.le, Real.sqrt_eq_zero_of_nonpos h.le, mul_zero]
    exact (Real.zero_rpow (by positivity)).symm
  · rw [h, max_self, Real.zero_rpow (by positivity : ((n : ℝ) + 1 / 2) ≠ 0)]
    simp
  · rw [max_eq_left h.le, Real.rpow_add h, ← Real.rpow_natCast, ← Real.sqrt_eq_rpow]

/-- Lipschitz bound for `φ ↦ max (y² - φ²) 0`, with constant `2 |y|`.  The auxiliary function
`φ ↦ min |φ| |y|` clamps `φ` to the range where the maximum is not zero, and the claim follows
from `|min a c - min b c| ≤ |a - b|` and `||a| - |b|| ≤ |a - b|`. -/
lemma max_sq_sub_lipschitz (y φ₁ φ₂ : ℝ) :
    |max (y ^ 2 - φ₁ ^ 2) 0 - max (y ^ 2 - φ₂ ^ 2) 0| ≤ 2 * |y| * |φ₁ - φ₂| := by
  have key : ∀ a b c : ℝ, a ≤ b → min b c - min a c ≤ b - a := by
    intro a b c hab
    rcases le_total a c with hac | hac
    · rw [min_eq_left hac]
      linarith [min_le_left b c]
    · rw [min_eq_right hac, min_eq_right (le_trans hac hab)]
      linarith
  have hmin_lip : ∀ a b c : ℝ, |min a c - min b c| ≤ |a - b| := by
    intro a b c
    rcases le_total a b with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr (min_le_min h le_rfl)), abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [key a b c h]
    · have h1 : min b c ≤ min a c := min_le_min h le_rfl
      rw [abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonneg (sub_nonneg.mpr h)]
      exact key b a c h
  have hw : ∀ φ : ℝ, max (y ^ 2 - φ ^ 2) 0 = y ^ 2 - (min |φ| |y|) ^ 2 := by
    intro φ
    rcases le_total |φ| |y| with h | h
    · have hfy : φ ^ 2 ≤ y ^ 2 := by
        rw [← sq_abs φ, ← sq_abs y]
        exact pow_le_pow_left₀ (abs_nonneg φ) h 2
      rw [min_eq_left h, max_eq_left (by linarith), sq_abs]
    · have hfy : y ^ 2 ≤ φ ^ 2 := by
        rw [← sq_abs φ, ← sq_abs y]
        exact pow_le_pow_left₀ (abs_nonneg y) h 2
      rw [min_eq_right h, max_eq_right (by linarith), sq_abs]
      ring
  rw [hw φ₁, hw φ₂]
  have hkey : (y ^ 2 - (min |φ₁| |y|) ^ 2) - (y ^ 2 - (min |φ₂| |y|) ^ 2)
      = (min |φ₂| |y| - min |φ₁| |y|) * (min |φ₁| |y| + min |φ₂| |y|) := by ring
  rw [hkey, abs_mul]
  have hnn1 : 0 ≤ min |φ₁| |y| := le_min (abs_nonneg φ₁) (abs_nonneg y)
  have hnn2 : 0 ≤ min |φ₂| |y| := le_min (abs_nonneg φ₂) (abs_nonneg y)
  rw [abs_of_nonneg (by linarith : 0 ≤ min |φ₁| |y| + min |φ₂| |y|)]
  have hlip1 : |(min |φ₂| |y|) - (min |φ₁| |y|)| ≤ |φ₁ - φ₂| := by
    calc |(min |φ₂| |y|) - (min |φ₁| |y|)| ≤ |(|φ₂|) - (|φ₁|)| := hmin_lip _ _ _
      _ = |(|φ₁|) - (|φ₂|)| := abs_sub_comm _ _
      _ ≤ |φ₁ - φ₂| := abs_abs_sub_abs_le_abs_sub φ₁ φ₂
  have hwle : min |φ₁| |y| + min |φ₂| |y| ≤ 2 * |y| := by
    have h1 : min |φ₁| |y| ≤ |y| := min_le_right _ _
    have h2 : min |φ₂| |y| ≤ |y| := min_le_right _ _
    linarith
  calc |(min |φ₂| |y|) - (min |φ₁| |y|)| * (min |φ₁| |y| + min |φ₂| |y|)
      ≤ |φ₁ - φ₂| * (2 * |y|) := mul_le_mul hlip1 hwle (by positivity) (abs_nonneg _)
    _ = 2 * |y| * |φ₁ - φ₂| := by ring

/-- The core estimate, with `|y| ^ (2n)` (instead of `M ^ (2n)`) on the right. -/
theorem abs_rad_phi_sub_le_abs {n : ℕ} (hn : 1 ≤ n) (y φ₁ φ₂ : ℝ) :
    |(y ^ 2 - φ₁ ^ 2) ^ n * Real.sqrt (y ^ 2 - φ₁ ^ 2) -
      (y ^ 2 - φ₂ ^ 2) ^ n * Real.sqrt (y ^ 2 - φ₂ ^ 2)|
      ≤ (2 * (n : ℝ) + 1) * |y| ^ (2 * n) * |φ₁ - φ₂| := by
  rw [radn_eq_max_rpow y φ₁, radn_eq_max_rpow y φ₂]
  set r : ℝ := (n : ℝ) + 1 / 2 with hr
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hr0 : 0 ≤ r := le_trans zero_le_one hr1
  have hg1 : 0 ≤ max (y ^ 2 - φ₁ ^ 2) 0 := le_max_right _ _
  have hg2 : 0 ≤ max (y ^ 2 - φ₂ ^ 2) 0 := le_max_right _ _
  have hgy1 : max (y ^ 2 - φ₁ ^ 2) 0 ≤ y ^ 2 :=
    max_le (by nlinarith [sq_nonneg φ₁]) (sq_nonneg y)
  have hgy2 : max (y ^ 2 - φ₂ ^ 2) 0 ≤ y ^ 2 :=
    max_le (by nlinarith [sq_nonneg φ₂]) (sq_nonneg y)
  have hA := abs_rpow_sub_rpow_le hr1 hg1 hg2
  have hD := max_sq_sub_lipschitz y φ₁ φ₂
  have hB : (max (max (y ^ 2 - φ₁ ^ 2) 0) (max (y ^ 2 - φ₂ ^ 2) 0)) ^ (r - 1)
      ≤ (y ^ 2) ^ (r - 1) := by
    apply Real.rpow_le_rpow _ _ _
    · exact le_trans hg1 (le_max_left _ _)
    · exact max_le hgy1 hgy2
    · linarith
  have hC : (y ^ 2) ^ (r - 1) = |y| ^ (2 * n - 1) := by
    rw [← sq_abs y, ← Real.rpow_natCast |y| 2, ← Real.rpow_mul (abs_nonneg y),
      ← Real.rpow_natCast]
    congr 1
    rw [hr, Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  have hpow2n : |y| ^ (2 * n - 1) * |y| = |y| ^ (2 * n) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)]
  calc |(max (y ^ 2 - φ₁ ^ 2) 0) ^ r - (max (y ^ 2 - φ₂ ^ 2) 0) ^ r|
      ≤ r * (max (max (y ^ 2 - φ₁ ^ 2) 0) (max (y ^ 2 - φ₂ ^ 2) 0)) ^ (r - 1)
          * |max (y ^ 2 - φ₁ ^ 2) 0 - max (y ^ 2 - φ₂ ^ 2) 0| := hA
    _ ≤ r * |y| ^ (2 * n - 1) * (2 * |y| * |φ₁ - φ₂|) := by
        rw [← hC]
        have h := mul_le_mul hB hD (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)
        calc r * (max (max (y ^ 2 - φ₁ ^ 2) 0) (max (y ^ 2 - φ₂ ^ 2) 0)) ^ (r - 1)
              * |max (y ^ 2 - φ₁ ^ 2) 0 - max (y ^ 2 - φ₂ ^ 2) 0|
            = r * ((max (max (y ^ 2 - φ₁ ^ 2) 0) (max (y ^ 2 - φ₂ ^ 2) 0)) ^ (r - 1)
              * |max (y ^ 2 - φ₁ ^ 2) 0 - max (y ^ 2 - φ₂ ^ 2) 0|) := by ring
          _ ≤ r * ((y ^ 2) ^ (r - 1) * (2 * |y| * |φ₁ - φ₂|)) :=
              mul_le_mul_of_nonneg_left h hr0
          _ = r * (y ^ 2) ^ (r - 1) * (2 * |y| * |φ₁ - φ₂|) := by ring
    _ = (2 * (n : ℝ) + 1) * |y| ^ (2 * n) * |φ₁ - φ₂| := by
        rw [hr]
        rw [show (↑n + 1 / 2) * |y| ^ (2 * n - 1) * (2 * |y| * |φ₁ - φ₂|)
              = 2 * (↑n + 1 / 2) * (|y| ^ (2 * n - 1) * |y|) * |φ₁ - φ₂| by ring]
        rw [hpow2n]
        ring

theorem abs_rad_phi_sub_le {n : ℕ} (hn : 1 ≤ n) {M y φ₁ φ₂ : ℝ} (hM : 0 ≤ M) (hy : |y| ≤ M) :
    |(y ^ 2 - φ₁ ^ 2) ^ n * Real.sqrt (y ^ 2 - φ₁ ^ 2) -
      (y ^ 2 - φ₂ ^ 2) ^ n * Real.sqrt (y ^ 2 - φ₂ ^ 2)|
      ≤ (2 * (n : ℝ) + 1) * M ^ (2 * n) * |φ₁ - φ₂| := by
  refine (abs_rad_phi_sub_le_abs hn y φ₁ φ₂).trans ?_
  have hMle : |y| ^ (2 * n) ≤ M ^ (2 * n) := pow_le_pow_left₀ (abs_nonneg y) hy (2 * n)
  have h2 : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMle h2) (abs_nonneg _)

end Work.OddCurve
