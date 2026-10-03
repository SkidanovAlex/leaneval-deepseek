import Mathlib
import Submission.Work.Peluse.BoxNorm.boxNorm_pow

/-!
# From a power bound on `boxNormPow` to a bound on `boxNorm`

This file proves `Work.Prop36SW.boxNorm_le_of_boxNormPow_le`: if the `2 ^ (n - t)`-th power of the
`t`-fold box-norm power of `f` is at most `2 ^ (2 ^ (n - t) - 1)` times the `n`-fold box-norm power
of `f` (`t ≤ n`), then the `t`-fold box norm is at most twice the `n`-fold box norm.

The content is the pure real-variable lemma `root_le_two_mul_root`: for `A, B ≥ 0` and `t ≤ n`,

`A ^ (2 ^ (n - t)) ≤ 2 ^ (2 ^ (n - t) - 1) * B  ⟹  A ^ (1/2^t) ≤ 2 * B ^ (1/2^n)`.

Indeed both sides are nonnegative, so it suffices to compare their `2 ^ n`-th powers; there

`(A ^ (1/2^t)) ^ (2^n) = A ^ (2^n / 2^t) = A ^ (2^(n - t))`

(using `2^n = 2^(n - t) * 2^t`, valid in `ℝ` because `2^(n - t) * 2^t = 2^n` in `ℕ` and casts are
multiplicative), while

`(2 * B ^ (1/2^n)) ^ (2^n) = 2 ^ (2^n) * B`.

The hypothesis gives `A ^ (2^(n-t)) ≤ 2^(2^(n-t) - 1) * B`, and
`2^(2^(n-t) - 1) ≤ 2^(2^n)` because `2^(n-t) - 1 ≤ 2^(n-t) ≤ 2^n`.

The box-norm statement follows by unfolding `Work.Peluse.boxNorm`, which is *defined* as the
`2^t`-th root of `Work.Peluse.boxNormPow` (see `Work.Peluse.BoxNorm.boxNorm_pow`).

No finite-support hypothesis on `f` is needed: only the nonnegativity of `boxNormPow`, which holds
because it is a modulus (`Work.Peluse.boxNormPow t Q S f = ‖boxSumPow t Q S f‖`).
-/

namespace Work.Prop36SW

/-- The elementary real-variable core of `boxNorm_le_of_boxNormPow_le`: taking `2 ^ t`-th roots
turns the `2 ^ (n - t)`-th power bound into a factor-`2` bound. -/
theorem root_le_two_mul_root {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {t n : ℕ} (ht : t ≤ n)
    (h : A ^ (2 ^ (n - t)) ≤ (2 : ℝ) ^ (2 ^ (n - t) - 1) * B) :
    A ^ (1 / (2 : ℝ) ^ t) ≤ 2 * B ^ (1 / (2 : ℝ) ^ n) := by
  have hX : 0 ≤ A ^ (1 / (2 : ℝ) ^ t) := Real.rpow_nonneg hA _
  have hY : 0 ≤ 2 * B ^ (1 / (2 : ℝ) ^ n) := by
    have := Real.rpow_nonneg hB (1 / (2 : ℝ) ^ n); positivity
  -- `2 ^ n = 2 ^ (n - t) * 2 ^ t` in `ℕ`, hence in `ℝ`
  have hcast : ((2 : ℝ) ^ (n - t)) * ((2 : ℝ) ^ t) = (2 : ℝ) ^ n := by
    have hh := Nat.pow_sub_mul_pow 2 ht
    have h2 := congrArg (fun m : ℕ => (m : ℝ)) hh
    push_cast at h2
    exact h2
  -- exponent arithmetic: `(1 / 2^t) * 2^n = 2^(n - t)`
  have he1 : (1 / (2 : ℝ) ^ t) * ((2 : ℝ) ^ n) = (2 : ℝ) ^ (n - t) := by
    rw [← hcast, one_div]
    field_simp
  have hcastn : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  have hcastnt : ((2 ^ (n - t) : ℕ) : ℝ) = (2 : ℝ) ^ (n - t) := by push_cast; ring
  have hkey1 : (1 / (2 : ℝ) ^ t) * ((2 ^ n : ℕ) : ℝ) = ((2 ^ (n - t) : ℕ) : ℝ) := by
    rw [hcastn, hcastnt, he1]
  have hkey2 : (1 / (2 : ℝ) ^ n) * ((2 ^ n : ℕ) : ℝ) = 1 := by
    rw [hcastn, one_div, inv_mul_cancel₀ (by positivity : ((2 : ℝ) ^ n) ≠ 0)]
  -- it suffices to compare the `2 ^ n`-th powers, both sides being nonnegative
  have key : (A ^ (1 / (2 : ℝ) ^ t)) ^ (2 ^ n) ≤ (2 * B ^ (1 / (2 : ℝ) ^ n)) ^ (2 ^ n) := by
    have h1 : (A ^ (1 / (2 : ℝ) ^ t)) ^ (2 ^ n) = A ^ (2 ^ (n - t)) := by
      rw [← Real.rpow_natCast (A ^ (1 / (2 : ℝ) ^ t)) (2 ^ n), ← Real.rpow_mul hA]
      rw [hkey1, Real.rpow_natCast]
    have h2 : (2 * B ^ (1 / (2 : ℝ) ^ n)) ^ (2 ^ n) = (2 : ℝ) ^ (2 ^ n) * B := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast (B ^ (1 / (2 : ℝ) ^ n)) (2 ^ n), ← Real.rpow_mul hB]
      rw [hkey2, Real.rpow_one]
    rw [h1, h2]
    have hle : 2 ^ (n - t) - 1 ≤ 2 ^ n := by
      have h1 : 2 ^ (n - t) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n t)
      exact Nat.sub_le_iff_le_add.mpr (le_trans h1 (Nat.le_add_right _ _))
    exact le_trans h (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hle) hB)
  exact (pow_le_pow_iff_left₀ hX hY (pow_ne_zero n (by norm_num))).mp key

theorem boxNorm_le_of_boxNormPow_le {t n : ℕ} (ht : t ≤ n) (Q : Fin t → Finset ℤ)
    (Q' : Fin n → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (h : (Work.Peluse.boxNormPow t Q S f) ^ (2 ^ (n - t))
      ≤ (2 : ℝ) ^ (2 ^ (n - t) - 1) * Work.Peluse.boxNormPow n Q' S f) :
    Work.Peluse.boxNorm t Q S f ≤ 2 * Work.Peluse.boxNorm n Q' S f := by
  rw [Work.Peluse.boxNorm, Work.Peluse.boxNorm]
  exact root_le_two_mul_root (norm_nonneg _) (norm_nonneg _) ht h

end Work.Prop36SW
