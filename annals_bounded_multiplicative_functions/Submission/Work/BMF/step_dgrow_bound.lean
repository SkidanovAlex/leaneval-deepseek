import Mathlib
import Submission.Work.BMF.adi_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- `(3 * C₀ ^ 2) ^ (m + 1) = 3 ^ (m + 1) * C₀ ^ (2 * m + 2)`, the form in which the
power of `3 * C₀ ^ 2` appears inside `Dgrow`. -/
theorem three_sq_pow_succ (C₀ : ℝ) (m : ℕ) :
    (3 * C₀ ^ 2) ^ (m + 1) = 3 ^ (m + 1) * C₀ ^ (2 * m + 2) := by
  rw [mul_pow, ← pow_mul]
  have h : 2 * (m + 1) = 2 * m + 2 := by ring
  rw [h]

theorem step_dgrow_bound (k j : ℕ) (C₀ A N x L : ℝ) (hC₀ : 1 ≤ C₀) (hA : 0 ≤ A)
    (hx : 0 < x) (hj : j ≤ k) (hNL : N * L ≤ C₀ * x) :
    2 * A * ((j : ℝ) + 1) * (j : ℝ) ^ (j + 1) * (N * L / x) * C₀ *
        (1 + (3 * C₀ ^ 2) ^ (j + 1)) ≤ A * Dgrow k C₀ := by
  have hjR : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
  have hNLx : N * L / x ≤ C₀ := (div_le_iff₀ hx).mpr hNL
  -- the base of the geometric factor is `≥ 1`
  have hbase : (1 : ℝ) ≤ 3 * C₀ ^ 2 := by
    have hC02 : (1 : ℝ) ≤ C₀ ^ 2 := one_le_pow₀ hC₀
    nlinarith
  -- key inequality `(j+1) j^{j+1} (1+X_j) ≤ k (k+1) k^k (1+X_k)`
  have hj1 : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by linarith
  have hjpow : (j : ℝ) ^ (j + 1) ≤ (k : ℝ) ^ (k + 1) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst hj0
      norm_num
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        have : 1 ≤ k := hk
        exact_mod_cast this
      calc (j : ℝ) ^ (j + 1) ≤ (k : ℝ) ^ (j + 1) :=
            pow_le_pow_left₀ (Nat.cast_nonneg j) hjR (j + 1)
        _ ≤ (k : ℝ) ^ (k + 1) := pow_le_pow_right₀ hk1 (by omega)
  have hX : (1 + (3 * C₀ ^ 2) ^ (j + 1)) ≤ (1 + (3 * C₀ ^ 2) ^ (k + 1)) := by
    have := pow_le_pow_right₀ hbase (show j + 1 ≤ k + 1 by omega)
    linarith
  have hmain : ((j : ℝ) + 1) * (j : ℝ) ^ (j + 1) * (1 + (3 * C₀ ^ 2) ^ (j + 1))
      ≤ (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * (1 + (3 * C₀ ^ 2) ^ (k + 1)) := by
    have hprod : ((j : ℝ) + 1) * (j : ℝ) ^ (j + 1) ≤ ((k : ℝ) + 1) * (k : ℝ) ^ (k + 1) :=
      mul_le_mul hj1 hjpow (pow_nonneg (Nat.cast_nonneg j) _) (by positivity)
    have hmain0 : ((j : ℝ) + 1) * (j : ℝ) ^ (j + 1) * (1 + (3 * C₀ ^ 2) ^ (j + 1))
        ≤ ((k : ℝ) + 1) * (k : ℝ) ^ (k + 1) * (1 + (3 * C₀ ^ 2) ^ (k + 1)) :=
      mul_le_mul hprod hX (by positivity) (by positivity)
    have hkpow : (k : ℝ) ^ (k + 1) = (k : ℝ) ^ k * (k : ℝ) := by rw [pow_succ]
    calc ((j : ℝ) + 1) * (j : ℝ) ^ (j + 1) * (1 + (3 * C₀ ^ 2) ^ (j + 1))
        ≤ ((k : ℝ) + 1) * (k : ℝ) ^ (k + 1) * (1 + (3 * C₀ ^ 2) ^ (k + 1)) := hmain0
      _ = (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * (1 + (3 * C₀ ^ 2) ^ (k + 1)) := by
          rw [hkpow]; ring
  have hA2 : (0 : ℝ) ≤ 2 * A * C₀ ^ 2 := by positivity
  have hstep1 : 2 * A * ((j : ℝ) + 1) * (j : ℝ) ^ (j + 1) * (N * L / x) * C₀ *
        (1 + (3 * C₀ ^ 2) ^ (j + 1))
      ≤ 2 * A * C₀ ^ 2 * (((j : ℝ) + 1) * (j : ℝ) ^ (j + 1) *
        (1 + (3 * C₀ ^ 2) ^ (j + 1))) := by
    have hnn : (0 : ℝ) ≤ 2 * A * ((j : ℝ) + 1) * (j : ℝ) ^ (j + 1) *
        (1 + (3 * C₀ ^ 2) ^ (j + 1)) * C₀ := by positivity
    have h1 := mul_le_mul_of_nonneg_left hNLx hnn
    ring_nf at h1 ⊢
    linarith [h1]
  have hstep2 : 2 * A * C₀ ^ 2 * (((j : ℝ) + 1) * (j : ℝ) ^ (j + 1) *
        (1 + (3 * C₀ ^ 2) ^ (j + 1))) ≤ A * Dgrow k C₀ := by
    have h2 := mul_le_mul_of_nonneg_left hmain hA2
    have hDgrow : A * Dgrow k C₀
        = 2 * A * C₀ ^ 2 * ((k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k *
            (1 + (3 * C₀ ^ 2) ^ (k + 1))) := by
      unfold Dgrow
      rw [three_sq_pow_succ]
      ring
    rw [hDgrow]
    exact h2
  linarith [hstep1, hstep2]

end Work.BMF
