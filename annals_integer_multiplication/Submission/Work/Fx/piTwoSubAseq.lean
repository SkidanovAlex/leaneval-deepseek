import Mathlib
import Submission.Work.Fx.piDefs

/-!
# The basic lower bound `2 - Aseq p ≥ 4 / 2^(qq p)`

`Aseq p = √(2+√(2+⋯))` (`p` nested square roots) tends to `2`, and we need a
quantitative decay for `2 - Aseq p`, valid from `p = 1` on.

The proof is elementary.  From `Aseq (k+1)² = 2 + Aseq k` we get the factorisation

  `(2 - Aseq (k+1)) * (2 + Aseq (k+1)) = 2 - Aseq k`,

and since `Aseq (k+1) ≤ 2` the second factor is at most `4`.  Hence
`2 - Aseq (k+1) ≥ (2 - Aseq k)/4`, and by induction

  `(2 - Aseq k) * 4^k ≥ 2`,   i.e.   `2 - Aseq k ≥ 2^(1-2k)`.

With `k = p ≥ 1` this gives `2 - Aseq p ≥ 2^(1-2p) ≥ 2^(2-4p) = 4/2^(4p)`.
No π bounds are used.
-/

set_option autoImplicit false

namespace Work.Fx

/-- The defining square relation of the real model sequence. -/
theorem Aseq_sq_succ (k : ℕ) : Aseq (k + 1) ^ 2 = 2 + Aseq k := by
  have hk : 0 ≤ Aseq k := by
    simpa [Aseq] using Real.sqrtTwoAddSeries_zero_nonneg k
  rw [Aseq_succ k, Real.sq_sqrt (show (0 : ℝ) ≤ 2 + Aseq k by linarith)]

/-- The multiplicative form of the decay: `(2 - Aseq k) * 4^k ≥ 2`. -/
theorem two_sub_Aseq_mul_four_pow_ge (k : ℕ) : 2 ≤ (2 - Aseq k) * (4 : ℝ) ^ k := by
  induction k with
  | zero => norm_num [Aseq_zero]
  | succ k ih =>
    have hle : Aseq (k + 1) ≤ 2 := by
      simpa [Aseq] using (Real.sqrtTwoAddSeries_lt_two (k + 1)).le
    have hnn : 0 ≤ 2 - Aseq (k + 1) := by linarith
    have hfac : (2 - Aseq (k + 1)) * (2 + Aseq (k + 1)) = 2 - Aseq k := by
      have hs := Aseq_sq_succ k
      nlinarith [hs]
    have h4 : (2 - Aseq k) ≤ (2 - Aseq (k + 1)) * 4 := by
      calc (2 - Aseq k) = (2 - Aseq (k + 1)) * (2 + Aseq (k + 1)) := hfac.symm
        _ ≤ (2 - Aseq (k + 1)) * 4 := by
              apply mul_le_mul_of_nonneg_left _ hnn
              linarith
    calc 2 ≤ (2 - Aseq k) * (4 : ℝ) ^ k := ih
      _ ≤ ((2 - Aseq (k + 1)) * 4) * (4 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (2 - Aseq (k + 1)) * (4 : ℝ) ^ (k + 1) := by ring

theorem piTwoSubAseq (p : ℕ) (hp : 1 ≤ p) :
    4 / (2 : ℝ) ^ Work.Fx.qq p ≤ 2 - Work.Fx.Aseq p := by
  have h := two_sub_Aseq_mul_four_pow_ge p
  have h4p : (4 : ℝ) ^ p = (2 : ℝ) ^ (2 * p) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h4p] at h
  have h2p : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * p) := by
    have h2 : 1 ≤ 2 * p := by omega
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ (2 * p) := pow_le_pow_right₀ (by norm_num) h2
  have hnn : 0 ≤ 2 - Aseq p := (two_sub_Aseq_pos p).le
  have hpow : (2 : ℝ) ^ (4 * p) = (2 : ℝ) ^ (2 * p) * (2 : ℝ) ^ (2 * p) := by
    rw [show 4 * p = 2 * p + 2 * p by ring, pow_add]
  rw [qq, hpow,
    div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * p) * (2 : ℝ) ^ (2 * p))]
  have h1 : 2 * 2 ≤ ((2 - Aseq p) * (2 : ℝ) ^ (2 * p)) * (2 : ℝ) ^ (2 * p) :=
    mul_le_mul h h2p (by norm_num) (by positivity)
  rw [show (2 : ℝ) * 2 = 4 by norm_num] at h1
  simpa [mul_assoc] using h1

end Work.Fx
