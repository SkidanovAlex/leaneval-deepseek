import Mathlib
import Submission.Work.Peluse.Basic

/-!
# `boxNorm` is the `2^t`-th root of `boxNormPow`

Peluse's box norm `‖f‖_{□^t_{Q₁,…,Q_t}(S)}` is *defined* as the `2^t`-th root of the box-norm
power `boxNormPow` (see `Work.Peluse.boxNorm`).  This file records the inverse relation:
raising `boxNorm` to the `2^t`-th power recovers `boxNormPow`.

Nothing but nonnegativity of `boxNormPow` (it is a modulus) is used.
-/

namespace Work.Peluse.BoxNorm

theorem boxNorm_pow (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxNorm t Q S f ^ (2 ^ t) = Work.Peluse.boxNormPow t Q S f := by
  rw [Work.Peluse.boxNorm, ← Real.rpow_natCast]
  set A := Work.Peluse.boxNormPow t Q S f with hA
  have hA0 : (0 : ℝ) ≤ A := norm_nonneg _
  have h2 : ((2 : ℝ) ^ t) ≠ 0 := by positivity
  have hy : (1 / ((2 : ℝ) ^ t)) * ((2 ^ t : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, div_mul_eq_mul_div, one_mul, div_self h2]
  rw [← Real.rpow_mul hA0, hy, Real.rpow_one]

end Work.Peluse.BoxNorm
