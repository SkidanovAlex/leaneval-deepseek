import Mathlib
import Submission.Work.BW.valuation_eq_exp_neg_count

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The positive logarithm of a finite place is the valuation times `log` of the norm

For a nonzero `β` in a number field `L` and a finite place `v` of `L`, the positive part of the
logarithm of the value `v β` is exactly

`max 0 (- val_v(β)) · log N(v)`,

where `val_v(β) = FractionalIdeal.count L v.maximalIdeal (spanSingleton _ β)` is the valuation
attached to `v` and `N(v) = Ideal.absNorm v.maximalIdeal.asIdeal` is the norm of the place.

Equivalently `v β = N(v) ^ (- val_v(β))`, which is `FinitePlace.norm_embedding'` combined with
`Work.BW.valuation_eq_exp_neg_count`; the statement below is its logarithm, using the elementary
identity `(n * L)⁺ = (max 0 n).toNat * L` for `0 ≤ L`.
-/

namespace Work.BW

open scoped nonZeroDivisors

/-- `WithZeroMulInt.toNNReal` evaluated at `WithZero.exp n` is the `n`-th power of the base. -/
lemma toNNReal_exp {e : NNReal} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  rw [WithZeroMulInt.toNNReal_neg_apply he (WithZero.exp_ne_zero (a := n))]
  congr 1

/-- The positive part of an integer multiple of a nonnegative real number. -/
lemma posLog_int_mul (n : ℤ) {L : ℝ} (hL : 0 ≤ L) :
    (n * L)⁺ = ((max 0 n).toNat : ℝ) * L := by
  rcases lt_or_ge n 0 with h | h
  · have hn : ((n : ℤ) : ℝ) * L ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h.le) hL
    rw [max_eq_left h.le, Int.toNat_zero, Nat.cast_zero, zero_mul, posPart_eq_zero.mpr hn]
  · have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h
    rw [max_eq_right h, hcast]
    exact posPart_eq_self.mpr (mul_nonneg (by exact_mod_cast h) hL)

theorem finitePlace_posLog_eq {L : Type*} [Field L] [NumberField L] (β : L) (hβ : β ≠ 0)
    (v : NumberField.FinitePlace L) :
    (Real.log (v β))⁺ =
      (((max 0 (-(FractionalIdeal.count L v.maximalIdeal
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L)) β)))).toNat : ℕ) : ℝ) *
      Real.log ((Ideal.absNorm v.maximalIdeal.asIdeal : ℕ) : ℝ) := by
  have hval := valuation_eq_exp_neg_count v.maximalIdeal hβ
  have hvβ : v β = (((Ideal.absNorm v.maximalIdeal.asIdeal : ℕ) : ℝ)) ^
      (-(FractionalIdeal.count L v.maximalIdeal (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers L)) β))) := by
    rw [← NumberField.FinitePlace.norm_embedding_eq v β,
      NumberField.FinitePlace.norm_embedding', hval, toNNReal_exp,
      NNReal.coe_zpow, NNReal.coe_natCast]
  rw [hvβ, Real.log_zpow, posLog_int_mul _ (Real.log_nonneg (by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).le))]

end Work.BW
