import Mathlib
import Submission.Work.DSPB5.Basic

namespace Work.DSPB5

universe u

/-! ## Local helper: `x ^ n * y = 0` with `n > 0` forces `x * y = 0` in a reduced monoid

This is the reduction step behind PB5.  It is proved here (rather than imported) so that this
file depends on nothing but `DSMap.Mix` from the area's vocabulary module. -/

/-- In a reduced commutative monoid with zero, `x ^ n * y = 0` with `n > 0` forces `x * y = 0`:
from `h` we get `(x * y) ^ n = x ^ n * y ^ n = (x ^ n * y) * y ^ (n - 1) = 0`, so `x * y` is
nilpotent. -/
private lemma mul_eq_zero_of_pow_mul_eq_zero_aux {M₀ : Type u} [CommMonoidWithZero M₀]
    [IsReduced M₀] {x y : M₀} {n : ℕ} (hn : 0 < n) (h : x ^ n * y = 0) : x * y = 0 := by
  refine eq_zero_of_pow_eq_zero (n := n) ?_
  have hy : y ^ n = y ^ (n - 1) * y := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
  rw [mul_pow, hy, mul_comm (y ^ (n - 1)) y, ← mul_assoc, h, zero_mul]

/-- **PB5, `N`-form** (the form in which the node is consumed by the MIX subtree, node M5b):
in a perfect ring of characteristic a prime `p`, if `t ^ N` annihilates `x`, then *every*
`p`-power root of `t` annihilates `x`.  I.e. `t ^ N`-torsion is almost zero along the tower
`t, t^(1/p), t^(1/p^2), ...`.

Proof route: reduce to `t * x = 0` first (`(t*x)^N = t^N * x * x^(N-1) = 0` and `R` is reduced, up
to the case `N = 0`), then apply `DSMap.Mix.isAlmostZeroAlong_of_mul_eq_zero`.  Auxiliary facts may
be proved locally in this file (give local helpers an `_aux` suffix to avoid name clashes). -/
theorem isAlmostZeroAlong_of_pow_mul_eq_zero (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]
    [CharP R p] [PerfectRing R p] (t x : R) (N : ℕ) (h : t ^ N * x = 0) :
    DSMap.Mix.IsAlmostZeroAlong p R t x := by
  haveI : IsReduced R := DSMap.Mix.instIsReducedOfPerfectRing R p
  refine DSMap.Mix.isAlmostZeroAlong_of_mul_eq_zero p R ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- `N = 0`: the hypothesis reads `1 * x = 0`, i.e. `x = 0`
    subst hN
    rw [pow_zero, one_mul] at h
    rw [h, mul_zero]
  · -- `N > 0`: reduce `t ^ N * x = 0` to `t * x = 0` using reducedness
    exact mul_eq_zero_of_pow_mul_eq_zero_aux hN h

end Work.DSPB5
