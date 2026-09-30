import Mathlib
import Submission.Work.KeyLemma.Sum
import Submission.Work.KeyLemma.Sum.toDiv_injective
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.KeyLemma.Curve

open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

variable {k : Type u} [Field k]

/-! ## The divisor of a `p`-th power

The first ingredient is `div (u ^ p) = p • div u`: the order of vanishing is additive over
products (`Curve.div_mul`), so it is `ℕ`-linear over powers.  The two degenerate cases
(`u = 0`, and `p = 0` where `u ^ 0 = 1`) are handled by `Curve.div_zero` and `Curve.div_one`. -/

/-- The divisor of a `p`-th power: `div (u ^ p) = p • div u`. -/
theorem div_pow (C : Work.CurveBasics.Curve k) (u : C.functionField) (p : ℕ) :
    C.div (u ^ p) = p • C.div u := by
  rcases eq_or_ne u 0 with rfl | hu
  · rcases Nat.eq_zero_or_pos p with rfl | hp
    · rw [pow_zero, div_one, zero_smul]
    · rw [zero_pow hp.ne', Work.CurveBasics.Curve.div_zero, smul_zero]
  · induction p with
    | zero => rw [pow_zero, div_one, zero_smul]
    | succ p ih =>
      rw [pow_succ, Work.CurveBasics.Curve.div_mul C (pow_ne_zero p hu) hu, ih, succ_nsmul]

/-- The divisor of zeros of a `p`-th power is `p` times the divisor of zeros: this is
`div_pow` together with the pointwise identity `max (p * n) 0 = p * max n 0` (`p ≥ 0`). -/
theorem posPart_pow (C : Work.CurveBasics.Curve k) (u : C.functionField) (p : ℕ) :
    posPart C (u ^ p) = p • posPart C u := by
  ext Q
  have h : C.div (u ^ p) Q = (p : ℤ) * C.div u Q := by
    rw [div_pow, Finsupp.smul_apply, nsmul_eq_mul]
  rw [posPart, posPart, Finsupp.mapRange_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
    nsmul_eq_mul, h]
  by_cases hle : 0 ≤ C.div u Q
  · rw [max_eq_left (mul_nonneg (Nat.cast_nonneg p) hle), max_eq_left hle]
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p) (le_of_lt (not_le.mp hle))),
      max_eq_right (le_of_lt (not_le.mp hle)), mul_zero]

namespace SumDiv

/-- `toDiv` is `ℕ`-linear: the divisor of `n • s` is `n` times the divisor of `s`. -/
theorem toDiv_nsmul (C : Work.CurveBasics.Curve k) (n : ℕ) (s : SumDiv C) :
    toDiv C (n • s) = n • toDiv C s := by
  induction n with
  | zero => rw [zero_nsmul, toDiv_zero, zero_nsmul]
  | succ n ih => rw [succ_nsmul, toDiv_add, ih, succ_nsmul]

/-- The sum of the images of the points of `n • s` is the `n`-th power of the sum for `s`:
the sum of images is a homomorphism of additive monoids into the commutative group `A(k)`,
and `n`-fold addition of an effective divisor corresponds to `n`-fold multiplication. -/
theorem sumOfPoints_nsmul (C : Work.CurveBasics.Curve k)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A) (n : ℕ) (s : SumDiv C) :
    sumOfPoints C f (n • s) = (sumOfPoints C f s) ^ n := by
  induction n with
  | zero => rw [zero_nsmul, sumOfPoints_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, sumOfPoints_add, ih, pow_succ]

end SumDiv

/-- **The inseparable case is a `p`-th power.**  If `h = u ^ p` for a rational function `u` on `C`
and `p : ℕ`, then `div h = p • div u` (from `Curve.div_mul`), hence `posPart h = p • posPart u`
and `negPart h = p • negPart u`.  Consequently a multiset `s` presenting `posPart h` is `p • sp`
for any multiset `sp` presenting `posPart u` (by `Work.KeyLemma.Sum.toDiv_injective`), and the sum
of the images of the points of `s` in a commutative group scheme is the `p`-th power of the
corresponding sum for `sp`.

This is the reduction step of the inseparable case of the pencil lemma: if `K(C)/k(h)` is not
separable then `h = u ^ p` with `[K(C) : k(u)] = [K(C) : k(h)] / p < [K(C) : k(h)]`
(`Work.CurveBasics.Order.exists_pow_eq_of_not_separable` together with
`Work.CurveBasics.Order.finrank_adjoin_pow_eq_prime`), so the statement for `h` follows from the
statement for `u` by induction on the degree. -/
theorem sumOfPoints_pow_of_pow_eq {k : Type u} [Field k] {p : ℕ}
    {C : Work.CurveBasics.Curve k}
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A) {h u : C.functionField} (hu : u ^ p = h)
    (s sp : Work.KeyLemma.Curve.SumDiv C)
    (hs : Work.KeyLemma.Curve.SumDiv.toDiv C s = Work.KeyLemma.Curve.posPart C h)
    (hsp : Work.KeyLemma.Curve.SumDiv.toDiv C sp = Work.KeyLemma.Curve.posPart C u) :
    Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s =
      (Work.KeyLemma.Curve.SumDiv.sumOfPoints C f sp) ^ p := by
  -- `h = u ^ p`, so the divisors presented by `s` and by `p • sp` agree.
  have hto : SumDiv.toDiv C s = SumDiv.toDiv C (p • sp) := by
    rw [hs, ← hu, posPart_pow, SumDiv.toDiv_nsmul, hsp]
  -- `toDiv` is injective, so the multisets themselves agree.
  have hsp' : s = p • sp := Work.KeyLemma.Sum.toDiv_injective C hto
  rw [hsp', SumDiv.sumOfPoints_nsmul]

end Work.KeyLemma.Curve
