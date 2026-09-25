import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.EisFactor

universe u

namespace NK.LocalReciprocityLubinTate.Unramified

open Polynomial

/-- In the quotient by the ideal `(P)` the standard Lubin–Tate polynomial `P·X + X^q` becomes
`X^q`. -/
private lemma map_mk_LTpoly_eq {A : Type u} [CommRing A] (P : A) (q : ℕ) :
    (LTpoly P q).map (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) = X ^ q := by
  have hP : Ideal.Quotient.mk (Ideal.span ({P} : Set A)) P = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton P))
  simp only [LTpoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_pow, hP, Polynomial.C_0, zero_mul, zero_add]

/-- In the quotient by the ideal `(P)` the iterate `f^{(m)}` of `P·X + X^q` becomes `X^(q^m)`:
`f^{(m)} ≡ X^(q^m) mod (P)`. -/
private lemma map_mk_LTpolyIter {A : Type u} [CommRing A] (P : A) (q m : ℕ) :
    (LTpolyIter P q m).map (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) = X ^ (q ^ m) := by
  induction m with
  | zero => rw [LTpolyIter_zero, Polynomial.map_X, pow_zero, pow_one]
  | succ m ih =>
    rw [LTpolyIter_succ, Polynomial.map_comp, ih, map_mk_LTpoly_eq, Polynomial.pow_comp,
      Polynomial.X_comp, ← pow_mul, ← pow_succ']

/-- In the quotient by the ideal `(P)` the Eisenstein factor `E = (f^{(n)})^{q-1} + P` becomes
`X^((q-1)q^n)`. -/
private lemma map_mk_LTpolyEis {A : Type u} [CommRing A] (P : A) (q n : ℕ) :
    (LTpolyEis P q n).map (Ideal.Quotient.mk (Ideal.span ({P} : Set A)))
      = X ^ ((q - 1) * q ^ n) := by
  have hP : Ideal.Quotient.mk (Ideal.span ({P} : Set A)) P = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton P))
  simp only [LTpolyEis, Polynomial.map_add, Polynomial.map_pow, map_mk_LTpolyIter,
    Polynomial.map_C, hP, Polynomial.C_0, add_zero, ← pow_mul, Nat.mul_comm]

/-- **All coefficients of the Eisenstein factor below the top one are divisible by `π`.**

For a commutative ring `A`, `P ∈ A` and `q ≥ 2`, the Eisenstein factor
`E = LTpolyEis P q n = (f^{(n)})^{q-1} + P` of the standard Lubin–Tate polynomial `f = P·X + X^q` is
congruent to `X^((q-1)q^n)` modulo `P`: every coefficient of index `< (q-1)q^n` lies in the ideal
`(P)`.  (Together with `LTpolyEis_shape`, which gives `E.coeff 0 = P` and
`E.coeff ((q-1)q^n) = 1`, this is the Newton-polygon shape used to compute the valuation of a root
of `E`.)

PROOF ROUTE.  `LTpolyIter P q (m+1) = (LTpoly P q).comp (LTpolyIter P q m)` and
`LTpoly P q = P·X + X^q ≡ X^q` mod `(P)`, so by induction `LTpolyIter P q m ≡ X^(q^m)` mod `(P)`
(a congruence of polynomials modulo the ideal `(P)`, coefficientwise).  Then
`LTpolyEis P q n = (LTpolyIter P q n)^(q-1) + C P ≡ X^((q-1)q^n)` mod `(P)`, which is the claim. -/
theorem coeff_LTpolyEis_mem_span_lower {A : Type u} [CommRing A] (P : A) (q n : ℕ) (hq : 2 ≤ q) :
    ∀ i, i < (q - 1) * q ^ n →
      (NK.LocalReciprocityLubinTate.LTpolyEis P q n).coeff i ∈ Ideal.span ({P} : Set A) := by
  intro i hi
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [← Polynomial.coeff_map, map_mk_LTpolyEis, Polynomial.coeff_X_pow,
    if_neg (ne_of_lt hi)]

end NK.LocalReciprocityLubinTate.Unramified
