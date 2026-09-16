import Mathlib.FieldTheory.Finite.Basic

namespace Commons.Algebra.Polynomial

open _root_.Polynomial

set_option linter.style.haveILetI false

/-- For a finite field `F` of cardinality `q` and a commutative `F`-algebra `K` of characteristic
`p = ringChar F`, the Frobenius `x ↦ x ^ q` commutes with polynomial evaluation:
`(aeval x a) ^ q = aeval (x ^ q) a`.  (The point is that the coefficients of `a` lie in `F` and are
fixed by `c ^ q = c`.) -/
theorem aeval_pow_card {F K : Type*} [Field F] [Finite F] [CommRing K] [Algebra F K]
    [CharP K (ringChar F)] (x : K) (a : Polynomial F) :
    (Polynomial.aeval x a) ^ (Nat.card F) = Polynomial.aeval (x ^ (Nat.card F)) a := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Nat.card F := Fintype.card_eq_nat_card
  have hleft : (Polynomial.aeval x a) ^ (Nat.card F)
      = (FiniteField.frobeniusAlgHom F K) (Polynomial.aeval x a) := by
    rw [FiniteField.coe_frobeniusAlgHom, hcard]
  have hσx : (FiniteField.frobeniusAlgHom F K) x = x ^ (Nat.card F) := by
    rw [FiniteField.coe_frobeniusAlgHom, hcard]
  have hcomp : (FiniteField.frobeniusAlgHom F K) (Polynomial.aeval x a)
      = Polynomial.aeval (x ^ (Nat.card F)) a := by
    rw [← hσx]
    exact (DFunLike.congr_fun
      (Polynomial.aeval_algHom (FiniteField.frobeniusAlgHom F K) x) a).symm
  exact hleft.trans hcomp

end Commons.Algebra.Polynomial