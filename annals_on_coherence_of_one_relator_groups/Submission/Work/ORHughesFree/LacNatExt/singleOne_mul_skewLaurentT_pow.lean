import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs

namespace Work.ORHughesFree.NaturalExtension

/-- Powers of the variable `t` of the skew Laurent polynomial ring, in normal form. -/
private lemma lacskewLaurentT_pow_aux {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (k : ℕ) :
    (skewLaurentT (R := R)) ^ k = SkewMonoidAlgebra.single (Multiplicative.ofAdd (k : ℤ)) (1 : R) := by
  rw [skewLaurentT]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, SkewMonoidAlgebra.single_mul_single]
    simp

/-- In `Multiplicative ℤ`, multiplying `ofAdd 1` on the left of `ofAdd k` adds the exponents. -/
private lemma lacofAdd_one_mul_aux (k : ℕ) :
    (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) * Multiplicative.ofAdd (k : ℤ)
      = Multiplicative.ofAdd ((k : ℤ) + 1) := by
  rw [← ofAdd_add]
  congr 1
  omega

theorem lacsingleOne_mul_skewLaurentT_pow {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (r : R) (k : ℕ) :
    SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) r * (skewLaurentT : SkewL R) ^ k =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k : ℤ) + 1)) r := by
  rw [lacskewLaurentT_pow_aux, SkewMonoidAlgebra.single_mul_single, lacofAdd_one_mul_aux,
    MulSemiringAction.smul_one, mul_one]

end Work.ORHughesFree.NaturalExtension
