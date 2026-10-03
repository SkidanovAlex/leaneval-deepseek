import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension

namespace Work.ORHughesFree.Section6

theorem skewL_single_one_smul {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (m : Multiplicative ℤ) (a : A) :
    SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (m • a) =
      SkewMonoidAlgebra.single m (1 : A) * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a *
        SkewMonoidAlgebra.single m⁻¹ (1 : A) := by
  rw [SkewMonoidAlgebra.single_mul_single, SkewMonoidAlgebra.single_mul_single]
  simp

end Work.ORHughesFree.Section6
