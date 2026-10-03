import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs

namespace Work.ORHughesFree.NaturalExtension

theorem lacsum_single_mul_skewLaurentT {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (c : ℕ → R) (d : ℕ) :
    (∑ k : Fin (d + 1), SkewMonoidAlgebra.single (Multiplicative.ofAdd (k : ℤ)) (c (k : ℕ))) *
        (skewLaurentT : SkewL R)
      = ∑ k : Fin (d + 1),
          SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k : ℤ) + 1)) (c (k : ℕ)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [skewLaurentT, SkewMonoidAlgebra.single_mul_single]
  simp only [ofAdd_add, smul_one, mul_one]

end Work.ORHughesFree.NaturalExtension
