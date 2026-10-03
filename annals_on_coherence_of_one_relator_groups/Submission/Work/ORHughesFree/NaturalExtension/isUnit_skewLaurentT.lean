import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension

universe u

namespace Work.ORHughesFree.NaturalExtension

theorem isUnit_skewLaurentT {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] : IsUnit (skewLaurentT (R := R)) := by
  refine ⟨⟨skewLaurentT, SkewMonoidAlgebra.single (Multiplicative.ofAdd (-1)) (1 : R), ?_, ?_⟩, rfl⟩
  · rw [skewLaurentT, SkewMonoidAlgebra.single_mul_single]; simp
  · rw [skewLaurentT, SkewMonoidAlgebra.single_mul_single]; simp

end Work.ORHughesFree.NaturalExtension
