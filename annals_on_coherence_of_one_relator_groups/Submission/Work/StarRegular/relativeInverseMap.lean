import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.StarRegular

theorem relativeInverseMap {U : Type*} [Ring U] [StarRing U] {x y : U}
    (h : Work.ORHughesFree.IsRelativeInverse x y) (f : U →+* U)
    (hf : ∀ a : U, f (star a) = star (f a)) :
    Work.ORHughesFree.IsRelativeInverse (f x) (f y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, h.left]
  · rw [← map_mul, ← map_mul, h.right]
  · rw [← map_mul, ← hf, h.star_left]
  · rw [← map_mul, ← hf, h.star_right]

end Work.StarRegular
