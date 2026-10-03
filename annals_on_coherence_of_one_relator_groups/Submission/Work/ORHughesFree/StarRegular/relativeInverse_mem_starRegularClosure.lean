import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff

namespace Work.ORHughesFree.StarRegular

open Work.ORHughesFree

/-- Every relative (Moore--Penrose) inverse of an element of the ∗-regular closure of `R` again
lies in that closure.

Indeed, if `x ∈ (starRegularChain R n)` then `y` lies in `relativeInverses (starRegularChain R n)`,
which is one of the two sets whose ∗-subring closure is `starRegularChain R (n+1)`. -/
theorem relativeInverse_mem_starRegularClosure {U : Type*} [Ring U] [StarRing U]
    {R : StarSubring U} {x y : U} (hx : x ∈ (starRegularClosure R : Set U))
    (hy : IsRelativeInverse x y) : y ∈ (starRegularClosure R : Set U) := by
  obtain ⟨n, hn⟩ := (mem_starRegularClosure_iff R x).mp hx
  refine (mem_starRegularClosure_iff R y).mpr ⟨n + 1, ?_⟩
  exact subset_starSubringClosure _ (Or.inr ⟨x, hn, hy⟩)

end Work.ORHughesFree.StarRegular
