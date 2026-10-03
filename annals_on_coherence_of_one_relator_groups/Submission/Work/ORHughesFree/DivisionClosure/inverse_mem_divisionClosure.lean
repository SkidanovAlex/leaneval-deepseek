import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.mem_divisionClosure_iff

namespace Work.ORHughesFree.DivisionClosure

/-- The division closure is closed under inverses in `S`: if `x` lies in
`divisionClosure R` and `y` is a two-sided inverse of `x` in `S`, then `y` also lies in
`divisionClosure R`. -/
theorem inverse_mem_divisionClosure {S : Type*} [Ring S] {R : Set S} {x y : S}
    (hx : x ∈ (divisionClosure R : Set S)) (h1 : x * y = 1) (h2 : y * x = 1) :
    y ∈ (divisionClosure R : Set S) := by
  obtain ⟨n, hn⟩ := (mem_divisionClosure_iff R x).mp hx
  refine le_iSup (divisionClosureChain R) (n + 1) ?_
  exact Subring.subset_closure (Set.mem_union_right _ ⟨x, hn, h1, h2⟩)

end Work.ORHughesFree.DivisionClosure
