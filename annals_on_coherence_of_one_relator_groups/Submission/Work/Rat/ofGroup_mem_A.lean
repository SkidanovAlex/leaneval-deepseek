import Mathlib
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.exists_source_subgroup_weak
import Submission.Work.ORHughesFree.Rat.A_ofGroup

namespace Work.Rat

/-- The image of `U` in `Rat(U)` meets `Rat.A V` exactly in `V`: if the image of a group element
`u : U` lies in the image of `Rat(V) → Rat(U)`, then `u ∈ V`.

This is `Work.ORHughesFree.Rat.A_ofGroup`, whose proof shows more: such an element of `Rat(V)`
is itself `ofGroup v` for a group element `v : V`, and injectivity of `ofGroup` forces `u = v`. -/
theorem ofGroup_mem_A {U : Type} [Group U] {V : Subgroup U} {u : U} :
    Work.ORHughesFree.RatU.ofGroup u ∈ Work.ORHughesFree.Rat.A V → u ∈ V :=
  Work.ORHughesFree.Rat.A_ofGroup

end Work.Rat
