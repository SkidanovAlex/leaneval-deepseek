import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.LI.locallyIndicable_prod

namespace Work.ORTorsion.GroupOps

open scoped TensorProduct
open Work.ORTorsion

/-- **A finitely generated subgroup of `G` not contained in `N` is indicable when `G ⧸ N` is
locally indicable.**

The image `H.map (mk' N)` of `H` in `G ⧸ N` is finitely generated (image of a finitely generated
subgroup) and nontrivial (since `H ⊄ N`), so local indicability of `G ⧸ N` supplies a surjection
`H.map (mk' N) →* Multiplicative ℤ`; pulling it back along the surjection `H →* H.map (mk' N)`
gives a surjection out of `H`. -/
theorem surjective_of_locallyIndicable_quotient {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (h : Work.ORLocInd.Group.LocallyIndicable (G ⧸ N)) (H : Subgroup G)
    (hFG : H.FG) (hne : H.map (QuotientGroup.mk' N) ≠ ⊥) :
    ∃ φ : H →* Multiplicative ℤ, Function.Surjective φ :=
  Work.ORLocInd.LI.indicable_of_map_ne_bot (QuotientGroup.mk' N) h hFG hne

end Work.ORTorsion.GroupOps
