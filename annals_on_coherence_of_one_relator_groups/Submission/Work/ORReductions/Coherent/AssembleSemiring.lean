import Mathlib
import Submission.Work.ORReductions.SubgroupAlg
import Submission.Work.ORReductions.SubgroupAlg.ker_le_span_of_subgroup

/-!
# The assembly map `(G ⧸ H) →₀ K[H] → K[G]` over a semiring

`K[G]` is the direct sum, over the left cosets `q ∈ G ⧸ H`, of the copies
`single (Quotient.out q) 1 * K[H]` of `K[H]`.  This file defines the resulting assembly map

`assembleS H K c = ∑ q, single (Quotient.out q) 1 * subgroupAlgMap H K (c q)`

at the level of *semirings* `K` (no commutativity assumption), which is what the flatness
arguments of the coherence proof require.
-/

namespace Work.ORReductions.Coherent

open MonoidAlgebra

/-- Assembly of an element of `(G ⧸ H) →₀ K[H]` into an element of `K[G]`: the component at the
coset `q` is placed on the coset `q` using the representative `Quotient.out q`.  Unlike
`Work.ORReductions.SubgroupAlg.assemble` this is defined for an arbitrary *semiring* `K`. -/
noncomputable def assembleS {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Semiring K]
    (c : (G ⧸ H) →₀ MonoidAlgebra K H) : MonoidAlgebra K G :=
  c.sum fun q r => MonoidAlgebra.single (Quotient.out q) (1 : K) *
    Work.ORReductions.subgroupAlgMap H K r

end Work.ORReductions.Coherent
