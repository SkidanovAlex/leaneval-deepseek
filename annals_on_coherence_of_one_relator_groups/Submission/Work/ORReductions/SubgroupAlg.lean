/-
Copyright (c) 2026 The contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The group algebra of a subgroup inside the group algebra of the group

For a subgroup `H ≤ G` and a semiring `K`, this file defines the canonical inclusion
`subgroupAlgMap H K : K[H] →+* K[G]` and the "coset component" of an element of `K[G]`
along a left coset of `H`.
-/
import Submission.Work.ORReductions.Basic
import Mathlib.GroupTheory.Index

set_option autoImplicit false

namespace Work.ORReductions

open MonoidAlgebra

variable {G : Type*} [Group G] {K : Type*}

/-- The canonical inclusion of the group algebra of a subgroup into the group algebra of the
group, induced by `H →* G`. -/
noncomputable def subgroupAlgMap (H : Subgroup G) (K : Type*) [Semiring K] :
    MonoidAlgebra K H →+* MonoidAlgebra K G :=
  MonoidAlgebra.mapDomainRingHom K H.subtype

/-- The component of `x : K[G]` supported on the left coset `q ∈ G ⧸ H`.
(Here `G ⧸ H` is the space of left cosets `gH`, i.e. the quotient by `QuotientGroup.leftRel H`.) -/
noncomputable def cosetComponent (H : Subgroup G) (K : Type*) [Semiring K]
    (q : G ⧸ H) (x : MonoidAlgebra K G) :
    MonoidAlgebra K G :=
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  MonoidAlgebra.ofCoeff
    (Finsupp.filter (fun g => (Quotient.mk (QuotientGroup.leftRel H) g : G ⧸ H) = q) x.coeff)

end Work.ORReductions
