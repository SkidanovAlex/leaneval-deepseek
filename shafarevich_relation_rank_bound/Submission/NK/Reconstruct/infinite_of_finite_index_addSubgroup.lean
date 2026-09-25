import Mathlib
import Submission.NK.Reconstruct.galToGamma

namespace NK.Reconstruct

/-- An additive subgroup of an infinite additive group with finite quotient is itself
infinite: `G` is the union of `Finite (G ⧸ H)`-many cosets of `H`, each in bijection with `H`,
so a finite `H` would force a finite `G`. -/
theorem infinite_of_finite_index_addSubgroup {G : Type*} [AddCommGroup G] [Infinite G]
    (H : AddSubgroup G) (hH : Finite (G ⧸ H)) : Infinite H :=
  Infinite.mk fun hHfin =>
    (inferInstance : Infinite G).not_finite
      (@Finite.of_addSubgroup_quotient G _ H hHfin hH)

end NK.Reconstruct
