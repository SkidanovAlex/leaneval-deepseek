import Mathlib
import Submission.Work.TameArithmetic.Defs

set_option linter.style.haveILetI false

namespace Work.TameArithmetic

/-- Every finite quotient of a group `G` modelling the maximal tame pro-`2` extension `K` is a
`2`-group: the model condition realises it as the Galois group of a finite Galois extension `L/ℚ`
embedding into `K`, and the sub-clause of `K` says every such `L` has pro-`2` Galois group. -/
theorem isPGroup_two_quotient_of_model {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hsub : Work.TameArithmetic.TameSubClause K) {G : Type} [Group G]
    (hmodel : Work.TameArithmetic.IsProTwoModel K G) :
    ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N) := by
  intro N _ hfin
  obtain ⟨L, _iL, _iAL, _iFd, _iGal, φ, hinj, he⟩ := hmodel N hfin
  haveI : NumberField L := NumberField.of_module_finite ℚ L
  obtain ⟨hpro, _⟩ := hsub L φ hinj
  obtain ⟨e⟩ := he
  exact IsPGroup.of_equiv hpro e

end Work.TameArithmetic
