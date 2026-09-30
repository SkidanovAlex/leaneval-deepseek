import Mathlib
import Submission.Work.ThreeConnected.Excision.PairVanish
import Submission.Work.Cohomology.relCohMV_honest_prereq

namespace Work.ThreeConnected.Excision

/-- The `inclSubtype` of an inclusion of subsets is the same morphism as
`Work.Cohomology.HMV.subInclSub`. -/
theorem inclSubtype_eq_subInclSub {X : TopCat.{0}} {B C : Set X} (hBC : B ⊆ C) :
    inclSubtype hBC = Work.Cohomology.HMV.subInclSub hBC := rfl

theorem smallInToSingA_subInclChain {X : TopCat.{0}} (U V B C : Set X) (hBC : B ⊆ C) :
    CategoryTheory.CategoryStruct.comp (Work.Cohomology.smallInToSingA U V B)
        (Work.Cohomology.chainMap ℤ (TopCat.of B) (TopCat.of C)
          (Work.ThreeConnected.Excision.inclSubtype hBC))
      = CategoryTheory.CategoryStruct.comp (Work.Cohomology.subInclChain U V hBC)
          (Work.Cohomology.smallInToSingA U V C) := by
  rw [inclSubtype_eq_subInclSub hBC]
  exact (Work.Cohomology.HMV.subInclChain_gen_natural' U V hBC).symm

end Work.ThreeConnected.Excision
