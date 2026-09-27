import Mathlib
import Submission.Work.Cohomology.cokerSmallAux
import Submission.Work.Cohomology.excisionAux

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

/-- The naturality square comparing the chains of `V ∩ A` in the two ways: the inclusion
`C_*(V ∩ A) → C_*(V)` followed by the map `C_*(V) → smallChains A V` equals the map
`C_*(V ∩ A) → C_*(A)` (induced by the inclusion of `V ∩ A` into `A`) followed by
`C_*(A) → smallChains A V`.  This is the statement `incl ≫ smallOfV = w ≫ smallOfU`.

Suggested route: both sides are `SSet.chainComplexMap` of simplicial maps into the subcomplex
`smallSSet A V ⊆ toSSet.obj X`; it suffices to compare them (a map into a subcomplex is determined
by its composite with the inclusion), and both composites with `(smallSubcomplex A V).ι` are
`toSSet.map` of the two inclusions `V ∩ A → X`, which agree because both send `x ↦ (x : V : X)`.

Note that `Work.Cohomology.smallOfU_comp_smallToSing` and `smallOfV_comp_smallToSing`
(`Submission/Work/Cohomology/excisionAux.lean`) are available: rewriting both sides with
`smallToSing A V` on the right turns the goal into an equality of composites of `inclChains`, which
follows from `Work.Cohomology.overlapIncl_comp_subtypeIncl` and the functoriality of `chainMap`,
using that `smallToSing A V` is a monomorphism (degreewise injective, see
`Work.Cohomology.smallToSing_f_injective`). -/
theorem inclChains_comp_smallOfV (X : TopCat) (A V : Set X) :
    CategoryTheory.CategoryStruct.comp (inclChains (TopCat.of V) (relSubset A V)) (smallOfV A V)
      = CategoryTheory.CategoryStruct.comp (overlapChainsMap A V) (smallOfU A V) := by
  haveI : Mono (smallToSing A V) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    rw [ModuleCat.mono_iff_injective]
    exact smallToSing_f_injective A V n
  apply (cancel_mono (smallToSing A V)).1
  rw [Category.assoc, Category.assoc, smallOfV_comp_smallToSing, smallOfU_comp_smallToSing]
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp only [overlapIncl_comp_subtypeIncl]

end Work.Cohomology
