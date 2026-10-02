import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.Crux.ovl_transport
import Submission.Work.Cohomology.Crux.relCapPair_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 2000000

namespace Work.Cohomology.Crux

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

/-- Transport of unimodularity from the model pair `(PairXT, PairAT)` to the overlap
`(vkOvl, vkOvlA)`.  (Re-proves `Crux.vkOvl_unimodular_of_pair_map` in a module that does not
disable the transparency of `isDefEq` and using explicit `@`-applications, which makes the heavy
implicit-argument inference instant.) -/
theorem ovlUnimodularOfPairMap (f : vkOvl ⟶ Work.Cohomology.PairXT)
    (g : TopCat.of ↥(vkOvlA) ⟶ TopCat.of Work.Cohomology.PairAT)
    (w : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl vkOvl vkOvlA) f
      = CategoryTheory.CategoryStruct.comp g
          (Work.Cohomology.subtypeIncl Work.Cohomology.PairXT Work.Cohomology.PairAT))
    (h3 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ vkOvl Work.Cohomology.PairXT f) 3))
    (h7 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf vkOvl Work.Cohomology.PairXT
        vkOvlA Work.Cohomology.PairAT f g w) 7))
    (hw : ∃ wm : (Work.Cohomology.relChains Work.Cohomology.PairXT
        Work.Cohomology.PairAT).homology 7,
      Function.Surjective (fun u : Work.Cohomology.relCohomology ℤ Work.Cohomology.PairXT
        Work.Cohomology.PairAT 4 =>
        Work.Cohomology.relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 u wm)) :
    ∃ w' : (Work.Cohomology.relChains vkOvl vkOvlA).homology 7,
      Function.Surjective (fun u : Work.Cohomology.relCohomology ℤ vkOvl vkOvlA 4 =>
        Work.Cohomology.relCapPair vkOvl vkOvlA 4 3 u w') := by
  have hp : ∀ x ∈ vkOvlA, f x ∈ Work.Cohomology.PairAT :=
    @mem_of_comp_eq vkOvl Work.Cohomology.PairXT vkOvlA Work.Cohomology.PairAT f g w
  have hg' : g = Work.Cohomology.relMapSub vkOvlA Work.Cohomology.PairAT f hp :=
    @relMapSub_eq_of_comp_eq vkOvl Work.Cohomology.PairXT vkOvlA Work.Cohomology.PairAT
      f hp g w
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf vkOvl Work.Cohomology.PairXT vkOvlA
        Work.Cohomology.PairAT f (Work.Cohomology.relMapSub vkOvlA Work.Cohomology.PairAT f hp)
        (Work.Cohomology.relMapSub_spec vkOvlA Work.Cohomology.PairAT f hp)) 7).hom := by
    rw [← @relChainsMapOf_congr_sub vkOvl Work.Cohomology.PairXT vkOvlA Work.Cohomology.PairAT
      f hp g w hg']
    exact (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf vkOvl Work.Cohomology.PairXT
        vkOvlA Work.Cohomology.PairAT f g w) 7)).2
  have hinj : Function.Injective (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ vkOvl Work.Cohomology.PairXT f) 3).hom :=
    (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ vkOvl Work.Cohomology.PairXT f) 3)).1
  exact @exists_unimodular_of_natural vkOvl Work.Cohomology.PairXT vkOvlA
    Work.Cohomology.PairAT f hp 4 3
    (fun a c => @relCapPair_natural vkOvl Work.Cohomology.PairXT vkOvlA Work.Cohomology.PairAT
      f hp 4 3 a c) hsurj hinj hw

end

end Work.Cohomology.Crux
