import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.smallChainsHomotopyEquiv
import Submission.Work.Cohomology.homotopyEquivDual
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.DualComplexMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The small-chain comparison, free of `prod_sphere_aux`

`Submission/Work/Cohomology/prod_sphere_aux.lean` carries three unrelated things: the definition
`smallIsoHom` (the cohomology map induced by the dual of the inclusion of the small chains), the
compound lemmas `smallOfU_comp_smallToSing'`, and a large amount of product-of-spheres machinery.
The product-of-spheres part re-declares names (for instance `Work.Cohomology.Yt`) that clash with
the transplant in `Submission/Work/Cohomology/CompatTrans/`, which is needed here; and it is only
`smallIsoHom` that is wanted.  This file reproduces the three declarations verbatim in the
namespace `Work.Cohomology.CompatIso`, so that modules which cannot have `prod_sphere_aux` in
their import closure can still use the small-chain comparison.
-/

open CategoryTheory Limits

namespace Work.Cohomology.CompatIso

noncomputable section

/-- `smallOfU U V ≫ smallToSing U V = inclChains X U` (verbatim copy of
`Work.Cohomology.smallOfU_comp_smallToSing'`). -/
lemma smallOfU_comp_smallToSing' {X : TopCat} (U V : Set X) :
    smallOfU U V ≫ smallToSing U V = inclChains X U := by
  have hlift : smallLiftU U V ≫ (smallSubcomplex U V).ι = TopCat.toSSet.map (inclUX U) :=
    SSet.Subcomplex.lift_ι _ _
  show SSet.chainComplexMap (smallLiftU U V) (ModuleCat.of ℤ ℤ) ≫
      SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ) = _
  rw [← Functor.map_comp, hlift]
  rfl

/-- The dual of the inclusion of the small chains, as a cohomology map (verbatim copy of
`Work.Cohomology.smallIsoHom`). -/
noncomputable def smallIsoHom {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    singularCohomology ℤ n X ⟶ HomologicalComplex.homology (dualComplex ℤ (smallChains U V)) n :=
  HomologicalComplex.homologyMap
    (dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V)) n

/-- The `U`-component of `smallIsoHom` (verbatim copy of
`Work.Cohomology.smallIsoHom_comp_smallOfU`). -/
lemma smallIsoHom_comp_smallOfU {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    smallIsoHom U V hU hV hcov n
      ≫ HomologicalComplex.homologyMap (dualComplexMap ℤ (singularChains ℤ (TopCat.of U))
          (smallChains U V) (smallOfU U V)) n
      = singularCohomologyMap ℤ (TopCat.of U) X (subtypeIncl X U) n := by
  show HomologicalComplex.homologyMap
      (dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V)) n
      ≫ HomologicalComplex.homologyMap
        (dualComplexMap ℤ (singularChains ℤ (TopCat.of U)) (smallChains U V) (smallOfU U V)) n = _
  rw [← HomologicalComplex.homologyMap_comp, ← dualComplexMap_comp, smallOfU_comp_smallToSing']
  rfl

/-- The dual of the inclusion of the small chains induces an isomorphism on cohomology
(verbatim copy of `Work.Cohomology.isIso_smallIsoHom`). -/
theorem isIso_smallIsoHom {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) : IsIso (smallIsoHom U V hU hV hcov n) := by
  obtain ⟨e, he⟩ := smallChainsHomotopyEquiv U V hU hV hcov
  show IsIso (HomologicalComplex.homologyMap
    (dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V)) n)
  rw [← he]
  refine IsIso.mk ⟨HomologicalComplex.homologyMap
    (dualComplexMap ℤ (singularChains ℤ X) (smallChains U V) e.inv) n, ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp,
      ← dualComplexMap_comp (R := ℤ) (f := e.inv) (g := e.hom),
      (dualHomotopy ℤ e.homotopyInvHomId).symm.homologyMap_eq, dualComplexMap_id,
      HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp,
      ← dualComplexMap_comp (R := ℤ) (f := e.hom) (g := e.inv),
      (dualHomotopy ℤ e.homotopyHomInvId).symm.homologyMap_eq, dualComplexMap_id,
      HomologicalComplex.homologyMap_id]

end

end Work.Cohomology.CompatIso
