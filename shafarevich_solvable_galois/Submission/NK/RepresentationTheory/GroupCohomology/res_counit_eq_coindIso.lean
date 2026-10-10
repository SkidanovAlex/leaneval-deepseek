import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Submission.NK.RepresentationTheory.GroupCohomology.coindIso_hom_eq
import Submission.NK.RepresentationTheory.GroupCohomology.key_chain_identity_counit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace NK.RepresentationTheory.GroupCohomology

open CategoryTheory Limits

/-- Auxiliary proof of the main theorem, conditional on the two chain-level inputs
(the chain-level identity `key_chain_identity_counit` and the expansion of `coindIso`). -/
theorem res_counit_eq_coindIso_of {k G : Type} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) (A : Rep.{0, 0, 0} k S) (n : ℕ)
    (hchain : CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp
          (groupCohomology.inhomogeneousCochainsIso (Rep.coind S.subtype A)).hom
          (lambdaIso k G S A).symm.hom)
        (psiMap k G S A) =
      CategoryTheory.CategoryStruct.comp
        (groupCohomology.cochainsMap S.subtype
          ((Rep.resCoindAdjunction k S.subtype).counit.app A))
        (groupCohomology.inhomogeneousCochainsIso A).hom)
    (hexp : (groupCohomology.coindIso (k := k) (S := S) A n).hom =
      CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.homologyMap
            (CategoryTheory.Iso.hom (CategoryTheory.Iso.trans
              (groupCohomology.inhomogeneousCochainsIso (Rep.coind S.subtype A))
              (lambdaIso k G S A).symm)) n)
          (HomologicalComplex.homologyMap (psiMap k G S A) n))
        (isoOfQuasiIsoAt
          (HomotopyEquiv.ofIso (groupCohomology.inhomogeneousCochainsIso A)).hom n).inv) :
    CategoryTheory.CategoryStruct.comp
        ((groupCohomology.resNatTrans k (G := S) (H := G) S.subtype n).app (Rep.coind S.subtype A))
        (groupCohomology.map (MonoidHom.id S)
          ((Rep.resCoindAdjunction k S.subtype).counit.app A) n) =
      (groupCohomology.coindIso (k := k) (S := S) A n).hom
:= by
  have hA : CategoryTheory.CategoryStruct.comp
        ((groupCohomology.resNatTrans k (G := S) (H := G) S.subtype n).app (Rep.coind S.subtype A))
        (groupCohomology.map (MonoidHom.id S)
          ((Rep.resCoindAdjunction k S.subtype).counit.app A) n) =
      groupCohomology.map S.subtype ((Rep.resCoindAdjunction k S.subtype).counit.app A) n := by
    rw [groupCohomology.resNatTrans_app]
    show HomologicalComplex.homologyMap
          (groupCohomology.cochainsMap S.subtype
            (𝟙 (Rep.res S.subtype (Rep.coind S.subtype A)))) n ≫
        HomologicalComplex.homologyMap
          (groupCohomology.cochainsMap (MonoidHom.id S)
            ((Rep.resCoindAdjunction k S.subtype).counit.app A)) n =
      HomologicalComplex.homologyMap
        (groupCohomology.cochainsMap S.subtype
          ((Rep.resCoindAdjunction k S.subtype).counit.app A)) n
    rw [← HomologicalComplex.homologyMap_comp]
    congr 1
  rw [hA]
  change groupCohomology.map S.subtype
      ((Rep.resCoindAdjunction k S.subtype).counit.app A) n =
    (groupCohomology.coindIso (k := k) (S := S) A n).hom
  rw [hexp]
  rw [Iso.trans_hom]
  rw [← HomologicalComplex.homologyMap_comp]
  rw [hchain]
  rw [HomologicalComplex.homologyMap_comp]
  have hqh : (isoOfQuasiIsoAt
      (HomotopyEquiv.ofIso (groupCohomology.inhomogeneousCochainsIso A)).hom n).hom =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n := rfl
  rw [← hqh]
  rw [Category.assoc]
  rw [Iso.hom_inv_id]
  change groupCohomology.map S.subtype
      ((Rep.resCoindAdjunction k S.subtype).counit.app A) n =
    HomologicalComplex.homologyMap
      (groupCohomology.cochainsMap S.subtype
        ((Rep.resCoindAdjunction k S.subtype).counit.app A)) n
  rfl

/-- **The counit form of Shapiro's lemma**: restriction along `S ≤ G` followed by the map on
cohomology induced by the counit of the restriction–coind adjunction is Shapiro's isomorphism. -/
theorem res_counit_eq_coindIso {k G : Type} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) (A : Rep.{0, 0, 0} k S) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp
        ((groupCohomology.resNatTrans k (G := S) (H := G) S.subtype n).app (Rep.coind S.subtype A))
        (groupCohomology.map (MonoidHom.id S)
          ((Rep.resCoindAdjunction k S.subtype).counit.app A) n) =
      (groupCohomology.coindIso (k := k) (S := S) A n).hom :=
  res_counit_eq_coindIso_of S A n (key_chain_identity_counit S A) (coindIso_hom_eq S A n)

end NK.RepresentationTheory.GroupCohomology
