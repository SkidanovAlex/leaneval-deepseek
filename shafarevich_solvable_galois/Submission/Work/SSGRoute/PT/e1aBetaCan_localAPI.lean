import Mathlib
import Submission.Work.SSGRoute.ext_localUnits_iso_Q
import Submission.Work.SSGRoute.PT.e1aBetaCan_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local-field transport API at degree two

For the local chain of the landing clause (`PT/NOTE_e1aBetaCan_le_ker.md` § 2, § 5) the local
Ext-group `Ext²_{D_w}(res E', K_wˣ)` has to be transported to the "clean" local field data
`(k_v, Ω_v, K')` produced by the place glue (`localField_subfield_place_compat`), where the
*field-generic* dictionary `Work.SSGRoute.ext_continuous_descent_fg` and the connecting map can be
applied.  The degree-one transport is the proved `Work.SSGRoute.ext_localUnits_iso_Q`; this file
supplies its degree-two companion, by making the two auxiliary functoriality lemmas
(`ext_res_mulEquiv`, `ext_coeff_change`) available in every degree (their proofs are degree-blind).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct

/-- **Restriction along a group isomorphism preserves `Ext` in every degree.**  This is
`ext_res_mulEquiv` with the degree `1` replaced by an arbitrary `n`; the proof is identical, since
`Rep.res` along a group isomorphism is an equivalence of categories and equivalences preserve
`Ext` in every degree. -/
theorem ext_res_mulEquiv_n {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} SSGRoute.PTExt.Coeff G) (n : ℕ) :
    Nonempty (CategoryTheory.Abelian.Ext
        (Rep.res e.symm.toMonoidHom X) (Rep.res e.symm.toMonoidHom Y) n ≃+
      CategoryTheory.Abelian.Ext X Y n) := by
  haveI : (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).IsEquivalence :=
    resFunctor_isEquivalence e
  refine ⟨(AddEquiv.ofBijective
    ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom X Y n) ?_).symm⟩
  exact Functor.mapExt_bijective_of_preservesProjectiveObjects
    (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom) X Y n

/-- **Change of coefficient module along a group isomorphism, in every degree.**  The degree-one
case is `ext_coeff_change` (private to `ext_localUnits_iso_Q`); the proof is the same three-step
composite `ext_congr_right ∘ ext_res_mulEquiv ∘ ext_congr_right`, none of whose ingredients is
degree-specific. -/
theorem ext_coeff_change_n {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (B : Rep.{0} SSGRoute.PTExt.Coeff G') (hi : A ≅ Rep.res e.toMonoidHom B) (n : ℕ) :
    Nonempty (CategoryTheory.Abelian.Ext X A n ≃+
      CategoryTheory.Abelian.Ext (Rep.res e.symm.toMonoidHom X) B n) := by
  obtain ⟨e1⟩ := ext_congr_right (M := X) hi n
  obtain ⟨e2⟩ := ext_res_mulEquiv_n e X (Rep.res e.toMonoidHom B) n
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by
    ext x
    simp
  have hres : Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom B) = B := by
    change Rep.res (e.toMonoidHom.comp e.symm.toMonoidHom) B = B
    rw [hcomp, Rep.res_id]
  obtain ⟨e3⟩ := ext_congr_right (M := Rep.res e.symm.toMonoidHom X) (eqToIso hres) n
  exact ⟨e1.trans (e2.symm.trans e3)⟩

/-- **The degree-two companion of `ext_localUnits_iso_Q`**: the local Ext-group
`Ext²_{D_w}(res E', K_wˣ)` of the place `w = ofFinite q` is the same as the Ext-group over the
intermediate field `K'` of the local closure with coefficients `(K')ˣ`, along the group isomorphism
`eG : D_w ≃* Gal(K'/k_v)`.  This is what makes the *field-generic* dictionary
(`Work.SSGRoute.ext_continuous_descent_fg`) and the connecting map applicable at a place. -/
theorem ext_localUnits_iso_Q_two (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
      (Work.SSGRoute.localClosureAt k A hA))
    [FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K']
    [IsGalois (Work.SSGRoute.localFieldAt k A hA) K']
    (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
    (hRep : Nonempty (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) ≅
      Rep.res eG.toMonoidHom (SSGRoute.PTExt.modRep
        (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K'))))) :
    Nonempty (CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 2 ≃+
      CategoryTheory.Abelian.Ext
        (Rep.res eG.symm.toMonoidHom
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))))
        (SSGRoute.PTExt.modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')
          (Additive (Units ↥K'))) 2) := by
  obtain ⟨iso⟩ := hRep
  exact ext_coeff_change_n (G := ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (G' := K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') eG
    (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
    (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q))
    (SSGRoute.PTExt.modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K')))
    iso 2

end Work.SSGRoute
