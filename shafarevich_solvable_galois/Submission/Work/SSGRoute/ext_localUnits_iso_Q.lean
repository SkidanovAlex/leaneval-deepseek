import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.LocalFields.completion_algebraMap_continuous
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
import Submission.Work.SSGRoute.ext_congr_right
import Submission.Work.SSGRoute.ext_res_mulEquiv
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.localAutHom_bijective

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct

set_option maxHeartbeats 800000

/- Without the v4.35 `respectTransparency` options, `AddCommGroup (DualMod p M)` is not found by
unfolding the `abbrev`; supply it explicitly (it is `LinearMap.addCommGroup`, as before). -/
local instance extLUQ_dualAddCommGroup (p : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod p) M] :
    AddCommGroup (DualMod p M) := LinearMap.addCommGroup

/-! ## Two elementary identities, proved generically (cheap) -/

example {G G' : Type} [Group G] [Group G'] (e : G ≃* G') :
    e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by
  ext x
  simp

example {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (B : Rep.{0} SSGRoute.PTExt.Coeff G') :
    Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom B) = B := by
  change Rep.res (e.toMonoidHom.comp e.symm.toMonoidHom) B = B
  rw [show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' from by ext x; simp,
    Rep.res_id]

/-- **Change of coefficient module along a group isomorphism.**  If the `G`-representation `A` is
isomorphic to the restriction along `e : G ≃* G'` of the `G'`-representation `B`, then
`Ext¹_G(X, A) ≃+ Ext¹_{G'}(res_{e⁻¹} X, B)`.  Three-step composition: `ext_congr_right`
(coefficient iso), `ext_res_mulEquiv` (group change), `ext_congr_right`
(`res_{e⁻¹} ∘ res_e ≅ id`). -/
theorem ext_coeff_change {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (B : Rep.{0} SSGRoute.PTExt.Coeff G') (hi : A ≅ Rep.res e.toMonoidHom B) :
    Nonempty (CategoryTheory.Abelian.Ext X A 1 ≃+
      CategoryTheory.Abelian.Ext (Rep.res e.symm.toMonoidHom X) B 1) := by
  obtain ⟨e1⟩ := ext_congr_right (M := X) hi 1
  obtain ⟨e2⟩ := ext_res_mulEquiv e X (Rep.res e.toMonoidHom B)
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by
    ext x
    simp
  have hres : Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom B) = B := by
    change Rep.res (e.toMonoidHom.comp e.symm.toMonoidHom) B = B
    rw [hcomp, Rep.res_id]
  obtain ⟨e3⟩ := ext_congr_right (M := Rep.res e.symm.toMonoidHom X) (eqToIso hres) 1
  exact ⟨e1.trans (e2.symm.trans e3)⟩

theorem ext_localUnits_iso_Q (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
    (eG : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
    (hRep : Nonempty (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) ≅
      Rep.res eG.toMonoidHom (SSGRoute.PTExt.modRep
        (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K'))))) :
    Nonempty (Abelian.Ext
        (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
          (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))))
        (localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 1 ≃+
      Abelian.Ext
        (Rep.res eG.symm.toMonoidHom
          (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
            (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T)))))
        (modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')
          (Additive (Units ↥K'))) 1) := by
  obtain ⟨iso⟩ := hRep
  -- elaborated without the expected type (its propagation re-unified the `Ext` group instances)
  have h := ext_coeff_change (G := ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (G' := K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') eG
    (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
      (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))))
    (localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q))
    (modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K')))
    iso
  exact h

end Work.SSGRoute
