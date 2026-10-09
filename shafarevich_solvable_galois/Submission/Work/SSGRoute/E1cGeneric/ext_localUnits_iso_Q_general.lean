import Mathlib
import Submission.Work.SSGRoute.ext_localUnits_iso_Q
import Submission.Work.SSGRoute.PT.e1aBetaCan_localAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1cGeneric

open SSGRoute.PTExt CategoryTheory

theorem ext_localUnits_iso_Q_general (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA) (Work.SSGRoute.localClosureAt k A hA))
    [FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K']
    [IsGalois (Work.SSGRoute.localFieldAt k A hA) K']
    (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
    (hRep : Nonempty (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) ≅
      Rep.res eG.toMonoidHom (SSGRoute.PTExt.modRep
        (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K'))))) :
    Nonempty (CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
        (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 1 ≃+
      CategoryTheory.Abelian.Ext
        (Rep.res eG.symm.toMonoidHom
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X))
        (SSGRoute.PTExt.modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K')
          (Additive (Units ↥K'))) 1) := by
  obtain ⟨iso⟩ := hRep
  exact Work.SSGRoute.ext_coeff_change
    (G := ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (G' := K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') eG
    (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X)
    (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q))
    (SSGRoute.PTExt.modRep (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K')))
    iso

end Work.SSGRoute.E1cGeneric
