import Mathlib
import Submission.Work.SSGRoute.ExtChain.exists_khLift_of_extToIdeles_eq_zero
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb_algebraMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
-- (cut, H161 2026-10-08) `import Submission.Work.SSGRoute.ArchNat.localisation_zero_imp_restriction_zero`
-- was a DEAD import (0 of that module's 5 declarations referenced below), and it was the last edge
-- putting the leaf `E1aClean.localDictionary_natural_family` inside `cone(finPlaceDictHolds)`,
-- i.e. inside the cone of the leaf's own closure.  Removed so that the leaf can be closed in place.

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

open CategoryTheory

theorem unitsToLocalUnits_eq_khIota_comp_theta
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [hNorm : Normal ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
      ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)]
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[
          ↥(Work.SSGRoute.E1aClean.decompField k Ω A)]
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : ↥K),
      ((e τ) ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ : Ω)
        = ((τ : ↥K ≃ₐ[k] ↥K) x : Ω))
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (θ : Rep.res e.toMonoidHom
          (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
            ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) ⟶
        SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q))
    (hθ : ∀ u : (↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))ˣ,
        Rep.Hom.hom θ (Additive.ofMul u) = Additive.ofMul
          (Units.map (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom u)) :
    NK.HassePrinciple.unitsToLocalUnits k ↥K (NK.GlobalCFT.Place.ofFinite q)
      = CategoryTheory.CategoryStruct.comp (Work.SSGRoute.ExtChain.khIota A q e he) θ := by
  -- Both sides are morphisms of `D_q`-representations of the same source and target; it suffices
  -- to compare their underlying linear maps on the generators `Additive.ofMul u`, `u : Kˣ`.
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have key : ∀ u : (↥K)ˣ,
      (Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k ↥K
        (NK.GlobalCFT.Place.ofFinite q))).toLinearMap (Additive.ofMul u)
      = (Rep.Hom.hom (Work.SSGRoute.ExtChain.khIota A q e he ≫ θ)).toLinearMap
          (Additive.ofMul u) := by
    intro u
    -- value of the left-hand side
    have hL := NK.HassePrinciple.unitsToLocalUnits_apply k ↥K (NK.GlobalCFT.Place.ofFinite q) u
    -- value of the right-hand side, computed along `khIota` then `θ`
    have hC := Rep.comp_apply (Work.SSGRoute.ExtChain.khIota A q e he) θ (Additive.ofMul u)
    have hK := Work.SSGRoute.ExtChain.khIota_apply A q e he (Additive.ofMul u)
    have hT := hθ (Units.map (Work.SSGRoute.ExtChain.khIncl
      (k := k) (Ω := Ω) (K := K) A).toMonoidHom u)
    -- the two coefficient maps agree: `φ ∘ incl = algebraMap`
    have hfin : NK.HassePrinciple.unitsToLocalUnitsHom (NK.GlobalCFT.Place.ofFinite q) u
        = Units.map (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom
            (Units.map (Work.SSGRoute.ExtChain.khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom u) := by
      apply Units.ext
      simp only [NK.HassePrinciple.unitsToLocalUnitsHom, Units.coe_map]
      exact (Work.SSGRoute.E1aClean.decompFieldHenselEmb_algebraMap k Ω K A hA q hAq halg
        (↑u)).symm
    have hYeqW : (Rep.Hom.hom θ).toLinearMap
          ((Rep.Hom.hom (Work.SSGRoute.ExtChain.khIota A q e he)).toLinearMap (Additive.ofMul u))
        = Additive.ofMul (Units.map
            (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom
            (Units.map (Work.SSGRoute.ExtChain.khIncl (k := k) (Ω := Ω) (K := K) A).toMonoidHom u)) :=
      (congrArg (fun y => (Rep.Hom.hom θ).toLinearMap y) hK).trans hT
    exact Eq.trans hL (Eq.trans (congrArg Additive.ofMul hfin)
      (Eq.trans hYeqW.symm hC.symm))
  exact key (Additive.toMul (α := (↥K)ˣ) x)

end Work.SSGRoute.E1aClean.LeadPhiUnr
