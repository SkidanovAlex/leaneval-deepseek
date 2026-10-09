import Mathlib
import Submission.Work.SSGRoute.E1aClean.phiUnrU1
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb_algebraMap
import Submission.Work.SSGRoute.E1aClean.finPlaceSquare
import Submission.Work.SSGRoute.E1aClean.transferNatCoeff
import Submission.Work.SSGRoute.E1aClean.e1cMap_hensel_cocycle_formula
import Submission.Work.SSGRoute.E1aClean.levelTwoDatum
import Submission.Work.SSGRoute.ValuationSES.C1
import Submission.Work.SSGRoute.E1aClean.h1locToClassRes
import Submission.Work.SSGRoute.E1aClean.levelChange_lift_transport
import Submission.Work.SSGRoute.PT.E1aFinBox.levelChangeTransfer_e1cMap_eq_hensel
import Submission.Work.SSGRoute.ExtChain.exists_khLift_of_extToIdeles_eq_zero
import Submission.Work.SSGRoute.PT.E1aFinBox.freeCoverCompat_comp_hom
import Submission.Work.SSGRoute.PT.PhiEgen_compat
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.phiCan_square_scaffold
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

theorem phiCan_square
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
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
    (hφres : ∀ g : Ω ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Ω,
      Work.SSGRoute.E1aClean.levelTwoGroupHom k Ω K A hA q hAq e
          (SSGRoute.res ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
            (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
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
          (Units.map (Work.SSGRoute.E1aClean.decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom u))
    (hpush : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Bijective ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (add_zero 1)))
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hl : SSGRoute.IsLocConstOn ⊤ b) :
    SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
      = Work.SSGRoute.E1aClean.phiCan p k Ω K ζ hζ hζK T hT A hA q hAq e hφres θ hpush E
          (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b) :=
  phiCan_square_main p k Ω K ζ hζ hζK T hT A hA q hAq e hφres halg θ hθ hpush E b hb hl

end Work.SSGRoute.E1aClean.LeadPhiUnr
