import Mathlib
import Submission.Work.SSGRoute.HRec.cupKummer_helpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HRec

theorem locUnits_mkClass_eq_zero_of_inflCoboundary (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : FiniteGaloisIntermediateField k Ω)
    (z : (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) ×
        (↥(L : IntermediateField k Ω) ≃ₐ[k] ↥(L : IntermediateField k Ω)) →
        Additive (↥(L : IntermediateField k Ω))ˣ)
    (hz : z ∈ groupCohomology.cocycles₂
        (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → Additive (↥(L : IntermediateField k Ω))ˣ)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hcob : ∀ g ∈ SSGRoute.decomp k A, ∀ h ∈ SSGRoute.decomp k A,
      z (SSGRoute.res k (L : IntermediateField k Ω) g, SSGRoute.res k (L : IntermediateField k Ω) h)
        = SSGRoute.res k (L : IntermediateField k Ω) g • b h - b (g * h) + b g) :
    ∀ w : NK.GlobalCFT.Place ↥(L : IntermediateField k Ω),
      NK.GlobalCFT.Place.LiesOver w
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hA)) →
      (NK.HassePrinciple.locUnits k ↥(L : IntermediateField k Ω) w).hom
        (Work.SSGRoute.sha2_hasse.mkClass
          (NK.HassePrinciple.unitsRep k ↥(L : IntermediateField k Ω)) z hz) = 0 := by sorry

end Work.SSGRoute.HRec
