import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.ZDataMup.OddForm.oTheta_eq_one_of_ne_oddPrime
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.H9.swTwoPlacePairingTwo
import Submission.Work.SSGRoute.H9.oPairAt_swapTwo
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The crossed two-place value identity at `p = 2`, proved

Same statement as `Work.SSGRoute.ZDataTwo.crossedValueTwo` (item 2 of
`ZDataTwo/NOTE_p2_antisymmetry_identity.md` §8), proved by the four-step composition of
`ZDataTwo/ACTION_crossedValueTwo_composition.md` §0bis.
-/

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

/-- **The crossed two-place value identity at `p = 2`** (item 2 of the `p = 2` §4 verification). -/
theorem crossedValueTwoProof {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (bs bt : (↥K)ˣ) (Zi ZN : ValuationSubring Ω)
    (hZi : SSGRoute.IsFinPlace k Zi) (hZN : SSGRoute.IsFinPlace k ZN)
    (hZiN : ¬ Work.SSGRoute.gesKConj K Zi ZN)
    [FiniteDimensional ↥K (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs)]
    [IsGalois ↥K (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs)]
    [FiniteDimensional ↥K (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt)]
    [IsGalois ↥K (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt)]
    (ψZ ψN : Ω ≃ₐ[k] Ω)
    (hψZ : ψZ ∈ SSGRoute.decomp k Zi ⊓ K.fixingSubgroup)
    (hψN : ψN ∈ SSGRoute.decomp k ZN ⊓ K.fixingSubgroup)
    (hpinZ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψZ, (Subgroup.mem_inf.mp hψZ).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bt))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Zi hZi))
    (hpinN : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψN, (Subgroup.mem_inf.mp hψN).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ZN hZN))
    (hunrN : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) bs))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ZN hZN))
    (hconfZ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Zi B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs u = 0)
    (hconfN : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K ZN B) →
      ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt u = 0)
    (hkillZ : ∀ u : Ω ≃ₐ[k] Ω, u ∈ K.fixingSubgroup → SSGRoute.IsInertia k Zi u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt u = 0)
    (hinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs c = 0)
    (hcountZ : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Zi hZi)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bs : ↥K))))
    (hcountN : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ZN hZN)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (bt : ↥K)))) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bs ψN
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bt ψZ = 0 := by
  -- (1) the `p = 2` two-place product formula at `(bs, bt)` over `(Zi, ZN)`
  have hsum := Work.SSGRoute.H9.swTwoPlacePairingTwo (K := K) ζ hζ hζK bs bt Zi ZN
    hZi hZN hZiN hconfZ hconfN hinf
  -- (2) the dictionary at `ZN` (first-argument form; odd count on the second argument)
  have hN := Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count (K := K) ζ hζ hζK bs bt ZN hZN
    ψN (Subgroup.mem_inf.mp hψN).2 hunrN hpinN hcountN
  -- (3) the dictionary at `Zi` (the swapped form; odd count on the first argument)
  have hZ := Work.SSGRoute.H9.oPairAt_swapTwo (K := K) ζ hζ hζK bs bt Zi hZi
    ψZ (Subgroup.mem_inf.mp hψZ).2 hkillZ hpinZ hcountZ
  -- (4) add and close
  rw [hZ, hN] at hsum
  rw [add_comm] at hsum
  exact hsum

end Work.SSGRoute.ZDataTwo
