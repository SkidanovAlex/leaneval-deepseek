import Mathlib
import Submission.Work.SSGRoute.NodeS34.swKLevel_localValue_eq_zero
import Submission.Work.SSGRoute.NodeS34.swKLevel_kills_levelKernel
import Submission.Work.SSGRoute.NodeS34.swKLevel_localGroup_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The §4(b) promotion, packaged for the chain

`NodeS34.swKLevel_localValue_eq_zero` promotes the value of `z` at a Frobenius of the local group to
the whole local group at a level over `K`.  This file specialises it to the two classes of the chain,
`z = χ_{b_i} + χ_{b_N}`, and discharges the level-kernel hypothesis with
`NodeS34.swKLevel_sum_kills_levelKernel`:

* `swKLevel_sum_vanish_of_hpow` — from (i) the value identity `χ_{b_i} σ + χ_{b_N} σ = 0` at a an
  element `σ` of the local group, (ii) the cyclicity input (`every element of the local group
  restricts to a power of `res_L σ``, supplied in the assembly by
  `NodeS34.swKLevel_localGroup_pow`) and (iii) `L ⊇ K((b_i b_N)^{1/p})`, the sum vanishes on the
  whole local group `decomp k A ⊓ K.fixingSubgroup`.

This is exactly Schmidt--Wingberg's final step of §4(b) ("`z_i` and `z_N` are unramified at
`σP_N`, so it suffices to check the Frobenius") at the level `K((b_i b_N)^{1/p})`.
-/

namespace Work.SSGRoute.NodeS34

open _root_.SSGRoute

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
  [IsGalois k K]

/-- **The promotion for the sum `χ_{b_i} + χ_{b_N}`** (with the cyclicity input as a hypothesis).
If the sum of the two Kummer cochains vanishes at `σ ∈ decomp k A ⊓ K.fixingSubgroup`, if every
element of the local group restricts into `⟨res_L σ⟩` at a level `L ⊇ K((b_i b_N)^{1/p})`, then the
sum vanishes on the whole local group at `A`. -/
theorem swKLevel_sum_vanish_of_hpow
    (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (bi bN : (↥K)ˣ)
    (hroot : (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p (bi * bN) : Ω) ∈ L)
    (A : ValuationSubring Ω)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (hpow : ∀ (τ : Ω ≃ₐ[k] Ω) (hτ : τ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup), ∃ m : ℤ,
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L
          ((IntermediateField.fixingSubgroupEquiv K) ⟨τ, (Subgroup.mem_inf.mp hτ).2⟩) =
        (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, (Subgroup.mem_inf.mp hσ).2⟩)) ^ m)
    (hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi σ
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN σ = 0) :
    ∀ (τ : Ω ≃ₐ[k] Ω) (hτ : τ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi τ
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN τ = 0 := by
  refine swKLevel_localValue_eq_zero (K := K) L A
    (fun τ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi τ
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN τ) ?_ σ hσ hpow ?_ hval
  · intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ bi g hg h hh,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ bN g hg h hh]
    abel
  · intro u hu huL _
    exact swKLevel_sum_kills_levelKernel (K := K) L ζ hζ hζK bi bN hroot u hu huL

/-- **The same with the cyclicity input produced from `IsFrobAtPrime`** (via
`NodeS34.swKLevel_localGroup_pow`): the hypotheses `hunr` and `hfrob` are exactly those of the
latter, so in the assembly the promotion is a single call. -/
theorem swKLevel_sum_vanish
    (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (bi bN : (↥K)ˣ)
    (hroot : (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p (bi * bN) : Ω) ∈ L)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔮 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮)
    (hunr : ∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔮.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) = 1)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥L) 𝔮
      (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, (Subgroup.mem_inf.mp hσ).2⟩)))
    (hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi σ
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN σ = 0) :
    ∀ (τ : Ω ≃ₐ[k] Ω) (hτ : τ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi τ
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN τ = 0 :=
  swKLevel_sum_vanish_of_hpow (K := K) L ζ hζ hζK bi bN hroot A σ hσ
    (swKLevel_localGroup_pow (K := K) L A hA 𝔮 h𝔮 hunr σ hσ hfrob) hval

end Work.SSGRoute.NodeS34
