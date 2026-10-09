import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_dictionary
import Submission.Work.SSGRoute.ZDataTwo.Mu2FiniteForm
import Submission.Work.SSGRoute.NodeS37.p16Shim
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSGRoute.P2Close.unitSquare
import Submission.Work.SSGRoute.NodeS37.isSquare_of_fixed_of_involution
import Submission.Work.SSGRoute.P2Close.isSquare_of_mul_aut_eq_one
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.Work.SSGRoute.ges_readoff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PinnedTwin

open scoped Pointwise NumberField

/-- **A finite field with a nontrivial involution of odd characteristic: fixed elements and
norm-one elements are squares.**  This is the finite-field input `hFF` consumed by
`Work.SSGRoute.P2Close.unitSquare`; it is assembled from
`Work.SSGRoute.NodeS37.isSquare_of_fixed_of_involution` (fixed elements are squares, in every
characteristic) and `Work.SSGRoute.P2Close.isSquare_of_mul_aut_eq_one` (norm-one elements are
squares, granted the fixed-element statement). -/
private lemma involutionIsSquare_of_fintype {E : Type*} [Field E] [Fintype E] (σ : E ≃+* E)
    (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (hchar : ringChar E ≠ 2) :
    (∀ y : E, σ y = y → IsSquare y) ∧ (∀ y : E, y * σ y = 1 → IsSquare y) := by
  haveI : Finite E := Fintype.finite (inferInstance : Fintype E)
  have hinv : Function.Involutive σ := fun z => by
    have h := congrArg (fun f : E ≃+* E => f z) hσ2
    simpa [pow_two] using h
  have hfix : ∀ y : E, σ y = y → IsSquare y :=
    fun y hy => Work.SSGRoute.NodeS37.isSquare_of_fixed_of_involution σ hinv hσ1 hy
  exact ⟨hfix, fun y hy => Work.SSGRoute.P2Close.isSquare_of_mul_aut_eq_one σ hσ2 hfix y hy⟩

/-- The action of `ρ` on `𝓞 ↥K` is the restriction of the automorphism `ρ` of `↥K`. -/
private lemma galRestrict_apply_eq_smul {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [NumberField ↥K] (ρ : K ≃ₐ[k] K)
    (y : NumberField.RingOfIntegers ↥K) :
    galRestrict (NumberField.RingOfIntegers k) k ↥K (NumberField.RingOfIntegers ↥K) ρ y =
      ρ • y := by
  apply NumberField.RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply, algebraMap.smul', AlgEquiv.smul_def]

/-- The `𝔭`-adic valuation of the image of `ρ • y - y` in `↥K`. -/
private lemma algebraMap_smul_sub_smul {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [NumberField ↥K] (ρ : K ≃ₐ[k] K)
    (y : NumberField.RingOfIntegers ↥K) :
    algebraMap (NumberField.RingOfIntegers ↥K) ↥K (ρ • y - y) =
      ρ (y : ↥K) - (y : ↥K) := by
  rw [map_sub, algebraMap.smul', AlgEquiv.smul_def]

theorem oPairAtInvariantUnitAnti {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
    (a X : (↥K)ˣ)
    (ha : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a = a)
    (hX : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) X = -X)
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hB2 : ¬ B.valuation (2 : Ω) < 1)
    (hfixB : Work.SSGRoute.ZDataMup.galLift K ρ • B = B)
    (hunr : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.res k K σ = ρ → ¬ SSGRoute.IsInertia k B σ)
    (hvala : B.valuation (algebraMap ↥K Ω (a : ↥K)) = 1) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
      B hB (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) = 0 := by
  classical
  -- ## The prime `𝔭` of `𝓞 ↥K` below the place `B`
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    Work.SSGRoute.levelPrime k Ω B hB K
  have h𝔭 : B.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
    NK.Reconstruct.primeOfLevel_spec B K (NK.Reconstruct.comap_level_ne_top hB K)
  -- ## `ρ` acts nontrivially on the residue field `𝓞 ↥K ⧸ 𝔭`
  --
  -- If it acted trivially, then `ρ` would lie in the inertia subgroup of `Gal(↥K/k)` at `𝔭`,
  -- which by `inertiaSub_image_eq_levelInertia` is the image of the place inertia `I_B`; some
  -- lift of `ρ` would then be an inertia element, contradicting `hunr`.
  have hnontriv : ∃ x₀ : NumberField.RingOfIntegers ↥K,
      ¬ (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭
        (ρ (x₀ : ↥K) - (x₀ : ↥K)) < 1) := by
    by_contra hcon
    push Not at hcon
    have hρmem : ρ ∈ Work.SSGRoute.levelInertiaOf k Ω B hB K := by
      intro x
      change ρ • x - x ∈ 𝔭.asIdeal
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) 𝔭 (ρ • x - x)]
      simpa only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_sub, algebraMap.smul',
        AlgEquiv.smul_def] using hcon x
    have hIn : ρ ∈ (Work.SSGRoute.inertiaSub k Ω B).map (AlgEquiv.restrictNormalHom K) := by
      rw [Work.SSGRoute.inertiaSub_image_eq_levelInertia k Ω B hB K]
      exact hρmem
    obtain ⟨u, hu, huρ⟩ := Subgroup.mem_map.mp hIn
    exact hunr u huρ hu
  -- ## The finite-field input
  have hFF : ∀ (E : Type) [Field E] [Fintype E] (σ : E ≃+* E), σ ^ 2 = 1 → σ ≠ 1 →
      ringChar E ≠ 2 → (∀ y : E, σ y = y → IsSquare y) ∧ (∀ y : E, y * σ y = 1 → IsSquare y) :=
    fun E _ _ σ hσ2 hσ1 hchar => involutionIsSquare_of_fintype σ hσ2 hσ1 hchar
  -- ## `a` is a square in the completion `K_𝔭`
  have hsq : ∃ c : (𝔭.adicCompletion ↥K)ˣ,
      Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom a = c ^ 2 :=
    Work.SSGRoute.P2Close.unitSquare (K := K) ρ hρ2 B hB 𝔭 h𝔭 hB2 hfixB hnontriv hFF a hvala
      (Or.inl ha)
  -- ## Hence the local `2`-power class of `a` at `𝔭` is trivial
  have he : (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom a)⁻¹ ∈
      NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion ↥K) 2 := by
    obtain ⟨c, hc⟩ := hsq
    refine ⟨c⁻¹, ?_⟩
    rw [powMonoidHom_apply, pow_two]
    rw [show c⁻¹ * c⁻¹ = (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom a)⁻¹
      from by rw [← mul_inv_rev, ← pow_two, ← hc]]
  have hloc : NK.UchidaKummer.localPowClass ↥K 2 𝔭 a = 1 :=
    Work.SSGRoute.localPowClass_eq_one_of_unit_component (K := ↥K) (p := 2) Nat.prime_two
      (𝔭 := 𝔭) (γ := a)
      (e := (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom a)⁻¹) he
      (by rw [inv_inv])
  -- ## The Kummer cochain of `a` kills the whole local group, so the pairing vanishes
  have hkill : ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a u = 0 :=
    fun u hu => (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_eq_zero_iff_localPowClass
      K ζ hζK hζ a B hB 𝔭 h𝔭).mpr hloc u hu
  exact Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup
    (ζ := ζ) (hζ := hζ) (hζK := hζK) a X B hB hkill

end Work.SSGRoute.PinnedTwin
