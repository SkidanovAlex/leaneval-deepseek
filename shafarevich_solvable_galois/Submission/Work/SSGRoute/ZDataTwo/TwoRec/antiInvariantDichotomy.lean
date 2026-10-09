import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_dictionary
import Submission.Work.SSGRoute.ZConstruction.HilbertSymbolTransitivity
import Submission.Work.SSGRoute.ZConstruction.LocalSquares
import Submission.Work.SSGRoute.ZConstruction.OThetaLocalNorm
import Submission.Work.SSGRoute.NodeS37.oPairAt_smul_conj
import Submission.Work.SSGRoute.H9.oPairAt_swapTwo
import Submission.Work.SSGRoute.H9.swChainConjDefs
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup_right
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.PlaceValBridge
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.killsLocalGroup_of_one_unit
import Submission.Work.SSGRoute.ZDataTwo.isLocalNorm_of_kills_inertia
import Submission.Work.SSGRoute.ZDataTwo.RealPlaceInvolution
import Submission.Work.HilbertSymbolGeneral.hilbertReciprocityTwo
import Submission.Work.SSGRoute.EscapeCoreLib.correctionFromPrime
import Submission.Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo.TwoRec

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- **The chosen lift of `ρ` acts on `↥K` through `ρ`.**  Consequently the conjugate unit
`conjUnit (galLift K ρ) b` is the image `ρ b` of `b` under `ρ`. -/
private lemma conjUnit_galLift_coe (ρ : K ≃ₐ[k] K) (b : (↥K)ˣ) :
    ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b : (↥K)ˣ) : ↥K)
      = ρ (b : ↥K) := by
  rw [Work.SSGRoute.H9.conjUnit, Units.coe_map, Work.SSGRoute.ZDataMup.galLift_spec]
  rfl

/-- **The pairing of two Kummer cochains at a place is the pairing computed with global
representatives.**  This is the `p = 2` form of `oPair_toClass_eq_oPairGlob`, with the cocycle,
local-constancy and character hypotheses supplied by the Kummer cochain. -/
private theorem oPairAt_eq_oPairGlob_two (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
          (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
          hA α β := by
  rw [Work.SSGRoute.ZDataMup.OddForm.oPairAt]
  refine Work.SSGRoute.ZDataMup.OddForm.oPair_toClass_eq_oPairGlob (K := K) (p := 2) (k := k)
    (Ω := Ω) (ζ := (⟨ζ, hζK⟩ : ↥K))
    (hζ := Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (hA := hA)
    _ _ α β ?_ ?_ ?_ ?_ ?_ ?_
  · intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ α g hg h hh]
    have hg1 : SSGRoute.res k K g = 1 := by
      rw [← MonoidHom.mem_ker]
      rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
        IntermediateField.restrictNormalHom_ker K]
      exact hg
    rw [hg1, one_smul]
  · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ α
  · intro g hg h hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ β g hg h hh]
    have hg1 : SSGRoute.res k K g = 1 := by
      rw [← MonoidHom.mem_ker]
      rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
        IntermediateField.restrictNormalHom_ker K]
      exact hg
    rw [hg1, one_smul]
  · exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ β
  · intro σ hσ
    exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := α) hσ
  · intro σ hσ
    exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := β) hσ

/-- **The `𝔮`-adic valuation is equivariant for the Galois transport of places.**  If `ρ` is a
`k`-automorphism of the number field `K` and `𝔮` a height-one prime of `𝓞 K`, then the `ρ`-image
`placeSmul ρ 𝔮` of `𝔮` satisfies `v_{ρ𝔮}(ρ x) = v_𝔮(x)` for every `x ∈ K`. -/
private theorem valuation_placeSmul (ρ : K ≃ₐ[k] K)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) (x : ↥K) :
    (IsDedekindDomain.HeightOneSpectrum.valuation ↥K
      (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) (ρ x)) =
      (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔮) x :=
  Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
    (R := NumberField.RingOfIntegers ↥K) (K := ↥K)
    (galRestrict (NumberField.RingOfIntegers k) k (↥K) (NumberField.RingOfIntegers ↥K) ρ :
      NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K)
    ρ.toRingEquiv
    (fun r => (algebraMap_galRestrict_apply (NumberField.RingOfIntegers k) ρ r).symm)
    𝔮 (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
    (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal ρ 𝔮) x

/-- **The conjugate class is a unit at the prime below `A` exactly when it is a unit at the conjugate
prime.**  The `𝔭`-count of `ρ b` is the `ρ𝔭`-count of `b`, where `ρ𝔭 = placeSmul ρ 𝔭`. -/
private theorem count_spanSingleton_conjUnit_eq (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (b : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    FractionalIdeal.count ↥K (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b : (↥K)ˣ) : ↥K))
      = FractionalIdeal.count ↥K
          (Commons.NumberTheory.NumberField.Completion.placeSmul ρ
            (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA))
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (b : ↥K)) := by
  have hρmul : ρ * ρ = 1 := by rw [← pow_two]; exact hρ2
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρmul
  have hconj : (((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b :
      (↥K)ˣ) : ↥K)) = ρ (b : ↥K) := by
    rw [Work.SSGRoute.H9.conjUnit, Units.coe_map, Work.SSGRoute.ZDataMup.galLift_spec]
    rfl
  rw [hconj]
  rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := ↥K) _
        ((map_ne_zero ρ).mpr (Units.ne_zero b)),
      Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := ↥K) _ (Units.ne_zero b)]
  have hv := valuation_placeSmul (K := K) (k := k) (Ω := Ω) ρ⁻¹
    (Commons.NumberTheory.NumberField.Completion.placeSmul ρ
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)) (b : ↥K)
  rw [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, inv_mul_cancel,
    Commons.NumberTheory.NumberField.Completion.placeSmul_one] at hv
  rw [show ρ⁻¹ (b : ↥K) = ρ (b : ↥K) from by rw [hρinv]] at hv
  rw [hv]

/-- **Two units at a place where `2` is a unit pair trivially.**  Both Kummer levels are unramified
at a non-dyadic prime, so both classes are unit classes, and units pair trivially. -/
private theorem oPairGlob_units_eq_zero (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (a u : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (ha : A.valuation (algebraMap ↥K Ω (a : ↥K)) = 1)
    (hu : A.valuation (algebraMap ↥K Ω (u : ↥K)) = 1) :
    Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        hA a u = 0 := by
  classical
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  haveI : IsAlgClosure ↥K Ω := ⟨inferInstance, inferInstance⟩
  by_cases hsq : a ∈ NK.LocalAnabelian.powSubgroup 2 ↥K
  · exact Work.SSGRoute.H9.oPairGlob_eq_zero_of_mem_powSubgroup_fst (K := K) (k := k) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) hζ' a u A hA hsq
  · haveI hfdL : FiniteDimensional ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
        (⟨ζ, hζK⟩ : ↥K) hζ' a
    haveI hgalL : IsGalois ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
        (⟨ζ, hζK⟩ : ↥K) hζ' a
    haveI hnfL : NumberField
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
        (⟨ζ, hζK⟩ : ↥K) hζ' a
    obtain ⟨hc, hy⟩ := Work.SSGRoute.H9.hLevel_quadratic_data (K := K) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) hζ' a hsq
    -- the Kummer character of the unit `a` kills the inertia of `A` over `↥K`
    have ha_inertia : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K A σ →
        Work.SSGRoute.kummerChar (K := ↥K) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' a σ = 0 := by
      intro σ hσ
      rw [← Work.SSGRoute.ZDataTwo.kummerCharZMod_two_eq_kummerChar (k := k) (Ω := Ω) K
        (⟨ζ, hζK⟩ : ↥K) hζ' a σ]
      exact Work.SSGRoute.kummerCharZMod_eq_zero_of_isInertia_of_unit k Ω K 2
        (⟨ζ, hζK⟩ : ↥K) hζ' A h2 a ha σ hσ
    -- `u` is a unit at the prime of `↥K` below `A`
    have hprime_unit :
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).valuation ↥K (u : ↥K) = 1 := by
      have h1 : (A.comap (algebraMap ↥K Ω)).valuation (u : ↥K) = 1 :=
        (Work.SSGRoute.GrunwaldEscapeCore.comap_valuation_eq_one_iff A u).mp hu
      rw [Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hA] at h1
      exact (Work.SSGRoute.EscapeCoreLib.valuationSubringAtPrime_valuation_eq_one_iff
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) (u : ↥K)).mp h1
    -- the value of the completion image of `u` is a square in the value group (it is `1`)
    have hsqval : ∃ y : ((Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion
          ↥K)ˣ,
        Valued.v (R := (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion ↥K)
            (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap ↥K
              ((Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion ↥K) (u : ↥K))
          = (Valued.v (R := (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion
                ↥K) (Γ₀ := WithZero (Multiplicative ℤ)) (y : _)) ^ 2 := by
      refine ⟨1, ?_⟩
      rw [show Valued.v (R := (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion
              ↥K) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap ↥K
              ((Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion ↥K) (u : ↥K))
          = (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).valuation ↥K (u : ↥K) from
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ (u : ↥K),
        hprime_unit]
      simp
    have hisnorm : NK.NUV2.LC.IsLocalNorm ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) u
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)) :=
      Work.SSGRoute.ZDataTwo.isLocalNorm_of_kills_inertia_of_sq_val (k := ↥K) (Ω := Ω)
        A (Work.SSGRoute.ZDataMup.OddForm.oddFinPlace (K := K) hA)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hA)
        (⟨ζ, hζK⟩ : ↥K) hζ' a u
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)
        hc hy ha_inertia hsqval
    refine (Work.SSGRoute.H9.oPairGlob_eq_zero_iff_mem_localNormSubgroup (K := K) (k := k)
      (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' a u A hA hsq).mpr ?_
    exact (Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup (K := ↥K)
      (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)) u
      (NK.GlobalCFT.Place.ofFinite
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA))).mp hisnorm

theorem antiInvariantDichotomy {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
    (z X : (↥K)ˣ)
    (hX : (X : ↥K) = (z : ↥K) - (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z : ↥K))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hA2 : ¬ A.valuation (2 : Ω) < 1)
    (hXA : FractionalIdeal.count ↥K (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (X : ↥K)) ≠ 0)
    (hPz : FractionalIdeal.count ↥K (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (z : ↥K)) = 0)
    (hPz' : FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA))
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (z : ↥K)) = 0) :
    ((Work.SSGRoute.gesKConj K A (Work.SSGRoute.ZDataMup.galLift K ρ • A) ∧
        (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
            (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z) σ = 0)) →
      Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) ⟨ζ, hζK⟩
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z)) = 0) ∧
    (¬ Work.SSGRoute.gesKConj K A (Work.SSGRoute.ZDataMup.galLift K ρ • A) →
      Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) ⟨ζ, hζK⟩
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z))
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω) ⟨ζ, hζK⟩
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • A)
        ((Work.SSGRoute.isFinPlace_smul_iff A (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hA)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z))) := by
  refine ⟨?_, ?_⟩
  · -- ## Clause 1: the second argument kills the local group
    rintro ⟨_hconj, hkill⟩
    exact oPairAt_eq_zero_of_killsLocalGroup_right (K := K) (k := k) (Ω := Ω) ζ hζ hζK X
      (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z) A hA hkill
  · -- ## Clause 2: the two conjugate places give the same pairing
    intro _hsplit
    let ζK : ↥K := ⟨ζ, hζK⟩
    have hζ' : IsPrimitiveRoot ζK 2 :=
      Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
    let b : (↥K)ˣ := Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z
    let w : (↥K)ˣ := z * b⁻¹
    let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
      Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA
    have h𝔭 : A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
      Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hA
    have hA' : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K ρ • A) :=
      (SSGRoute.isFinPlace_smul_iff A (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hA
    have hρmul : ρ * ρ = 1 := by rw [← pow_two]; exact hρ2
    -- ## bookkeeping: `ρ X = -X`, so `conjUnit (galLift K ρ) (-X) = X`
    have hbcoe : (b : ↥K) = ρ (z : ↥K) := conjUnit_galLift_coe ρ z
    have hXelem : (X : ↥K) = (z : ↥K) - (b : ↥K) := by rw [hX, hbcoe]
    have hρb : ρ (b : ↥K) = (z : ↥K) := by
      rw [hbcoe, ← AlgEquiv.mul_apply, hρmul]
      simp
    have hρX : ρ (X : ↥K) = -((X : ↥K)) := by
      have h1 : ρ (X : ↥K) = ρ (z : ↥K) - (z : ↥K) := by
        rw [hXelem, map_sub, hρb]
      rw [h1, hXelem, hbcoe]
      ring
    have hconjX : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) (-X) = X := by
      refine Units.ext ?_
      rw [conjUnit_galLift_coe, Units.val_neg, map_neg, hρX, neg_neg]
    -- ## unit conditions at `A`
    have hunit_z : A.valuation (algebraMap ↥K Ω (z : ↥K)) = 1 :=
      (Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero A 𝔭 h𝔭 z).mpr hPz
    have hcount_b : FractionalIdeal.count ↥K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (b : ↥K)) = 0 := by
      have hb' : (b : ↥K) = (Work.SSGRoute.H9.conjUnit
          (Work.SSGRoute.ZDataMup.galLift K ρ) z : ↥K) := rfl
      have hbridge := count_spanSingleton_conjUnit_eq (K := K) ρ hρ2 z A hA
      rw [hb', hbridge]
      exact hPz'
    have hunit_b : A.valuation (algebraMap ↥K Ω (b : ↥K)) = 1 :=
      (Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero A 𝔭 h𝔭 b).mpr hcount_b
    have hwc : (w : ↥K) = (z : ↥K) * (b : ↥K)⁻¹ := by
      show ((z * b⁻¹ : (↥K)ˣ) : ↥K) = (z : ↥K) * (b : ↥K)⁻¹
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
    have hunit_w : A.valuation (algebraMap ↥K Ω (w : ↥K)) = 1 := by
      rw [hwc, map_mul, map_inv₀, Valuation.map_mul, Valuation.map_inv, hunit_z, hunit_b, inv_one,
        mul_one]
    -- ## the anti-invariant element `X` is divisible by `𝔭`
    have hXval : A.valuation (algebraMap ↥K Ω (X : ↥K)) < 1 := by
      have hzmem : algebraMap ↥K Ω (z : ↥K) ∈ A :=
        (ValuationSubring.valuation_le_one_iff A _).mp (le_of_eq hunit_z)
      have hbmem : algebraMap ↥K Ω (b : ↥K) ∈ A :=
        (ValuationSubring.valuation_le_one_iff A _).mp (le_of_eq hunit_b)
      have hsub : algebraMap ↥K Ω (X : ↥K) =
          algebraMap ↥K Ω (z : ↥K) - algebraMap ↥K Ω (b : ↥K) := by
        rw [hXelem, map_sub]
      have hle : A.valuation (algebraMap ↥K Ω (X : ↥K)) ≤ 1 := by
        rw [hsub]
        exact (ValuationSubring.valuation_le_one_iff A _).mpr (A.sub_mem hzmem hbmem)
      have hne : A.valuation (algebraMap ↥K Ω (X : ↥K)) ≠ 1 := fun h1 =>
        hXA ((Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero A 𝔭 h𝔭
          X).mp h1)
      exact lt_of_le_of_ne hle hne
    have ht_w : A.valuation (algebraMap ↥K Ω ((w : ↥K) - 1)) < 1 := by
      have h2 : ((z : ↥K) - (b : ↥K)) * (b : ↥K)⁻¹
          = (z : ↥K) * (b : ↥K)⁻¹ - 1 := by
        rw [sub_mul, mul_inv_cancel₀ (Units.ne_zero b)]
      have h1 : (w : ↥K) - 1 = (X : ↥K) * (b : ↥K)⁻¹ := by
        rw [hwc, hXelem, h2]
      rw [h1, map_mul, map_inv₀, Valuation.map_mul, Valuation.map_inv, hunit_b, inv_one, mul_one]
      exact hXval
    -- ## `w` is a `1`-unit, so its Kummer class is locally trivial
    have hw_kill : ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ w u = 0 :=
      killsLocalGroup_of_one_unit (K := K) (k := k) (Ω := Ω) ζ hζ hζK w A hA hA2 hunit_w ht_w
    have hw_lpc : NK.UchidaKummer.localPowClass ↥K 2 𝔭 w = 1 :=
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_eq_zero_iff_localPowClass K ζ hζK hζ w A hA 𝔭
        h𝔭).mp hw_kill
    -- ## `z` and `b` have the same local class at `𝔭`
    have hlc : NK.UchidaKummer.localPowClass ↥K 2 𝔭 z
        = NK.UchidaKummer.localPowClass ↥K 2 𝔭 b := by
      have h2 : NK.UchidaKummer.localPowClass ↥K 2 𝔭 z
          * (NK.UchidaKummer.localPowClass ↥K 2 𝔭 b)⁻¹ = 1 := by
        rw [← map_inv, ← map_mul]
        exact hw_lpc
      exact mul_inv_eq_one.mp h2
    -- ## the chain
    haveI hlevel1_fd : FiniteDimensional ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (-X)) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
        ζK hζ' (-X)
    haveI hlevel1_gal : IsGalois ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (-X)) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2) ζK hζ' (-X)
    haveI hlevel1_nf : NumberField
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (-X)) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
        ζK hζ' (-X)
    haveI hlevel2_fd : FiniteDimensional ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2)
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) (-X))) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
        ζK hζ' (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) (-X))
    haveI hlevel2_gal : IsGalois ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2)
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) (-X))) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2) ζK hζ'
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) (-X))
    haveI hlevel2_nf : NumberField
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2)
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) (-X))) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2) ζK hζ'
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) (-X))
    have cov := Work.SSGRoute.NodeS37.oPairAt_smul_conj (K := K) (k := k) (Ω := Ω) ζ hζ hζK
      (-X) z ρ A hA hA'
    rw [hconjX] at cov
    have glob1 := oPairAt_eq_oPairGlob_two (K := K) (k := k) (Ω := Ω) ζ hζ hζK (-X) z A hA
    have glob2 := oPairAt_eq_oPairGlob_two (K := K) (k := k) (Ω := Ω) ζ hζ hζK X b A hA
    have hadd : Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        ζK hζ' hA (-X) z
        = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
            ζK hζ' hA (-1) z
          + Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
              ζK hζ' hA X z := by
      have h1 : (-X : (↥K)ˣ) = (-1 : (↥K)ˣ) * X := by ext; simp
      rw [h1, Work.SSGRoute.ZDataMup.OddForm.oPairGlob_add]
    have hneg1 : A.valuation (algebraMap ↥K Ω ((-1 : (↥K)ˣ) : ↥K)) = 1 := by
      have h1 : algebraMap ↥K Ω ((-1 : (↥K)ˣ) : ↥K) = (-1 : Ω) := by
        rw [show ((-1 : (↥K)ˣ) : ↥K) = -1 from rfl, map_neg, map_one]
      rw [h1, Valuation.map_neg, Valuation.map_one]
    have hneg : Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        ζK hζ' hA (-1) z = 0 :=
      oPairGlob_units_eq_zero ζ hζ hζK (-1) z A hA hA2 hneg1 hunit_z
    have hsame : Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        ζK hζ' hA X z
        = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
            ζK hζ' hA X b :=
      Work.SSGRoute.ZDataMup.OddForm.oPairGlob_localClass (K := K) (p := 2) (k := k) (Ω := Ω)
        ζK hζ' hA X z b hlc
    have hchain : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        ζK hζ' (Work.SSGRoute.ZDataMup.galLift K ρ • A) hA'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
        = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
            ζK hζ' A hA
            (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
            (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) := by
      rw [cov, glob1, hadd, hneg, hsame, zero_add, ← glob2]
    exact hchain.symm

end Work.SSGRoute.ZDataTwo.TwoRec
