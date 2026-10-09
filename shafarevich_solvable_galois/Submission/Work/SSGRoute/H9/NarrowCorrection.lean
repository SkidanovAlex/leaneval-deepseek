import Mathlib
import Submission.Work.SSGRoute.H9.NarrowReadOff
import Submission.Work.SSGRoute.ZDataTwo.TotallyPositive
import Submission.Work.SSGRoute.step4_y_escape_v2.CorrectionSupPow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The narrow correction step of the `p = 2` escape, with the total positivity of the output

`Work.H9Narrow.correctionFromPrime_narrow` is
`Work.SSGRoute.step4_y_escape_v2.correctionFromPrime_supPow` with the *narrow* read-off
(`Work.SSGRoute.H9.readOff_narrow`) in place of the wide one, at `p = 2`, and with one extra
conclusion: the correcting class `b = a γ⁻¹` **kills the involutions of `G_K`**.

The extra clause is the point of the narrow modulus: the read-off element `γ` is totally positive
(`readOff_narrow`), the input `a` is assumed to be so (`hapos`), whence `b` is totally positive, and
`Work.SSGRoute.ZDataTwo.kummerCharZMod_eq_zero_of_forall_not_isNegAt` converts the positivity into
the vanishing of `χ_b` at every involution.  In the character formulation the argument is even more
direct: `χ_b = χ_a + χ_{γ⁻¹}` (`kummerCharZMod_add`), the first term vanishes by `hapos` and the
second by `ZDataTwo.realPlace_involution_kummerChar_iff` (for each involution `c`, `χ_{γ⁻¹}(c) = 0`
is equivalent to the positivity of `γ` at the associated real place).
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.H9

/-- **The correction step of the `p = 2` escape with the narrow read-off.**  With the classes `a`
and the fractional ideal `𝔵 = 𝔡 · (𝔮)` of the escape construction, and with the membership
`mk (fracIdele 𝔵) ∈ narrowGesU ↥K 2 T' ⊔ C_K²` produced by the (narrow) escape prime, there is
`b ∈ (↥K)ˣ` with the *same* local Kummer data at the places of `T` as `a`, unramified outside the
`K`-primes of `T'` and of `𝔮`, and killing the involutions of `G_K` whenever `a` does. -/
theorem correctionFromPrime_narrow (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (2 : Ω) < 1 →
      ∃ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (a : (↥K)ˣ)
    (hapos : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0)
    (𝔵 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K)
    (h𝔵T : ∀ 𝔭 ∈ T', FractionalIdeal.count ↥K 𝔭 𝔵 = 0)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔵div : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      𝔭 ∉ T' → 𝔭 ≠ 𝔮 → FractionalIdeal.count ↥K 𝔭 𝔵 =
        FractionalIdeal.count ↥K 𝔭
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)))
    (h𝔵𝔮 : FractionalIdeal.count ↥K 𝔮 𝔵 =
        FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)) + 1)
    (hmem : IdeleClassGroup.mk ↥K
        (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) ∈
      narrowGesU ↥K 2 T' ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup ↥K)) :
    ∃ b : (↥K)ˣ,
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) →
        B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) ∧
      (∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
          (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) := by
  classical
  obtain ⟨γ, hγT, hγdiv, hγpos⟩ := readOff_narrow (K := ↥K) T' 𝔵 h𝔵T hmem
  refine ⟨a * γ⁻¹, ?_, ?_, ?_⟩
  · -- the local agreement at the places of `T`
    intro A hA σ
    obtain ⟨𝔭, h𝔭T', h𝔭c⟩ := hTbelow A hA
    have hzero := Work.SSGRoute.GrunwaldEscapeCore.kummerChar_eq_zero_on_decomp_of_localPow
      k Ω K 2 ζ hζ A (hTfin A hA) 𝔭 h𝔭c γ (hγT 𝔭 h𝔭T') σ
    have hmul : a = γ * (a * γ⁻¹) := by
      rw [← mul_assoc, mul_comm γ a, mul_assoc, mul_inv_cancel, mul_one]
    have hadd := Work.SSGRoute.ZConstruction.kummerCharZMod_add (p := 2) (K := K) (Ω := Ω)
      (ζ := ζ) (hζ := hζ) γ (a * γ⁻¹) (Work.SSGRoute.gesLocalToGalK K σ)
    rw [← hmul] at hadd
    rw [hadd, hzero, zero_add]
  · -- unramifiedness away from the primes of `T'` and from `𝔮`
    intro B hBfin hBnotT' hBnot𝔮 σ hσ hI
    -- the prime of `↥K` below `B`
    obtain ⟨𝔭B, h𝔭B⟩ :=
      Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
        (L := ↥K) (B.comap (algebraMap ↥K Ω))
        ((Work.SSGRoute.isFinPlace_baseChange k Ω K B).mpr hBfin)
        (fun x => by
          rw [ValuationSubring.mem_comap]
          rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥K) ↥K Ω x]
          exact Work.SSGRoute.ringOfIntegers_mem_of_isFinPlace_k k Ω B hBfin K x)
    have h𝔭BT' : 𝔭B ∉ T' := fun hmem => hBnotT' 𝔭B hmem h𝔭B
    have h𝔭B𝔮 : 𝔭B ≠ 𝔮 := fun hEq => hBnot𝔮 (by rw [h𝔭B, hEq])
    -- divisibility of the `𝔭B`-adic exponent of `a / γ`
    have hdvd : (2 : ℤ) ∣ FractionalIdeal.count ↥K 𝔭B
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (((a * γ⁻¹ : (↥K)ˣ)) : ↥K)) := by
      rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_mul_inv 𝔭B a γ,
        ← h𝔵div 𝔭B h𝔭BT' h𝔭B𝔮]
      exact hγdiv 𝔭B
    have hlogdvd : (2 : ℤ) ∣
        (𝔭B.valuation ↥K (((a * γ⁻¹ : (↥K)ˣ)) : ↥K)).log := by
      have hne : (((a * γ⁻¹ : (↥K)ˣ)) : ↥K) ≠ 0 := Units.ne_zero _
      have h1 : (𝔭B.valuation ↥K (((a * γ⁻¹ : (↥K)ˣ)) : ↥K)).log
          = -FractionalIdeal.count ↥K 𝔭B
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
              (((a * γ⁻¹ : (↥K)ˣ)) : ↥K)) := by
        have h2 := Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log 𝔭B hne
        linarith
      rw [h1]
      exact dvd_neg.mpr hdvd
    -- split off the square
    obtain ⟨c, u, hcu, huval⟩ :=
      Work.SSGRoute.EscapeCoreLib.powMulUnit_of_dvd_log 𝔭B 2 (Fact.out : Nat.Prime 2)
        (a * γ⁻¹) hlogdvd
    -- `u` is a unit at `B`
    have huO : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭B).valuation
        (u : ↥K) = 1 :=
      (Work.SSGRoute.EscapeCoreLib.valuationSubringAtPrime_valuation_eq_one_iff
        𝔭B (u : ↥K)).mpr huval
    have huB : B.valuation (algebraMap ↥K Ω (u : ↥K)) = 1 :=
      Work.SSGRoute.EscapeCoreLib.valuation_eq_one_of_comap_eq B
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭B) h𝔭B huO
    -- `2` is a unit at `B`
    have hp : ¬ B.valuation (2 : Ω) < 1 := fun hlt => by
      obtain ⟨𝔭', h𝔭'T', h𝔭'c⟩ := hT'p B hBfin hlt
      exact hBnotT' 𝔭' h𝔭'T' h𝔭'c
    have hI' : SSGRoute.IsInertia (k := ↥K) B
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) :=
      (Work.SSGRoute.isInertia_baseChange k Ω K B σ hσ).mpr hI
    have hto : Work.SSGRoute.gesGalKOfFixing K σ hσ =
        (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ := rfl
    rw [hto]
    exact Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd k Ω K 2 ζ hζ B hBfin
      hp (a * γ⁻¹) ⟨c, u, hcu, huB⟩ ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) hI'
  · -- the involutions: `χ_{a γ⁻¹} = χ_a + χ_{γ⁻¹}` and `γ` is totally positive
    intro c hc hc2
    have hadd := Work.SSGRoute.ZConstruction.kummerCharZMod_add (p := 2) (K := K) (Ω := Ω)
      (ζ := ζ) (hζ := hζ) a γ⁻¹ (Work.SSGRoute.gesGalKOfFixing K c hc)
    rw [hadd, hapos c hc hc2, zero_add]
    by_cases hc1 : c = 1
    · subst hc1
      have hone : Work.SSGRoute.gesGalKOfFixing K (1 : Ω ≃ₐ[k] Ω) hc = 1 :=
        map_one (IntermediateField.fixingSubgroupEquiv K)
      rw [hone, Work.SSGRoute.kummerCharZMod_apply]
      exact Work.SSGRoute.kummerIdx_one 2 hζ γ⁻¹ _ _
    · obtain ⟨w, hwreal, hw⟩ :=
        ZDataTwo.realPlace_involution_kummerChar_iff k Ω K ζ hζ c hc hc2 hc1
      have hto : Work.SSGRoute.gesGalKOfFixing K c hc =
          (IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ := rfl
      rw [hto, hw γ⁻¹]
      -- `γ⁻¹` is not negative at `w`, because `γ` is positive there
      have hposγ : 0 < InfinitePlace.embedding_of_isReal hwreal (γ : ↥K) := hγpos w hwreal
      intro hneg
      obtain ⟨hw', hlt⟩ := hneg
      have hcoe : InfinitePlace.embedding_of_isReal hw'
          ((γ⁻¹ : (↥K)ˣ) : ↥K) = (InfinitePlace.embedding_of_isReal hw' (γ : ↥K))⁻¹ := by
        rw [show ((γ⁻¹ : (↥K)ˣ) : ↥K) = ((γ : ↥K))⁻¹ from Units.val_inv_eq_inv_val γ,
          map_inv₀]
      rw [hcoe] at hlt
      have hlt' : InfinitePlace.embedding_of_isReal hw' (γ : ↥K) < 0 :=
        inv_lt_zero.mp hlt
      have hpos' : 0 < InfinitePlace.embedding_of_isReal hw' (γ : ↥K) := by
        rw [← ZDataTwo.embedding_of_isReal_eq hwreal hw']
        exact hposγ
      exact absurd hlt' (not_lt.mpr (le_of_lt hpos'))

end Work.SSGRoute.H9
