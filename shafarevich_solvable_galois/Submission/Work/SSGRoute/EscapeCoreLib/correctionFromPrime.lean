import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.EscapeCoreLib.algEquiv_extend_compositum
import Submission.Work.SSGRoute.EscapeCoreLib.count_spanSingleton_mul_inv
import Submission.Work.SSGRoute.EscapeCoreLib.exists_finiteDimensional_galois_superset
import Submission.Work.SSGRoute.EscapeCoreLib.powMulUnit_of_dvd_log
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.GrunwaldEscapeCore.grunwald_escape_correction
import Submission.Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv
import Submission.Work.SSGRoute.ZConstruction.kummerCharMonoidHom
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.Work.SSGRoute.ZSplit.BaseChange
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd
import Submission.Work.SSGRoute.ssg8Chebotarev
import Submission.Work.SSGRoute.step4_y_escape_v2.ReadOff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.EscapeCoreLib

set_option maxHeartbeats 1000000

/-- The `𝔭`-adic exponent `FractionalIdeal.count` of a principal fractional ideal is the negative
of the logarithm of the `𝔭`-adic valuation of the generator. -/
theorem count_spanSingleton_eq_neg_log {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {x : K}
    (hx : x ≠ 0) :
    FractionalIdeal.count K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x)
      = -(𝔭.valuation K x).log := by
  have h1 : 𝔭.valuation K x = WithZero.exp
      (-(FractionalIdeal.count K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x))) := by
    rw [← Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq (K := K) 𝔭 x]
    exact NK.CFTLib.ArtinReciprocityIdeal.valued_algebraMap_eq_exp_neg_count_spanSingleton 𝔭 hx
  have h2 := congrArg WithZero.log h1
  rw [WithZero.log_exp] at h2
  linarith

/-- The valuation of the valuation ring at `𝔭` takes the value `1` exactly where the height-one
spectrum valuation does. -/
theorem valuationSubringAtPrime_valuation_eq_one_iff {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) :
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭).valuation x = 1
      ↔ 𝔭.valuation K x = 1 := by
  have hEq : ((IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭).valuation).IsEquiv
      (𝔭.valuation K) := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro y
    rw [ValuationSubring.valuation_le_one_iff,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
  exact hEq.eq_one_iff_eq_one

/-- If `O` is the pullback of the valuation ring `W` of `L` along `K → L`, then the value of an
element of `K` which is a unit at `O` is `1` at `W`. -/
theorem valuation_eq_one_of_comap_eq {K L : Type} [Field K] [Field L] [Algebra K L]
    (W : ValuationSubring L) (O : ValuationSubring K) (h : W.comap (algebraMap K L) = O)
    {u : K} (hu : O.valuation u = 1) : W.valuation (algebraMap K L u) = 1 := by
  have hEq : (W.valuation.comap (algebraMap K L)).IsEquiv O.valuation := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro y
    rw [Valuation.comap_apply, ValuationSubring.valuation_le_one_iff,
      ← ValuationSubring.mem_comap, h, ValuationSubring.valuation_le_one_iff]
  have h1 : (W.valuation.comap (algebraMap K L)) u = 1 :=
    (hEq.eq_one_iff_eq_one (x := u)).mpr hu
  rwa [Valuation.comap_apply] at h1

theorem correctionFromPrime (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
      ∃ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (a : (↥K)ˣ)
    (𝔵 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K)
    (h𝔵T : ∀ 𝔭 ∈ T', FractionalIdeal.count ↥K 𝔭 𝔵 = 0)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔵div : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      𝔭 ∉ T' → 𝔭 ≠ 𝔮 → FractionalIdeal.count ↥K 𝔭 𝔵 =
        FractionalIdeal.count ↥K 𝔭
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)))
    (h𝔵𝔮 : 𝔮 ∉ T' → FractionalIdeal.count ↥K 𝔮 𝔵 =
        FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)) + 1)
    (hmem : NK.GlobalCFT.IdeleClassGroup.mk ↥K
        (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) ∈
      (NK.GlobalCFT.Idele.principalSubgroup ↥K ⊔ Work.SSGRoute.powTIdeles ↥K p T').map
        (NK.GlobalCFT.IdeleClassGroup.mk ↥K)) :
    ∃ b : (↥K)ˣ,
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) →
        B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) := by
  classical
  obtain ⟨γ, hγT, hγdiv⟩ := Work.SSGRoute.readOff_gesU (K := ↥K) p T' 𝔵 h𝔵T hmem
  refine ⟨a * γ⁻¹, ?_, ?_⟩
  · -- the local agreement at the places of `T`
    intro A hA σ
    obtain ⟨𝔭, h𝔭T', h𝔭c⟩ := hTbelow A hA
    have hzero := Work.SSGRoute.GrunwaldEscapeCore.kummerChar_eq_zero_on_decomp_of_localPow
      k Ω K p ζ hζ A (hTfin A hA) 𝔭 h𝔭c γ (hγT 𝔭 h𝔭T') σ
    have hmul : a = γ * (a * γ⁻¹) := by
      rw [← mul_assoc, mul_comm γ a, mul_assoc, mul_inv_cancel, mul_one]
    have hadd := Work.SSGRoute.ZConstruction.kummerCharZMod_add (p := p) (K := K) (Ω := Ω)
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
    have hdvd : (p : ℤ) ∣ FractionalIdeal.count ↥K 𝔭B
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (((a * γ⁻¹ : (↥K)ˣ)) : ↥K)) := by
      rw [count_spanSingleton_mul_inv 𝔭B a γ, ← h𝔵div 𝔭B h𝔭BT' h𝔭B𝔮]
      exact hγdiv 𝔭B
    have hlogdvd : (p : ℤ) ∣
        (𝔭B.valuation ↥K (((a * γ⁻¹ : (↥K)ˣ)) : ↥K)).log := by
      have hne : (((a * γ⁻¹ : (↥K)ˣ)) : ↥K) ≠ 0 := Units.ne_zero _
      have h1 : (𝔭B.valuation ↥K (((a * γ⁻¹ : (↥K)ˣ)) : ↥K)).log
          = -FractionalIdeal.count ↥K 𝔭B
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
              (((a * γ⁻¹ : (↥K)ˣ)) : ↥K)) := by
        have h2 := count_spanSingleton_eq_neg_log 𝔭B hne
        linarith
      rw [h1]
      exact dvd_neg.mpr hdvd
    -- split off the `p`-th power
    obtain ⟨c, u, hcu, huval⟩ :=
      powMulUnit_of_dvd_log 𝔭B p (Fact.out : p.Prime) (a * γ⁻¹) hlogdvd
    -- `u` is a unit at `B`
    have huO : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭B).valuation
        (u : ↥K) = 1 :=
      (valuationSubringAtPrime_valuation_eq_one_iff 𝔭B (u : ↥K)).mpr huval
    have huB : B.valuation (algebraMap ↥K Ω (u : ↥K)) = 1 :=
      valuation_eq_one_of_comap_eq B
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭B) h𝔭B huO
    -- `p` is a unit at `B`
    have hp : ¬ B.valuation (p : Ω) < 1 := fun hlt => by
      obtain ⟨𝔭', h𝔭'T', h𝔭'c⟩ := hT'p B hBfin hlt
      exact hBnotT' 𝔭' h𝔭'T' h𝔭'c
    have hI' : SSGRoute.IsInertia (k := ↥K) B
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) :=
      (Work.SSGRoute.isInertia_baseChange k Ω K B σ hσ).mpr hI
    have hto : Work.SSGRoute.gesGalKOfFixing K σ hσ =
        (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ := rfl
    rw [hto]
    exact Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd k Ω K p ζ hζ B hBfin
      hp (a * γ⁻¹) ⟨c, u, hcu, huB⟩ ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) hI'

end Work.SSGRoute.EscapeCoreLib