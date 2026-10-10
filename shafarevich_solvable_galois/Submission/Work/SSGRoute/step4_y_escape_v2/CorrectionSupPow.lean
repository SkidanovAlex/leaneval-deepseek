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
import Submission.Work.SSGRoute.EscapeCoreLib.correctionFromPrime
import Submission.Work.SSGRoute.EscapeCoreLib.readOffSupPow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The correction step of the Grünwald escape with the hypothesis `hmem ∈ U'`

`Work.SSGRoute.step4_y_escape_v2.correctionFromPrime_supPow` is the variant of
`Work.SSGRoute.EscapeCoreLib.correctionFromPrime` in which the hypothesis `hmem` is weakened from
membership in `gesU ↥K p T' = im(Kˣ · E_{T',unr})` to membership in
`gesU ↥K p T' ⊔ pPowSubgroup p C_↥K` — the form in which the orthogonality produces it.  The proof
is the text of `correctionFromPrime` with the single call `Work.SSGRoute.readOff_gesU` replaced by
`Work.SSGRoute.EscapeCoreLib.readOffSupPow` (whose conclusion is identical).
-/

namespace Work.SSGRoute.step4_y_escape_v2

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-- **The correction step of the Grünwald escape, with the orthogonality hypothesis `hmem ∈ U'`**
(`U' = gesU ⊔ C_K^p` instead of `gesU`).  See the module docstring. -/
theorem correctionFromPrime_supPow (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
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
      ((NK.GlobalCFT.Idele.principalSubgroup ↥K ⊔ Work.SSGRoute.powTIdeles ↥K p T').map
          (NK.GlobalCFT.IdeleClassGroup.mk ↥K))
        ⊔ Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (NK.GlobalCFT.IdeleClassGroup ↥K)) :
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
  obtain ⟨γ, hγT, hγdiv⟩ :=
    Work.SSGRoute.EscapeCoreLib.readOffSupPow (K := ↥K) p T' 𝔵 h𝔵T hmem
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
      rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_mul_inv 𝔭B a γ,
        ← h𝔵div 𝔭B h𝔭BT' h𝔭B𝔮]
      exact hγdiv 𝔭B
    have hlogdvd : (p : ℤ) ∣
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
    -- split off the `p`-th power
    obtain ⟨c, u, hcu, huval⟩ :=
      Work.SSGRoute.EscapeCoreLib.powMulUnit_of_dvd_log 𝔭B p (Fact.out : p.Prime)
        (a * γ⁻¹) hlogdvd
    -- `u` is a unit at `B`
    have huO : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭B).valuation
        (u : ↥K) = 1 :=
      (Work.SSGRoute.EscapeCoreLib.valuationSubringAtPrime_valuation_eq_one_iff
        𝔭B (u : ↥K)).mpr huval
    have huB : B.valuation (algebraMap ↥K Ω (u : ↥K)) = 1 :=
      Work.SSGRoute.EscapeCoreLib.valuation_eq_one_of_comap_eq B
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

end Work.SSGRoute.step4_y_escape_v2
