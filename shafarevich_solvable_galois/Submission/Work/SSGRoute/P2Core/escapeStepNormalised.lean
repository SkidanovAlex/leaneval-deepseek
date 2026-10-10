import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.ZDataTwo.mu2EscapeRealisationHKfresh
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` escape step *with* the odd-count normalisation

`Work.SSGRoute.ZDataTwo.mu2EscapeRealisationHKfresh` produces, from the datum `(g, h)` on the
`T`-blocks, a class `b ∈ (↥K)ˣ` and an escape prime `Q` with the prescribed local data, the
involution clause and the confinement clause.  Schmidt--Wingberg's §4 recursion needs one more
piece of information about this output, namely *condition (1)* of the paper: for the prime `𝔮` of
`↥K` below `Q`,

    `Odd (count_𝔮 b)`   (`b` has odd valuation at `𝔮`, i.e. `z = χ_b` is "normalised" at its own
    escape prime — this is what the crossed two-place value identity
    `Work.SSGRoute.NodeS37.crossedValue` consumes as its hypothesis `hnorm_*`).

The point of this file is that this clause is *not* new arithmetic: it is read off the very data
that the oracle's own construction already computes.  Concretely, `mu2EscapeRealisationHKfresh`'s
proof has

* `𝔵 = 𝔡 · (𝔮)` with `count_𝔮 𝔵 = count_𝔮 a + 1` (`h𝔵𝔮`), where `a` is the first element and `𝔡`
  the `T'`-free part of `a`, and
* `b = a · γ⁻¹`, where `γ` is the read-off element of the narrow modulus,
  `Work.SSGRoute.H9.readOff_narrow` (the "correction" step,
  `Work.SSGRoute.H9.correctionFromPrime_narrow`).

`readOff_narrow` supplies `2 ∣ count_𝔭 𝔵 − count_𝔭 γ` for *every* `𝔭`, hence at `𝔮`

    `count_𝔮 b = (count_𝔮 𝔵 − count_𝔮 γ) − 1`,

which is odd.

`Work.SSGRoute.H9.correctionFromPrime_narrow` existentially quantifies `b` and therefore hides
`γ`; `correctionFromPrime_narrow_odd` below is its proof verbatim, with `γ` exposed and the
count congruence returned.  `escapeStepNormalised` is then `mu2EscapeRealisationHKfresh`'s proof
with the one extra conjunct.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT
open NK.Chebotarev

namespace Work.SSGRoute.P2Core

/-- **The narrow correction step of the `p = 2` escape, with the read-off element exposed.**

This is `Work.SSGRoute.H9.correctionFromPrime_narrow`'s proof with `γ` returned instead of hidden:
`a * γ⁻¹` has the same local Kummer data at the places of `T` as `a`, is unramified outside the
`K`-primes of `T'` and of `𝔮`, and kills the involutions of `G_K` whenever `a` does; moreover the
`𝔮`-adic exponent congruence `2 ∣ count_𝔮 𝔵 − count_𝔮 γ` holds for every prime `𝔮`. -/
theorem correctionFromPrime_narrow_odd (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
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
      Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup ↥K)) :
    ∃ γ : (↥K)ˣ,
      (∀ 𝔮' : NK.Chebotarev.PrimeIdeal ↥K, (2 : ℤ) ∣ FractionalIdeal.count ↥K 𝔮' 𝔵 -
        FractionalIdeal.count ↥K 𝔮'
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (γ : ↥K))) ∧
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ (a * γ⁻¹)
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) →
        B.comap (algebraMap ↥K Ω) ≠
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ (a * γ⁻¹)
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) ∧
      (∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ (a * γ⁻¹)
          (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) := by
  classical
  obtain ⟨γ, hγT, hγdiv, hγpos⟩ :=
    Work.SSGRoute.H9.readOff_narrow (K := ↥K) T' 𝔵 h𝔵T hmem
  refine ⟨γ, hγdiv, ?_, ?_, ?_⟩
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

/-! ## The escape step with the odd-count normalisation -/

/-- **The `p = 2` escape step, with Schmidt--Wingberg's normalisation `Odd (count_𝔮 b)`.**

This is `Work.SSGRoute.ZDataTwo.mu2EscapeRealisationHKfresh`'s conclusion (the prescribed local
datum at the `T`-blocks, the involution clause, the confinement clause, the `k`-level freshness of
`Q`) together with the assertion that the produced class `b` has *odd* valuation at the prime `𝔮`
of `↥K` below `Q` — condition (1) of Schmidt--Wingberg §4, which the crossed two-place value
identity consumes as its normalisation hypothesis.

The clause is not new arithmetic: it is the count identity of the file `H9/NarrowCorrection` read
at `𝔮` (see the module docstring). -/
theorem escapeStepNormalised (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨ SSGRoute.IsSplitIn k Λ A)
    (hinertia : ∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (hhinf : ∀ A ∈ T, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → h A c = 0) :
    ∃ (b : (↥K)ˣ) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k Λ Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A Q) ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = g σ + h A σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
        (¬ Work.SSGRoute.gesKConj K Q B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0) ∧
      (∃ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
        Q.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
        Odd (FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (b : ↥K)))) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- the primitive second root of unity, viewed in `K`
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK 2 :=
    ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- (a) the totally positive first element realising the datum at `T`
  obtain ⟨a, ha, hapos⟩ :=
    Work.SSGRoute.ZDataTwo.firstElement_totallyPositive k Ω K ζK hζK' T hTfin hTdisj g hg hgc
      h hh hhc
  -- ## 0. the primes `T'` of `↥K` below the places of `T`
  let primeBelow : (A : {A // A ∈ T}) → NK.Chebotarev.PrimeIdeal ↥K :=
    fun A => (GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1 (hTfin A.1 A.2)).choose
  have hprimeBelow : ∀ A : {A // A ∈ T},
      A.1.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K (primeBelow A) :=
    fun A => (GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top K A.1
      (hTfin A.1 A.2)).choose_spec
  let T' : Finset (NK.Chebotarev.PrimeIdeal ↥K) := T.attach.image primeBelow
  have hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T',
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro A hA
    exact ⟨primeBelow ⟨A, hA⟩, Finset.mem_image_of_mem _ (Finset.mem_attach T ⟨A, hA⟩),
      hprimeBelow ⟨A, hA⟩⟩
  have hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T,
      A.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨A, -, hA⟩ := Finset.mem_image.mp h𝔭
    exact ⟨A.1, A.2, by rw [← hA]; exact hprimeBelow A⟩
  have hcomapK_ne_top : ∀ {B : ValuationSubring Ω}, SSGRoute.IsFinPlace k B →
      B.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro B hB htop
    apply hB
    refine le_antisymm le_top ?_
    intro x _
    have h1 : algebraMap ↥K Ω (algebraMap k ↥K x) ∈ B := by
      rw [← ValuationSubring.mem_comap, htop]
      exact trivial
    rwa [← IsScalarTower.algebraMap_apply k ↥K Ω] at h1
  -- the places over `2` lie in the classes of `T` (`hTcov`), so they lie over `T'`
  have hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (2 : Ω) < 1 →
      ∃ 𝔭 ∈ T', B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
    intro B hB hpB
    obtain ⟨A, hA, hconj⟩ := hTcov B hB (Or.inl hpB)
    obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
    obtain ⟨τ, hτ, hτA⟩ := hconj
    refine ⟨𝔭, h𝔭T', ?_⟩
    rw [← h𝔭A, ← hτA]
    have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ := funext fun _ => rfl
    rw [(GrunwaldEscapeCore.gesSmulEqOfCoeEq K hcoe A).symm]
    exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
  -- ## 1. the field `N' = baseChange K Λ` over `↥K`
  let N' : IntermediateField ↥K Ω := EscapeCoreLib.baseChange K Λ hKΛ
  have hN' : (N' : Set Ω) = (Λ : Set Ω) := by
    ext x
    exact EscapeCoreLib.mem_baseChange K Λ hKΛ
  haveI hN'fdk : FiniteDimensional k ↥N' := EscapeCoreLib.finiteDimensional_baseChange K Λ hKΛ
  haveI hN'fd : FiniteDimensional ↥K ↥N' := Module.Finite.of_restrictScalars_finite k ↥K ↥N'
  haveI hN'gal : IsGalois ↥K ↥N' := EscapeCoreLib.isGalois_baseChange K Λ hKΛ
  haveI hN'nf : NumberField ↥N' := NumberField.of_module_finite ↥K ↥N'
  -- ## 2. the class field `M` of the narrow modulus `U' = narrowGesU ↥K 2 T' ⊔ C_↥K²`
  let U' : Subgroup (IdeleClassGroup ↥K) :=
    Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup ↥K)
  have hU'fin : U'.FiniteIndex :=
    Work.SSGRoute.step4_y_escape_v2.finiteIndex_of_le le_sup_left
      (Work.SSGRoute.H9.narrowGesU_finiteIndex (K := ↥K) 2 T')
  have hU'open : IsOpen (U' : Set (IdeleClassGroup ↥K)) :=
    Work.SSGRoute.step4_y_escape_v2.isOpen_of_le_isOpen le_sup_left
      (Work.SSGRoute.H9.isOpen_narrowGesU 2 Nat.prime_two (K := ↥K) T')
  obtain ⟨M, hMfd, hMgal, hMnf, hMcomm, hMnorm⟩ :=
    GrunwaldEscapeCore.exists_abelian_classField_inside K U' hU'fin hU'open
  haveI : FiniteDimensional ↥K M := hMfd
  haveI : IsGalois ↥K M := hMgal
  haveI : NumberField ↥M := hMnf
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hMcomm
  -- ## 3. the trichotomy at `T`, from the dichotomy `horth`
  have horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ Λ.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ Λ.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0) := by
    intro A hA
    rcases horth A hA with h0 | hsplit
    · exact Or.inl h0
    · exact Or.inr (Or.inl (fun χ _ hχΛ σ hσ =>
        hχΛ σ (hsplit (Subgroup.mem_inf.mp hσ).1)))
  -- ## 4. the narrow orthogonality
  let 𝔡 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    Work.SSGRoute.tFreePart T' a
  have horth_mem : IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡) ∈
      U' ⊔ Idele.normClassSubgroup ↥K ↥N' := by
    have hraw := Work.H9Narrow.orthogonality_narrow_L2K (k := k) (Ω := Ω) K ζK hζK' Λ hKΛ
      T hTfin hTdisj hTcov g hg hgc hgram hginf h hh hhc horth₁ hinertia T' hTbelow hT'above
      M hMnorm N' hN' a ha hapos
    rw [hMnorm] at hraw
    exact hraw
  -- ## 5. the escape prime
  obtain ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', hQnotT, hQnotTk, hQcomap, hQmem⟩ :=
    Work.SSGRoute.ZDataTwo.escapePrimeKfresh K M U' hMnorm Λ N' hKΛ hN' T hTfin T' hTbelow
      (IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡)) horth_mem
  -- ## 6. the fractional ideal `𝔵 = 𝔡 · (𝔮)`
  let 𝔵 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    𝔡 * (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf
  have hcount𝔮 : ∀ q, FractionalIdeal.count ↥K q (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf =
      (if q = 𝔮 then 1 else 0) := by
    intro q
    rw [NK.GlobalCFT.Idele.count_idealOf]
    show NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K
      (fun q' => if q' = 𝔮 then 1 else 0) _) = _
    rw [NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  have hcount𝔡 : ∀ q, FractionalIdeal.count ↥K q 𝔡 =
      (if q ∈ T' then 0 else FractionalIdeal.count ↥K q
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (a : ↥K))) := by
    intro q
    rw [Work.SSGRoute.tFreePart_count]
    by_cases hq : q ∈ T'
    · rw [Work.SSGRoute.tFreeExp_of_mem T' a hq, if_pos hq]
    · rw [Work.SSGRoute.tFreeExp_of_not_mem T' a hq, if_neg hq,
        ← Idele.idealOf_principalIdele, Idele.count_idealOf]
  have h𝔡0 : 𝔡 ≠ 0 := by
    change Work.SSGRoute.tFreePart T' a ≠ 0
    exact Idele.idealOf_ne_zero _
  have hcount𝔵 : ∀ q, FractionalIdeal.count ↥K q 𝔵 =
      FractionalIdeal.count ↥K q 𝔡 + (if q = 𝔮 then 1 else 0) := by
    intro q
    change FractionalIdeal.count ↥K q (𝔡 * (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf) =
      FractionalIdeal.count ↥K q 𝔡 + (if q = 𝔮 then 1 else 0)
    rw [FractionalIdeal.count_mul ↥K q h𝔡0 (Idele.idealOf_ne_zero _), hcount𝔮 q]
  have h𝔵T : ∀ 𝔭 ∈ T', FractionalIdeal.count ↥K 𝔭 𝔵 = 0 := by
    intro 𝔭 h𝔭
    have h𝔭𝔮 : 𝔭 ≠ 𝔮 := fun hEq => h𝔮T' (hEq ▸ h𝔭)
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero, hcount𝔡 𝔭, if_pos h𝔭]
  have h𝔵div : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      𝔭 ∉ T' → 𝔭 ≠ 𝔮 → FractionalIdeal.count ↥K 𝔭 𝔵 =
        FractionalIdeal.count ↥K 𝔭
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)) := by
    intro 𝔭 h𝔭T h𝔭𝔮
    rw [hcount𝔵 𝔭, if_neg h𝔭𝔮, add_zero, hcount𝔡 𝔭, if_neg h𝔭T]
  have h𝔵𝔮 : FractionalIdeal.count ↥K 𝔮 𝔵 =
      FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (a : ↥K)) + 1 := by
    rw [hcount𝔵 𝔮, if_pos rfl, hcount𝔡 𝔮, if_neg h𝔮T']
  have hfrac𝔮 : NK.NUV2.RouteB.RayModulus.fracIdele
      ((NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf) = NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
    rw [NK.NUV2.RouteB.RayModulus.fracIdele_idealOf]
    refine (NK.HeckeL.Basic.IdeleFun.congr _ _ ?_).trans rfl
    funext q
    show NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.IdeleClassGroup.ideleOfFun ↥K
      (fun q' => if q' = 𝔮 then 1 else 0) _) = _
    rw [NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun]
  have hmem : IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) ∈ U' := by
    have hfrac : NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 =
        NK.NUV2.RouteB.RayModulus.fracIdele 𝔡 * NK.HeckeL.ideleOfPrime ↥K 𝔮 := by
      rw [show 𝔵 = 𝔡 * (NK.HeckeL.ideleOfPrime ↥K 𝔮).idealOf from rfl,
        NK.NUV2.RouteB.RayModulus.fracIdele_mul h𝔡0 (Idele.idealOf_ne_zero _), hfrac𝔮]
    have hC : IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡) =
        IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele
          (Work.SSGRoute.tFreePart T' a)) := rfl
    rw [hfrac, map_mul, hC]
    simpa only [mul_comm] using hQmem
  -- ## 7. the narrow correction, with the read-off element exposed
  obtain ⟨γ, hγdiv, hagree, hesc, hinv⟩ :=
    correctionFromPrime_narrow_odd k Ω K ζK hζK' T hTfin T' hTbelow hT'p a hapos
      𝔵 h𝔵T 𝔮 h𝔵div h𝔵𝔮 hmem
  -- ## 8. the assembly
  refine ⟨a * γ⁻¹, Q, hQfin, hQsplit, hQnotT, hQnotTk, ?_, ?_, ?_, ?_⟩
  · -- the prescribed local datum at `T`
    intro A hA σ hσ
    have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    show ZSplit.nodeKummerCocharZMod K ζ hζK hζ (a * γ⁻¹) σ = g σ + h A σ
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := a * γ⁻¹) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K ⟨σ, hσ⟩ := rfl
    rw [hto, hagree A hA ⟨σ, hσ⟩]
    exact (ha A hA ⟨σ, hσ⟩).symm
  · -- the involutions of `G_K`
    intro c hc hc2
    show ZSplit.nodeKummerCocharZMod K ζ hζK hζ (a * γ⁻¹) c = 0
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := a * γ⁻¹) hc]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ =
        Work.SSGRoute.gesGalKOfFixing K c hc := rfl
    rw [hto]
    exact hinv c hc hc2
  · -- unramified outside the classes of `T` and of `Q`
    intro B hBfin hBnotT hBnotQ σ hσ hI
    show ZSplit.nodeKummerCocharZMod K ζ hζK hζ (a * γ⁻¹) σ = 0
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := a * γ⁻¹) hσ]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ =
        Work.SSGRoute.gesGalKOfFixing K σ hσ := rfl
    rw [hto]
    refine hesc B hBfin ?_ ?_ σ hσ hI
    · intro 𝔭 h𝔭 heq
      obtain ⟨A, hA, hAcomap⟩ := hT'above 𝔭 h𝔭
      have hcomapK : A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hAcomap, heq]
      exact hBnotT A hA (Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
        (hcomapK_ne_top (hTfin A hA)) hcomapK)
    · intro heq
      have hcomapK : Q.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
        rw [hQcomap, heq]
      exact hBnotQ (Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
        (hcomapK_ne_top hQfin) hcomapK)
  · -- Schmidt--Wingberg's normalisation: `count_𝔮` of the corrected class is odd
    refine ⟨𝔮, hQcomap, ?_⟩
    have hsplit : FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (((a * γ⁻¹ : (↥K)ˣ)) : ↥K))
        = (FractionalIdeal.count ↥K 𝔮 𝔵 -
            FractionalIdeal.count ↥K 𝔮
              (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
                (γ : ↥K))) - 1 := by
      have h𝔵𝔮' : FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)) = FractionalIdeal.count ↥K 𝔮 𝔵 - 1 := by
        linarith [h𝔵𝔮]
      rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_mul_inv 𝔮 a γ, h𝔵𝔮']
      ring
    rw [hsplit]
    obtain ⟨k, hk⟩ := hγdiv 𝔮
    exact ⟨k - 1, by rw [hk]; ring⟩

end Work.SSGRoute.P2Core
