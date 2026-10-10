import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_pow_mul_unit_of_dvd_count
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesEscapePrimeSplit
import Submission.Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero
import Submission.Work.SSGRoute.ZConstruction.kummerCharZModAdd
import Submission.Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd
import Submission.Work.SSGRoute.step4_y_escape_v2.ReadOff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.GrunwaldEscapeCore

open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## Auxiliary lemmas for the correction step

These are the elementary transport and arithmetic lemmas used in the proof of
`gesCorrectionFromPrime` below. -/

/-- Two `Ω`-automorphisms (one over `↥K`, one over `k`) with the same underlying function act in the
same way on the places of `Ω`. -/
theorem gesSmulEqOfCoeEq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {φ : Ω ≃ₐ[↥K] Ω} {ψ : Ω ≃ₐ[k] Ω} (h : ⇑φ = ⇑ψ)
    (A : ValuationSubring Ω) : φ • A = ψ • A := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩

/-- An element of a local group `decomp k A ⊓ K.fixingSubgroup`, read as an element of
`Gal(Ω/↥K)`, still stabilises `A`. -/
theorem gesLocalToGalK_mem_decomp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {A : ValuationSubring Ω}
    (σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    Work.SSGRoute.gesLocalToGalK K σ ∈ SSGRoute.decomp (k := ↥K) A := by
  rw [MulAction.mem_stabilizer_iff]
  have hσ : (σ : Ω ≃ₐ[k] Ω) • A = A :=
    MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp σ.2).1
  rw [gesSmulEqOfCoeEq K (A := A)
    (show ⇑(Work.SSGRoute.gesLocalToGalK K σ) = ⇑(σ : Ω ≃ₐ[k] Ω) from rfl)]
  exact hσ

/-- Transport of the inertia condition: an element of `K.fixingSubgroup` which is inertia at a
place `B` remains inertia at `B` when viewed as an element of `Gal(Ω/↥K)`. -/
theorem gesInertia_of_gesGalKOfFixing {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (B : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω)
    (hσ : σ ∈ K.fixingSubgroup) (hI : SSGRoute.IsInertia k B σ) :
    SSGRoute.IsInertia (k := ↥K) B (Work.SSGRoute.gesGalKOfFixing K σ hσ) := by
  refine ⟨?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    have h1 : σ • B = B := MulAction.mem_stabilizer_iff.mp hI.1
    rw [gesSmulEqOfCoeEq K (A := B)
      (show ⇑(Work.SSGRoute.gesGalKOfFixing K σ hσ) = ⇑σ from rfl)]
    exact h1
  · intro x hx
    exact hI.2 x hx

/-- **The `K`-prime below a finite place of `Ω`.**  The restriction of a finite place `B` of `Ω`
over `k` to the finite Galois level `↥K` is the valuation ring of a height-one prime `𝔭` of
`𝓞[K]`. -/
theorem exists_primeIdeal_of_comap_ne_top {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [NumberField ↥K]
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B) :
    ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
  have hproper : B.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro htop
    apply hB
    refine top_unique ?_
    intro c _
    rw [ValuationSubring.mem_comap, IsScalarTower.algebraMap_apply k ↥K Ω]
    have hc : algebraMap k ↥K c ∈ B.comap (algebraMap ↥K Ω) := by rw [htop]; trivial
    rwa [ValuationSubring.mem_comap] at hc
  obtain ⟨𝔭, h𝔭⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
      (B.comap (algebraMap ↥K Ω)) hproper
      (fun x => Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring _ x)
  exact ⟨𝔭, h𝔭⟩

/-- The `𝔭`-adic exponent of the principal fractional ideal of `x·y⁻¹` is the difference of the
exponents of `x` and of `y`. -/
theorem count_spanSingleton_units_mul_inv {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x y : Kˣ) :
    FractionalIdeal.count K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          ((x * y⁻¹ : Kˣ) : K)) =
      FractionalIdeal.count K 𝔭
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (x : K)) -
        FractionalIdeal.count K 𝔭
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (y : K)) := by
  have hx : (x : K) ≠ 0 := Units.ne_zero x
  have hy : (y : K) ≠ 0 := Units.ne_zero y
  have hxne : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
      (x : K) ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
  have hyne : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
      ((y : K)⁻¹) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hy)
  rw [show ((x * y⁻¹ : Kˣ) : K) = (x : K) * (y : K)⁻¹ by simp,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K 𝔭 hxne hyne, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_inv]
  ring

/-- **The reading-off correction of Grünwald with escape, given the escape prime.**

Let `K/k` be a finite Galois extension of number fields inside `Ω`, `T` a finite set of finite
places of `Ω` whose `K`-primes lie in `T'`, and `a ∈ Kˣ`.  Suppose `𝔵` is a fractional ideal of `K`,
coprime to `T'`, whose divisor agrees with the divisor of `a` away from `T'`, except at the prime
`𝔮 ∉ T'` where it is one larger, and whose idèle class lies in `U = gesU K p T'`.  Then there is
`b ∈ Kˣ` whose Kummer character agrees with that of `a` on the decomposition group of every place of
`T`, and which is unramified (its Kummer character kills the inertia) at every finite place whose
`K`-prime lies in neither `T'` nor `{𝔮}`.

Route (all inputs are proved and axiom-clean; this is the "correction" step of the design's step 6,
with the escape prime already supplied).  Apply `Work.SSGRoute.readOff_gesU` to `𝔵` (hypotheses:
coprime to `T'`, and `hmem`): it returns `γ ∈ Kˣ` with `NK.UchidaKummer.localPowClass K p 𝔭 γ = 1`
for every `𝔭 ∈ T'` and `p ∣ count 𝔭 𝔵 - count 𝔭 (γ)` for every `𝔭`.  Set `b := a/γ` (so that
`b·a⁻¹ = γ⁻¹`).

* Local agreement at `T`: for `A ∈ T` with `K`-prime `𝔭 ∈ T'` (hypothesis `hTbelow`),
  `localPowClass` is multiplicative, so `b` and `a` have the same local class at `𝔭`; then
  `Work.SSGRoute.ZConstruction.kummerChar_eq_of_localPowClass_eq`
  (`Submission/Work/SSGRoute/ZConstruction/kummerChar_eq_of_localPowClass_eq.lean`) gives the
  agreement of the two Kummer characters on the decomposition group of `A`, transported to the
  `↥K`-side by `Work.SSGRoute.gesLocalToGalK` (`decomp k A ⊓ K.fixingSubgroup` maps into
  `decomp ↥K A` via `Work.SSGRoute.ges_decomp_of_mem_gal`).
* Unramifiedness away from `T' ∪ {𝔮}`: for a finite place `B` whose `K`-prime `𝔭_B` lies in neither,
  `h𝔵div` together with the read-off gives `p ∣ count 𝔭_B (b)`.  Then
  `Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd`
  (`Submission/Work/SSGRoute/kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd.lean`) applies: its
  hypothesis `∃ c u, b = c ^ p * u ∧ B.valuation (algebraMap u) = 1` follows from the
  `p`-divisibility of the valuation by taking for `c` a power of an element of `K` of valuation `1`
  at `𝔭_B`, and its hypothesis `¬ B.valuation (p : Ω) < 1` follows from `hT'p` (the primes above `p`
  all lie in `T'`).  The `↥K`-automorphism that the criterion produces is transported back to
  `K.fixingSubgroup` by `Work.SSGRoute.gesGalKOfFixing` (both `gesLocalToGalK` and `gesGalKOfFixing`
  are definitionally `IntermediateField.fixingSubgroupEquiv`). -/
theorem gesCorrectionFromPrime (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
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
      Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K p T') :
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
  -- ## Step 1: read off the subgroup `U = gesU K p T'`
  obtain ⟨γ, hγT, hγdiv⟩ :=
    Work.SSGRoute.readOff_gesU (K := ↥K) p T' 𝔵 h𝔵T hmem
  refine ⟨a * γ⁻¹, ?_, ?_⟩
  · -- ## Step 2: the Kummer characters of `a` and of `a · γ⁻¹` agree at `T`
    intro A hA σ
    have hAfin : SSGRoute.IsFinPlace k A := hTfin A hA
    obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
    -- `γ` is a local `p`-th power at `𝔭`, hence so is `γ⁻¹`, so the local classes of `a` and of
    -- `a · γ⁻¹` at `𝔭` agree
    have hγ1 : Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω)
        (K := K) (ζ := ζ) (hζ := hζ) (A := A) hAfin γ = 1 :=
      (Work.SSGRoute.ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (k := k) (Ω := Ω)
        (K := K) (ζ := ζ) (hζ := hζ) (A := A) hAfin 𝔭 h𝔭A γ).mpr (hγT 𝔭 h𝔭T')
    have hγinv : Work.SSGRoute.ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω)
        (K := K) (ζ := ζ) (hζ := hζ) (A := A) hAfin γ⁻¹ = 1 := by
      rw [map_inv, hγ1, inv_one]
    haveI hsepK : IsSepClosure ↥K Ω := ⟨inferInstance, inferInstance⟩
    have hkey := Work.SSGRoute.ZConstruction.kummerCharZMod_mul_eq_of_kummerCharMonoidHom_eq_one'
      (p := p) (k := k) (Ω := Ω) (K := K) ζ hζ A hAfin a γ⁻¹ hγinv
      (Work.SSGRoute.gesLocalToGalK K σ) (gesLocalToGalK_mem_decomp K σ)
    exact hkey.symm
  · -- ## Step 3: `b = a · γ⁻¹` is unramified outside `T' ∪ {𝔮}`
    intro B hB hnotT' hnot𝔮 σ hσ hI
    -- the `K`-prime `𝔭B` below `B`
    obtain ⟨𝔭B, h𝔭B⟩ := exists_primeIdeal_of_comap_ne_top K B hB
    have h𝔭B_notT' : 𝔭B ∉ T' := fun h => hnotT' 𝔭B h h𝔭B
    have h𝔭B_ne𝔮 : 𝔭B ≠ 𝔮 := fun h => hnot𝔮 (h ▸ h𝔭B)
    -- the `𝔭B`-adic exponent of `b = a · γ⁻¹`
    have hcount : FractionalIdeal.count ↥K 𝔭B
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((a * γ⁻¹ : (↥K)ˣ) : ↥K)) =
        FractionalIdeal.count ↥K 𝔭B
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
              (a : ↥K)) -
          FractionalIdeal.count ↥K 𝔭B
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
              (γ : ↥K)) :=
      count_spanSingleton_units_mul_inv (K := ↥K) 𝔭B a γ
    -- hence `p` divides it, by the read-off and the divisor hypothesis
    have hdiv : (p : ℤ) ∣ FractionalIdeal.count ↥K 𝔭B
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((a * γ⁻¹ : (↥K)ˣ) : ↥K)) := by
      rw [hcount, ← h𝔵div 𝔭B h𝔭B_notT' h𝔭B_ne𝔮]
      exact hγdiv 𝔭B
    -- split `b` as a `p`-th power times a unit at `𝔭B`
    obtain ⟨c, u, hcu, hcount_u⟩ :=
      exists_pow_mul_unit_of_dvd_count (K := ↥K) p (Fact.out : p.Prime).ne_zero 𝔭B (a * γ⁻¹) hdiv
    -- being a `𝔭B`-adic unit means being a unit at `B`
    have hu : B.valuation (algebraMap ↥K Ω (u : ↥K)) = 1 :=
      (valuation_eq_one_iff_count_eq_zero (K := ↥K) (Ω := Ω) B 𝔭B h𝔭B u).mpr hcount_u
    exact Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd k Ω K p ζ hζ B hB
      (by
        intro hlt
        obtain ⟨𝔭, h𝔭T', h𝔭eq⟩ := hT'p B hB hlt
        exact hnotT' 𝔭 h𝔭T' h𝔭eq)
      (a * γ⁻¹) ⟨c, u, hcu, hu⟩ (Work.SSGRoute.gesGalKOfFixing K σ hσ)
      (gesInertia_of_gesGalKOfFixing K B σ hσ hI)

end Work.SSGRoute.GrunwaldEscapeCore
