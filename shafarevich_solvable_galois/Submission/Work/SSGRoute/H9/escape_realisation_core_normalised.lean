import Mathlib.FieldTheory.KrullTopology
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
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_realisation_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

/-! ## Two elementary lemmas on `p`-th powers at the escape prime

A `p`-th power is invisible to the level-`K` Kummer cochain, and an element whose `𝔮`-adic
exponent is `-1` modulo `p` can be completed to an element of `𝔮`-adic exponent `1` by a `p`-th
power (so that the product is a `p`-th power, hence locally trivial at the escape prime). -/

/-- **A `p`-th power is invisible to the level-`K` Kummer cochain.** -/
lemma nodeKummerCocharZMod_pow_eq_zero {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (c : (↥K)ˣ) :
    ZSplit.nodeKummerCocharZMod K ζ hζK hζ (c ^ p) = 0 := by
  funext σ
  by_cases hσ : σ ∈ K.fixingSubgroup
  · rw [ZSplit.nodeKummerCocharZMod_apply (β := c ^ p) hσ]
    exact (Work.SSGRoute.ZConstruction.kummerCharZMod_fixingSubgroup_mul_pow p k Ω K ⟨ζ, hζK⟩
      (ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)).2 c ⟨σ, hσ⟩
  · rw [ZSplit.nodeKummerCocharZMod_of_notMem hσ]
    rfl

/-- **From `count_𝔮(b) ≡ -1 (mod p)` to an element of `𝔮`-adic exponent `1`.**  There is `c ∈ Kˣ`
such that `b⁻¹ · c ^ p` has `𝔮`-adic exponent exactly `1`; equivalently `b · (b⁻¹ c ^ p) = c ^ p` is
a `p`-th power vanishing at `𝔮` to order `-1`. -/
lemma exists_count_one_complement (p : ℕ) {K : Type} [Field K] [NumberField K] (hp : p.Prime)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (b : Kˣ)
    (hdiv : (p : ℤ) ∣ FractionalIdeal.count K 𝔮
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (b : K)) + 1) :
    ∃ c : Kˣ, FractionalIdeal.count K 𝔮
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (((b⁻¹ * c ^ p : Kˣ)) : K)) = 1 := by
  classical
  have hbne : (b : K) ≠ 0 := Units.ne_zero b
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮 (b : K)).log - 1 = (p : ℤ) * m := by
    have hcl := Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := K) 𝔮 hbne
    have hdvd : (p : ℤ) ∣
        -(IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮 (b : K)).log + 1 := by
      rw [← hcl]
      exact hdiv
    obtain ⟨n, hn⟩ := hdvd
    exact ⟨-n, by rw [mul_neg]; linarith⟩
  obtain ⟨c₀, hc₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective K 𝔮
    (WithZero.exp m)
  have hc₀ne : c₀ ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hc₀
    exact WithZero.exp_ne_zero hc₀.symm
  refine ⟨Units.mk0 c₀ hc₀ne, ?_⟩
  have hcval : (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮
      ((Units.mk0 c₀ hc₀ne : Kˣ) : K)) = WithZero.exp m := by
    rw [Units.val_mk0]
    exact hc₀
  have hv1 : (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮 (b : K))⁻¹ ≠ 0 :=
    inv_ne_zero ((Valuation.ne_zero_iff _).mpr hbne)
  have hv2 : ((IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮
      ((Units.mk0 c₀ hc₀ne : Kˣ) : K))) ^ p ≠ 0 :=
    pow_ne_zero p ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))
  have hxlog : (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮
      (((b⁻¹ * (Units.mk0 c₀ hc₀ne) ^ p : Kˣ)) : K)).log = -1 := by
    have hval : (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮
        (((b⁻¹ * (Units.mk0 c₀ hc₀ne) ^ p : Kˣ)) : K))
        = (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮 (b : K))⁻¹ *
          (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔮
            ((Units.mk0 c₀ hc₀ne : Kˣ) : K)) ^ p := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.val_mk0, map_mul, map_inv₀, map_pow]
    rw [hval, WithZero.log_mul hv1 hv2, WithZero.log_inv, WithZero.log_pow,
      hcval, WithZero.log_exp, nsmul_eq_mul, ← hm]
    ring
  rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := K) 𝔮 (Units.ne_zero _),
    hxlog]
  norm_num

/-! ## The correction step with the escape normalisation `v_𝔮(b) ≡ -1 (mod p)`

This is `Work.SSGRoute.step4_y_escape_v2.correctionFromPrime_supPow` with one extra conclusion: the
correcting element `b = a · γ⁻¹` has `𝔮`-adic exponent congruent to `-1` modulo `p`.  The reading-off
step `Work.SSGRoute.EscapeCoreLib.readOffSupPow` already produces the element `γ` with
`p ∣ count_𝔮 𝔵 - count_𝔮 γ`, and the additional congruence follows from
`count_spanSingleton_mul_inv` and `count_𝔮 𝔵 = count_𝔮 a + 1`. -/

theorem correctionFromPrime_supPow_uniformised (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
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
    (h𝔮T' : 𝔮 ∉ T')
    (h𝔵div : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      𝔭 ∉ T' → 𝔭 ≠ 𝔮 → FractionalIdeal.count ↥K 𝔭 𝔵 =
        FractionalIdeal.count ↥K 𝔭
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K)))
    (h𝔵𝔮 : FractionalIdeal.count ↥K 𝔮 𝔵 =
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
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) ∧
      ((p : ℤ) ∣ FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (b : ↥K)) + 1) := by
  classical
  obtain ⟨γ, hγT, hγdiv⟩ :=
    Work.SSGRoute.EscapeCoreLib.readOffSupPow (K := ↥K) p T' 𝔵 h𝔵T hmem
  refine ⟨a * γ⁻¹, ?_, ?_, ?_⟩
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
  · -- the escape normalisation `v_𝔮(b) ≡ -1 (mod p)`
    rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_mul_inv 𝔮 a γ]
    have h : (p : ℤ) ∣ (FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (a : ↥K))
        - FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (γ : ↥K))) + 1 := by
      have h2 := hγdiv 𝔮
      rw [h𝔵𝔮] at h2
      convert h2 using 1
      ring
    exact h

/-- **The escape realisation with the Frobenius normalisation at the escape prime.**  The
statement of `Work.SSGRoute.GrunwaldEscapeCore.escape_realisation_core`, with two additions to the
conclusion: (i) the produced class `z` is the level-`K` Kummer cochain
`Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b` of an explicit `b ∈ (↥K)ˣ`; (ii) at the
escape prime `Q` the class of `b` is the *inverse uniformiser* class: there is `u ∈ (↥K)ˣ` with
`count_𝔮(u) = 1` for `𝔮` the prime of `↥K` below `Q` and `b·u` locally trivial (kills the local
group) at `Q`.  This is the "strengthened escape normalisation" `v_Q(b) ≡ −1 (mod p)` of
Schmidt–Wingberg §4 condition (1), needed for the two-place reciprocity of the `§3` chain; it is
the arithmetic input missing from disk (the node `Work.SSGRoute.ZDataMup.escape_uniformised` and
the shared lane's `escape_correction_uniformised` both wait on it). -/
theorem escape_realisation_core_normalised (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      SSGRoute.IsSplitIn k N A) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω) (b : (↥K)ˣ),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = g σ + h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → (¬ Work.SSGRoute.gesKConj K Q B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ σ ∈ K.fixingSubgroup, z σ = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ) ∧
      (∃ u : (↥K)ˣ,
        (∃ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
          Q.comap (algebraMap ↥K Ω) =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
          FractionalIdeal.count ↥K 𝔮
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
              (u : ↥K)) = 1) ∧
        (∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k Q →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (b * u) σ = 0)) := by
  classical
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- the primitive `p`-th root of unity, viewed in `K`
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK p :=
    ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- `hKimag` is vacuous for `p ≠ 2`
  have hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1 :=
    fun h2 => absurd h2 hp
  -- (a) Grünwald + Kummer: the element realising the datum at `T`
  obtain ⟨a, ha⟩ := GrunwaldEscapeCore.grunwald_kummer_first_element p k Ω K ζK hζK' hKimag T
    hTfin hTdisj g hg hgc h hh hhc
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
  -- the places over `p` lie in the classes of `T` (`hTcov`), so they lie over `T'`
  have hT'p : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → B.valuation (p : Ω) < 1 →
      ∃ 𝔭 ∈ T',
        B.comap (algebraMap ↥K Ω) =
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
  -- ## 1. the field `N' = baseChange K N` over `↥K`
  let N' : IntermediateField ↥K Ω := EscapeCoreLib.baseChange K N hKN
  have hN' : (N' : Set Ω) = (N : Set Ω) := by
    ext x
    exact EscapeCoreLib.mem_baseChange K N hKN
  haveI hN'fdk : FiniteDimensional k ↥N' := EscapeCoreLib.finiteDimensional_baseChange K N hKN
  haveI hN'fd : FiniteDimensional ↥K ↥N' :=
    Module.Finite.of_restrictScalars_finite k ↥K ↥N'
  haveI hN'gal : IsGalois ↥K ↥N' := EscapeCoreLib.isGalois_baseChange K N hKN
  haveI hN'nf : NumberField ↥N' := NumberField.of_module_finite ↥K ↥N'
  -- ## 2. the class field `M` of `U' = gesU ↥K p T' ⊔ C_↥K^p`
  let U' : Subgroup (IdeleClassGroup ↥K) :=
    GrunwaldEscapeCore.gesU ↥K p T' ⊔ EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K)
  obtain ⟨M, hMfd, hMgal, hMnf, hMcomm, hMnorm⟩ :=
    GrunwaldEscapeCore.exists_abelian_classField_inside K U'
      (Work.SSGRoute.step4_y_escape_v2.finiteIndex_gesU_sup_pPow (p := p) (K := ↥K) T')
      (Work.SSGRoute.step4_y_escape_v2.isOpen_gesU_sup_pPow p T')
  haveI : FiniteDimensional ↥K M := hMfd
  haveI : IsGalois ↥K M := hMgal
  haveI : NumberField ↥M := hMnf
  haveI : IsMulCommutative (↥M ≃ₐ[↥K] ↥M) := hMcomm
  -- ## 3. the orthogonality, in the surviving case `L₂ = K`
  let 𝔡 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K :=
    Work.SSGRoute.tFreePart T' a
  have horth_mem : IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡) ∈
      U' ⊔ Idele.normClassSubgroup ↥K ↥N' := by
    have hraw := GrunwaldEscapeCore.orthogonality_L2K p hp k Ω K ζK hζK' hKimag N hKN T hTfin
      hTdisj hTcov g hg hgc hgram h hh hhc horth T' hTbelow hT'above M hMnorm N' hN' a ha
    rw [hMnorm] at hraw
    exact hraw
  -- ## 4. the escape prime, `Q` split completely in `N`
  obtain ⟨Q, 𝔮, hQfin, hQsplit, h𝔮T', hQnotT, hQcomap, hQmem⟩ :=
    GrunwaldEscapeCore.escape_prime_orthogonality K M U' hMnorm N N' hKN hN' T hTfin T' hTbelow
      (IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡)) horth_mem
  -- ## 5. the fractional ideal `𝔵 = 𝔡 · (𝔮)`
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
  -- ## 6. the membership of `𝔵` in `U'`
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
          (Work.SSGRoute.tFreePart T' a)) :=
      rfl
    rw [hfrac, map_mul, hC]
    simpa only [mul_comm] using hQmem
  -- ## 7. the correction, with the escape normalisation
  obtain ⟨b, hagree, hesc, hdiv⟩ :=
    correctionFromPrime_supPow_uniformised p k Ω K ζK hζK' T hTfin T' hTbelow hT'p a 𝔵 h𝔵T 𝔮
      h𝔮T' h𝔵div h𝔵𝔮 hmem
  -- ## 8. the assembly
  refine ⟨ZSplit.nodeKummerCocharZMod K ζ hζK hζ b, Q, b, hQfin, hQsplit, hQnotT,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- additivity on `G_K`
    exact ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b
  · -- local constancy on `G_K`
    exact ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ b
  · -- the prescribed local datum at `T`
    intro A hA σ hσ
    have hσK : (σ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨(σ : Ω ≃ₐ[k] Ω), hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K ⟨σ, hσ⟩ := rfl
    rw [hto]
    rw [← hagree A hA ⟨σ, hσ⟩]
    exact (ha A hA ⟨σ, hσ⟩).symm
  · -- unramified outside the classes of `T` and of `Q`
    intro B hBfin hBnotT hBnotQ σ hσ hI
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := b) hσ]
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
  · -- `z` is the level-`K` Kummer cochain of `b`
    intro σ hσ
    rfl
  · -- the inverse uniformiser class at the escape prime
    obtain ⟨c, hc⟩ := exists_count_one_complement p Fact.out 𝔮 b hdiv
    refine ⟨b⁻¹ * c ^ p, ⟨𝔮, hQcomap, hc⟩, ?_⟩
    intro σ hσ _
    have hbu : b * (b⁻¹ * c ^ p) = c ^ p := by group
    rw [hbu]
    exact congrFun (nodeKummerCocharZMod_pow_eq_zero K ζ hζ hζK c) σ

end Work.SSGRoute.H9
