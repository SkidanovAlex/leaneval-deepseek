import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.dvd_ramificationIdx_of_val_log_notMem_pow
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.exists_pow_mul_mem_localUnits_of_dvd_log
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt
import Submission.Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple
import Submission.Work.SSGRoute.ZSplit.BaseChange
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Kummer characters vanishing on the inertia are locally unramified

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K/k` a finite Galois level, `p` a prime,
`ζ ∈ K` a primitive `p`-th root of unity and `β ∈ Kˣ`.  For a finite place `A` of `Ω` over the prime
`𝔭` of `K`, the global Kummer character `χ_β` of `β`
(`Work.SSGRoute.kummerCharZMod`) is the `ZMod p`-valued function
`σ ↦ σ(√[p]β)/√[p]β` on `Gal(Ω/K)`.

The lemma proved here is the *unramified half* of the local Kummer dictionary: if `χ_β` kills the
inertia subgroup of `A` inside `Gal(Ω/K)`, then the image of `β` in the completion `K_𝔭` is a `p`-th
power times a local unit,

`Units.map (algebraMap K K_𝔭) β = γ ^ p * u`,   `u ∈ 𝒪_𝔭ˣ`.

Equivalently: the Kummer extension `K(β^{1/p})/K` is unramified at `𝔭`, so the `𝔭`-adic valuation of
`β` is divisible by `p`, and `β` is a uniformizer power times a unit.

## Proof

* If `p ∤ v_𝔭(β)`, then `β` is not a `p`-th power in `K`, so the Kummer field
  `N = K(β^{1/p})` is Galois of degree `p` over `K`.  Writing `β' = √[p]β ∈ N`, the identity
  `v_𝔭(β)^e = v_P(β')^p` for a prime `P | 𝔭` forces `p ∣ e = e(P/𝔭)`
  (`dvd_ramificationIdx_of_val_log_notMem_pow`), whence the inertia subgroup of `Gal(N/K)` at `P`
  is non-trivial (`inertia_eq_bot_iff_ramificationIdx_eq_one`).
* An element `τ ≠ 1` of that level inertia lifts to an inertia element `σ₁` of the place inertia of
  `A` over `K` (`inertiaSub_image_eq_levelInertia`); since `N = K⟮√[p]β⟯`, `σ₁` moves the root, i.e.
  `χ_β(σ₁) ≠ 0` (`kummerCharZMod_eq_zero_iff_apply_sqrt`).
* Transporting `σ₁` to `G_k` (`σ₁.restrictScalars k ∈ K.fixingSubgroup`, and `IsInertia` over `K`
  is `IsInertia` over `k` for such an element, `isInertia_baseChange`) contradicts the hypothesis.
* So `p ∣ v_𝔭(β)`, and `exists_pow_mul_mem_localUnits_of_dvd_log` produces `γ` and `u`.
-/

namespace Work.SSGRoute.ZDataMup.LocalUnramified

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The inertia condition is base-change invariant.**  For `σ ∈ Gal(Ω/↥K)` and a place `A` of `Ω`,
`σ` is an inertia element of `A` over `↥K` if and only if its restriction to a `k`-algebra
automorphism is an inertia element of `A` over `k`.  This is
`Work.SSGRoute.isInertia_baseChange` read through `IntermediateField.fixingSubgroupEquiv` (the two
maps have the same underlying function). -/
theorem isInertia_restrictScalars_iff (K : IntermediateField k Ω) [FiniteDimensional k K]
    (A : ValuationSubring Ω)
    (σ : Ω ≃ₐ[↥K] Ω) :
    SSGRoute.IsInertia k A (σ.restrictScalars k) ↔ SSGRoute.IsInertia ↥K A σ := by
  have hσK : σ.restrictScalars k ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  have heq : (IntermediateField.fixingSubgroupEquiv K) ⟨σ.restrictScalars k, hσK⟩ = σ := by
    ext x
    rfl
  rw [← heq]
  exact Work.SSGRoute.isInertia_baseChange k Ω K A (σ.restrictScalars k) hσK

/-- **Kummer characters vanishing on the inertia are locally unramified.**  If the global Kummer
character of `β ∈ Kˣ` vanishes on the inertia subgroup of the finite place `A` inside
`Gal(Ω/K)`, then the image of `β` in the completion `K_𝔭` is a `p`-th power times a local unit. -/
theorem kummerChar_zero_on_inertia_imp_mem_unramified
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (β : Kˣ)
    (h : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k A σ →
        Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) = 0) :
    ∃ (γ : (𝔭.adicCompletion ↥K)ˣ) (u : (𝔭.adicCompletion ↥K)ˣ),
      u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) ∧
      Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)) β = γ ^ p * u := by
  classical
  -- The `𝔭`-adic valuation of `β` is divisible by `p`; this is the whole arithmetic content.
  have hdvd : (p : ℤ) ∣ (𝔭.valuation ↥K (β : ↥K)).log := by
    by_contra hndvd
    -- `A` is a finite place over the number field `↥K`
    haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    haveI hSepK : IsSepClosure ↥K Ω := ⟨inferInstance, inferInstance⟩
    have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := NK.Reconstruct.comap_level_ne_top hA K
    -- Step 1: `β` is not a `p`-th power in `↥K`
    have hβnot : β ∉ NK.LocalAnabelian.powSubgroup p ↥K := by
      rintro ⟨d, hd⟩
      refine hndvd ⟨(𝔭.valuation ↥K (d : ↥K)).log, ?_⟩
      have hd' : (d : ↥K) ^ p = (β : ↥K) := by
        simpa using congrArg (fun u : (↥K)ˣ => (u : ↥K)) hd
      rw [← hd', map_pow, WithZero.log_pow, nsmul_eq_mul]
    -- Step 2: the Kummer field `N = ↥K⟮α⟯` of a chosen `p`-th root `α` of `β`
    set α : Ω := Work.SSGRoute.kummerSqrtZMod (Ω := Ω) (K := ↥K) p β with hαdef
    have hα : α ^ p = algebraMap ↥K Ω (β : ↥K) :=
      Work.SSGRoute.kummerSqrtZMod_pow (Ω := Ω) (K := ↥K) p β
    set N : IntermediateField ↥K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p β with hNdef
    haveI hgalN : IsGalois ↥K ↥N :=
      (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) p Fact.out hζ β
        hβnot).1
    haveI hfdN : FiniteDimensional ↥K ↥N :=
      NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (K' := Ω) (k := ↥K)
        (p := p) Fact.out hζ β
    haveI hnfN : NumberField ↥N :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField N
    have hNgen : N = IntermediateField.adjoin ↥K ({α} : Set Ω) := by
      rw [hNdef]
      exact NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p Fact.out hζ β hα
    have hαN : α ∈ N := by
      rw [hNgen]
      exact IntermediateField.mem_adjoin_simple_self ↥K α
    -- Step 3: the prime `P` of `𝓞 ↥N` below `A`, lying over `𝔭`
    set AF : NK.FrobeniusBridge.FinitePlaceOf ↥K Ω := ⟨A, hAK⟩ with hAFdef
    set P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥N) :=
      Work.SSGRoute.levelPrime ↥K Ω A hAK N with hPdef
    have hprimeOf : Submission.NeukirchUchida.primeOf AF.1 AF.2 = 𝔭 :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K) (by
        rw [← Submission.NeukirchUchida.primeOf_spec AF.1 AF.2]
        exact h𝔭)
    have hLies : P.asIdeal.LiesOver 𝔭.asIdeal := by
      have h := NK.ResidueFrob.primeOfLevel_liesOver (K := ↥K) (K' := Ω) AF N
      rw [hprimeOf] at h
      simpa only [hPdef, Work.SSGRoute.levelPrime] using h
    -- Step 4: `p` divides the ramification index of `P` over `𝔭`
    have hpP : p ∣ P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) := by
      haveI hLiesI := hLies
      have hβN : (⟨α, hαN⟩ : ↥N) ^ p = algebraMap ↥K ↥N (β : ↥K) := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_pow]
        change α ^ p = algebraMap ↥K Ω (β : ↥K)
        exact hα
      exact dvd_ramificationIdx_of_val_log_notMem_pow ↥K ↥N p Fact.out β ⟨α, hαN⟩ hβN 𝔭 P hndvd
    -- Step 5: the level inertia at `P` is non-trivial
    haveI h𝔭prime : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
    haveI hPprime : P.asIdeal.IsPrime := P.isPrime
    have he_ne : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K) ≠ 1 := by
      intro h1
      rw [h1] at hpP
      exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hpP)
    have hbot : Ideal.inertia (↥N ≃ₐ[↥K] ↥N) P.asIdeal ≠ ⊥ := fun hb =>
      he_ne ((Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
        𝔭.asIdeal P.asIdeal).mp hb)
    obtain ⟨τ, hτmem, hτne⟩ : ∃ τ : ↥N ≃ₐ[↥K] ↥N,
        τ ∈ Ideal.inertia (↥N ≃ₐ[↥K] ↥N) P.asIdeal ∧ τ ≠ 1 := by
      by_contra hcon
      apply hbot
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    -- Step 6: lift `τ` to an inertia element `σ₁` of the place `A` over `↥K`
    have hmap := Work.SSGRoute.inertiaSub_image_eq_levelInertia ↥K Ω A hAK N
    have hτmem' : τ ∈ (Work.SSGRoute.inertiaSub ↥K Ω A).map (AlgEquiv.restrictNormalHom N) := by
      rw [hmap]
      exact hτmem
    obtain ⟨σ₁, hσ₁mem, hσ₁res⟩ := Subgroup.mem_map.mp hτmem'
    -- Step 7: `σ₁` moves the chosen `p`-th root `α` of `β`
    have hσ₁α : σ₁ α ≠ α := by
      intro hfixα
      have hσ₁fix : σ₁ ∈ N.fixingSubgroup := by
        rw [hNgen]
        exact Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple α σ₁ hfixα
      have h1 : AlgEquiv.restrictNormalHom N σ₁ = 1 := by
        rw [show AlgEquiv.restrictNormalHom N σ₁ = σ₁.restrictNormal ↥N from rfl,
          AlgEquiv.restrictNormal_eq_one_iff]
        exact fun y hy => (IntermediateField.mem_fixingSubgroup_iff N σ₁).mp hσ₁fix y hy
      rw [h1] at hσ₁res
      exact hτne hσ₁res.symm
    -- Step 8: hence the Kummer character of `β` does not vanish at `σ₁`
    have hχ : Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β σ₁ ≠ 0 := by
      intro h0
      exact hσ₁α
        ((kummerCharZMod_eq_zero_iff_apply_sqrt (K := ↥K) p hζ β σ₁).mp h0)
    -- Step 9: transport `σ₁` to `G_k` and contradict the hypothesis
    have hσ₁K : σ₁.restrictScalars k ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ₁.commutes ⟨x, hx⟩
    have hInertia : SSGRoute.IsInertia k A (σ₁.restrictScalars k) :=
      (isInertia_restrictScalars_iff K A σ₁).mpr
        ((Work.SSGRoute.mem_inertiaSub ↥K Ω A σ₁).mp hσ₁mem)
    have heq : (IntermediateField.fixingSubgroupEquiv K) ⟨σ₁.restrictScalars k, hσ₁K⟩ = σ₁ := by
      ext x
      rfl
    have h0 := h (σ₁.restrictScalars k) hσ₁K hInertia
    rw [heq] at h0
    exact hχ h0
  exact exists_pow_mul_mem_localUnits_of_dvd_log 𝔭 p Fact.out β hdvd

end Work.SSGRoute.ZDataMup.LocalUnramified
