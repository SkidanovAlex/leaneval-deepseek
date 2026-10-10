import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Submission.NK.FrobeniusBridge.Core
import Submission.NK.ResidueFrob.isPrimitiveRoot_residue
import Submission.NK.ResidueFrob.map_eq_pow_of_primitiveRoot
import Submission.NK.ResidueFrob.residue_injective_on_torsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ResidueFrob

open scoped Pointwise Classical

set_option linter.unusedSectionVars false


/--
STRATEGY (for the prover). Let `C = NK.NeukirchUchida.placeCompletion A.1`, `R = placeCompletionIntegers A.1`
and `F̄ = IsLocalRing.ResidueField ↥R`. The natural map `ρ : 𝓞 L →+* R`, `x ↦ ⟨placeCompletionCoe A.1 (algebraMap ↥L K' x), _⟩`
has kernel `P.asIdeal` (use `NK.NeukirchUchida.comap_placeCompletionIntegers` and
`Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf` /
`NK.Reconstruct.primeOfLevel_spec`), so it induces an injection `i : 𝓞 L ⧸ P.asIdeal →+* F̄` whose image `F` is a
subfield of `F̄` with `Nat.card F = Nat.card (𝓞 L ⧸ P.asIdeal) =: N`.
Let `ζ₀ : K'` be a primitive `(N-1)`-st root of unity (exists since `IsSepClosure K K'` and `CharZero K'`).
Then `u ζ₀ = ζ₀^q` by `hroot`. Also `placeCompletionCoe A.1 ζ₀ ∈ ↥R`; let `ζ̄ = IsLocalRing.residue R _`.
The action of `u` on `F` is the residue action of `σ̂ := completionRingEquiv A.1.valuation u.toRingEquiv _`
(see `Submission.NeukirchUchida.Local.completionRingEquiv_coe`), and the induced map on `𝓞 L ⧸ P.asIdeal` is
`galRestrict ... (AlgEquiv.restrictNormalHom L u)`.
KEY: show `IsPrimitiveRoot ζ̄ (N-1)`, i.e. that `residue` is injective on the `(N-1)`-torsion. For this use
`rootOfUnity_eq_one_of_residue_eq_one` with `d = N-1` (or re-prove it inline): in the local ring `R`, if
`w^(N-1) = 1` and `residue w = 1` then `(w-1)*(1+w+...+w^(N-2)) = 0`, the second factor has residue
`(N-1 : F̄)` which is non-zero because it lies in the subfield `F` of `N` elements where `(N : F) = 0`, so it is
a unit. Hence `ζ̄` has order `N-1`, and since `F^×` is a cyclic group of order `N-1` (every `y ∈ F^×` satisfies
`y^(N-1) = 1` by Lagrange, and `{y | y^(N-1) = 1}` has `N-1` elements), `ζ̄` generates `F^×`. Therefore the
residue action of `u` on `F`, agreeing with `x ↦ x^q` on the generator `ζ̄`, is `x ↦ x^q`. Translating back
through the injection `i` gives exactly `frobAtLevel A L u` (i.e. `IsFrobAt P (restrictNormalHom L u)`), using
`hq` to identify `Nat.card (𝓞 K ⧸ (primeOf A.1 A.2).asIdeal)` with `q`.
-/
theorem frobAtLevel_of_primitiveRoot_action {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    {q : ℕ} (hq : q = Nat.card (NumberField.RingOfIntegers K ⧸
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal))
    (u : Gal(K'/K))
    (hu : u ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1)
    (hroot : ∀ ζ : K', IsPrimitiveRoot ζ
      (Nat.card (NumberField.RingOfIntegers ↥L ⧸ (NK.Reconstruct.primeOfLevel A.1 L
        (NK.Reconstruct.comap_level_ne_top A.2 L)).asIdeal) - 1) → u ζ = ζ ^ q) :
    NK.FrobeniusBridge.frobAtLevel A L u := by
  classical
  -- ## Setup
  let P : NK.Chebotarev.PrimeIdeal ↥L :=
    NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)
  have hP : A.1.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P :=
    NK.Reconstruct.primeOfLevel_spec A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)
  let N : ℕ := Nat.card (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal)
  -- ## `𝓞 L` sits inside the valuation ring `A.1`
  have hmem : ∀ x : NumberField.RingOfIntegers ↥L,
      algebraMap ↥L K' (algebraMap (NumberField.RingOfIntegers ↥L) ↥L x) ∈ A.1 := by
    intro x
    rw [← ValuationSubring.mem_comap, hP]
    exact Commons.RingTheory.Valuation.algebraMap_mem_valuationSubringAtPrime P x
  -- ## the maps `𝓞 L →+* 𝒪_A` and `𝓞 L →+* κ̄`
  let ρ' : NumberField.RingOfIntegers ↥L →+* ↥A.1 :=
    { toFun := fun x => ⟨algebraMap ↥L K' (algebraMap (NumberField.RingOfIntegers ↥L) ↥L x),
        hmem x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  let ρ : NumberField.RingOfIntegers ↥L →+* IsLocalRing.ResidueField ↥A.1 :=
    (IsLocalRing.residue ↥A.1).comp ρ'
  have hval : ∀ y : ↥L, A.1.valuation (algebraMap ↥L K' y) < 1 ↔ P.valuation ↥L y < 1 := by
    have hsub : (Valuation.comap (algebraMap ↥L K') A.1.valuation).valuationSubring =
        (P.valuation ↥L).valuationSubring := by
      rw [Commons.RingTheory.Valuation.valuationSubring_comap,
        ValuationSubring.valuationSubring_valuation]
      exact hP.trans
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring P)
    have heq : (Valuation.comap (algebraMap ↥L K') A.1.valuation).IsEquiv (P.valuation ↥L) :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
    intro y
    simpa [Valuation.comap_apply] using heq.lt_one_iff_lt_one (x := y)
  have hker : ∀ x : NumberField.RingOfIntegers ↥L, ρ x = 0 ↔ x ∈ P.asIdeal := by
    intro x
    change IsLocalRing.residue ↥A.1 (ρ' x) = 0 ↔ x ∈ P.asIdeal
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    change A.1.valuation (algebraMap ↥L K'
        (algebraMap (NumberField.RingOfIntegers ↥L) ↥L x)) < 1 ↔ x ∈ P.asIdeal
    rw [hval (algebraMap (NumberField.RingOfIntegers ↥L) ↥L x),
      IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  -- ## the induced injection `𝓞 L ⧸ P →+* κ̄`
  let i : (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) →+* IsLocalRing.ResidueField ↥A.1 :=
    Ideal.Quotient.lift P.asIdeal ρ (fun a ha => (hker a).mpr ha)
  have hi_mk : ∀ x : NumberField.RingOfIntegers ↥L,
      i (Ideal.Quotient.mk P.asIdeal x) = ρ x :=
    fun x => Ideal.Quotient.lift_mk P.asIdeal ρ (fun a ha => (hker a).mpr ha)
  have hi_inj : Function.Injective i := by
    intro y z hyz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hi_mk, hi_mk] at hyz
    rw [Ideal.Quotient.eq]
    exact (hker (a - b)).mp (by rw [map_sub, hyz, sub_self])
  -- ## `N` is the cardinality of the residue field of `L` at `P`
  haveI hmax : P.asIdeal.IsMaximal := inferInstance
  haveI hfin : Finite (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) := inferInstance
  haveI hfintype : Fintype (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) :=
    Fintype.ofFinite _
  have hNcard : N = Fintype.card (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) :=
    Nat.card_eq_fintype_card
  have hN2 : 2 ≤ N := by
    have h := Fintype.one_lt_card (α := NumberField.RingOfIntegers ↥L ⧸ P.asIdeal)
    omega
  have hNpos : 0 < N := by omega
  have hNcast : ((N : ℕ) : NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) = 0 := by
    rw [hNcard]
    exact Nat.cast_card_eq_zero _
  have hNm1 : ((N - 1 : ℕ) : NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) ≠ 0 := by
    intro h
    have hNsucc : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hNpos
    have h1 : ((N : ℕ) : NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) = 1 := by
      rw [← hNsucc, Nat.cast_add, Nat.cast_one, h, zero_add]
    rw [h1] at hNcast
    exact one_ne_zero hNcast
  -- ## `N - 1` is a unit of the local ring `𝒪_A`
  have hunit : IsUnit ((N - 1 : ℕ) : ↥A.1) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    rw [show ((N - 1 : ℕ) : ↥A.1) = ρ' ((N - 1 : ℕ) : NumberField.RingOfIntegers ↥L)
      from (map_natCast ρ' (N - 1)).symm]
    change ρ ((N - 1 : ℕ) : NumberField.RingOfIntegers ↥L) ≠ 0
    rw [← hi_mk ((N - 1 : ℕ) : NumberField.RingOfIntegers ↥L)]
    rw [← map_zero i]
    intro h
    exact hNm1 (by
      have h2 : Ideal.Quotient.mk P.asIdeal ((N - 1 : ℕ) : NumberField.RingOfIntegers ↥L) = 0 :=
        hi_inj (by rw [h, map_zero])
      rwa [map_natCast (Ideal.Quotient.mk P.asIdeal) (N - 1)] at h2)
  -- ## a primitive `(N-1)`-st root of unity in `K'`
  haveI hsep : IsSepClosed K' := IsSepClosure.sep_closed K
  have hinj_alg : Function.Injective (algebraMap K K') := by
    have hne : ∀ x : K, x ≠ 0 → algebraMap K K' x ≠ 0 := by
      intro x hx h0
      have h1 : algebraMap K K' x * algebraMap K K' x⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hx, map_one]
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    intro a b h
    rw [← sub_eq_zero]
    by_contra hab
    exact hne (a - b) hab (by rw [map_sub, h, sub_self])
  haveI hchar : CharZero K' := charZero_of_injective_algebraMap hinj_alg
  have hN1ne : N - 1 ≠ 0 := by omega
  haveI hNZ : NeZero (N - 1) := ⟨hN1ne⟩
  haveI hNZ' : NeZero ((N - 1 : ℕ) : K') :=
    ⟨fun h => hN1ne (CharZero.cast_injective (by rw [h]; simp))⟩
  obtain ⟨ζ, hζK⟩ : ∃ ζ : K', IsPrimitiveRoot ζ (N - 1) :=
    NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := K')
  have hζmem : ζ ∈ A.1 := by
    rcases ValuationSubring.mem_or_inv_mem A.1 ζ with h | h
    · exact h
    · have h1 : ζ ^ (N - 2) * ζ = 1 := by
        rw [← pow_succ, show N - 2 + 1 = N - 1 from by omega, hζK.pow_eq_one]
      have h2 : ζ = (ζ ^ (N - 2))⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : (ζ⁻¹) ^ (N - 2) = ζ := by
        rw [inv_pow ζ (N - 2)]
        exact h2.symm
      rw [← h3]
      exact pow_mem h _
  let ζA : ↥A.1 := ⟨ζ, hζmem⟩
  have hζA : IsPrimitiveRoot ζA (N - 1) := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζK
  have hζbar : IsPrimitiveRoot (IsLocalRing.residue ↥A.1 ζA) (N - 1) :=
    isPrimitiveRoot_residue hζA (fun w hw hres => residue_injective_on_torsion hunit hw hres)
  -- ## the action of `u` on `𝒪_A` and on its residue field
  have hstab : ∀ x : K', x ∈ A.1 ↔ u x ∈ A.1 :=
    (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubring_iff
      (F := K) (E := K') A.1 u).mp hu
  have hstab_inv : ∀ x : K', x ∈ A.1 ↔ u⁻¹ x ∈ A.1 :=
    (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubring_iff
      (F := K) (E := K') A.1 u⁻¹).mp (inv_mem hu)
  have huA : ∀ a : ↥A.1, u (a : K') ∈ A.1 := fun a => (hstab (a : K')).mp a.2
  have huAi : ∀ a : ↥A.1, u⁻¹ (a : K') ∈ A.1 := fun a => (hstab_inv (a : K')).mp a.2
  let uA : ↥A.1 →+* ↥A.1 :=
    { toFun := fun a => ⟨u (a : K'), huA a⟩
      map_one' := Subtype.ext (map_one u)
      map_mul' := fun a b => Subtype.ext (map_mul u _ _)
      map_zero' := Subtype.ext (map_zero u)
      map_add' := fun a b => Subtype.ext (map_add u _ _) }
  let uAi : ↥A.1 →+* ↥A.1 :=
    { toFun := fun a => ⟨u⁻¹ (a : K'), huAi a⟩
      map_one' := Subtype.ext (map_one u⁻¹)
      map_mul' := fun a b => Subtype.ext (map_mul u⁻¹ _ _)
      map_zero' := Subtype.ext (map_zero u⁻¹)
      map_add' := fun a b => Subtype.ext (map_add u⁻¹ _ _) }
  have huAi_uA : ∀ a : ↥A.1, uAi (uA a) = a := by
    intro a
    exact Subtype.ext (AlgEquiv.symm_apply_apply u (a : K'))
  have huA_uAi : ∀ a : ↥A.1, uA (uAi a) = a := by
    intro a
    exact Subtype.ext (AlgEquiv.apply_symm_apply u (a : K'))
  have huA_bij : Function.Bijective uA :=
    ⟨fun a b h => by
        have := congrArg uAi h
        simpa only [huAi_uA] using this,
      fun b => ⟨uAi b, huA_uAi b⟩⟩
  let uAe : ↥A.1 ≃+* ↥A.1 := RingEquiv.ofBijective uA huA_bij
  let φ : ↥A.1 →+* IsLocalRing.ResidueField ↥A.1 :=
    (IsLocalRing.residue ↥A.1).comp uAe.toRingHom
  have hφ_apply : ∀ a : ↥A.1, φ a = IsLocalRing.residue ↥A.1 (uAe a) := fun a => rfl
  have hφ_kill : ∀ a : ↥A.1, IsLocalRing.residue ↥A.1 a = 0 → φ a = 0 := by
    intro a ha
    have hnu : ¬ IsUnit a := by
      rw [← mem_nonunits_iff]
      exact (IsLocalRing.mem_maximalIdeal a).mp ((IsLocalRing.residue_eq_zero_iff a).mp ha)
    rw [hφ_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    have h2 : IsUnit (uAe.symm (uAe a)) := IsUnit.map (uAe.symm : ↥A.1 →+* ↥A.1) h
    rw [RingEquiv.symm_apply_apply] at h2
    exact hnu h2
  have hφ_ζ : φ ζA = (IsLocalRing.residue ↥A.1 ζA) ^ q := by
    have h3 : uAe ζA = ζA ^ q := by
      apply Subtype.ext
      exact hroot ζ hζK
    rw [hφ_apply, h3, map_pow]
  -- ## the identification of the exponent
  have hPeq : P = Submission.NeukirchUchida.Local.placeOf (Submission.NeukirchUchida.primeOf A.1 A.2)
      A.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2) L :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (hP.symm.trans (Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf
        (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
        (Submission.NeukirchUchida.primeOf_spec A.1 A.2) L))
  have hqnat : Nat.card (NumberField.RingOfIntegers K ⧸
      P.asIdeal.under (NumberField.RingOfIntegers K)) = q := by
    have hunder : P.asIdeal.under (NumberField.RingOfIntegers K) =
        (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal := by
      rw [hPeq]
      exact (Submission.NeukirchUchida.Local.placeOf_liesOver (Submission.NeukirchUchida.primeOf A.1 A.2)
        A.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2) L).over.symm
    rw [hunder, hq]
  have hqne : q ≠ 0 := by
    rw [hq]
    haveI : (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.IsMaximal := inferInstance
    haveI : Finite (NumberField.RingOfIntegers K ⧸
        (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) := inferInstance
    exact (Nat.card_pos (α := NumberField.RingOfIntegers K ⧸
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal)).ne'
  -- ## the action on the residue field of `L` at `P` is `x ↦ x ^ q`
  have hgal : ∀ x : NumberField.RingOfIntegers ↥L,
      ρ (galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L)
        (AlgEquiv.restrictNormalHom L u) x) = φ (ρ' x) := by
    intro x
    have h1 : ρ' (galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L)
        (AlgEquiv.restrictNormalHom L u) x) = uAe (ρ' x) := by
      apply Subtype.ext
      show algebraMap ↥L K' (algebraMap (NumberField.RingOfIntegers ↥L) ↥L
          (galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L)
            (AlgEquiv.restrictNormalHom L u) x)) =
        u (algebraMap ↥L K' (algebraMap (NumberField.RingOfIntegers ↥L) ↥L x))
      rw [algebraMap_galRestrict_apply,
        Submission.NeukirchUchida.Local.restrictNormalHom_apply_algebraMap]
    rw [show ρ (galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L)
        (AlgEquiv.restrictNormalHom L u) x) =
        IsLocalRing.residue ↥A.1 (ρ' (galRestrict (NumberField.RingOfIntegers K) K ↥L
          (NumberField.RingOfIntegers ↥L) (AlgEquiv.restrictNormalHom L u) x)) from rfl, h1]
    rfl
  -- ## the `(N-1)`-torsion of the residue field of `L` at `P` is fixed by the `q`-power action
  have hpowres : ∀ x : NumberField.RingOfIntegers ↥L, x ∉ P.asIdeal → (ρ x) ^ (N - 1) = 1 := by
    intro x hx
    have hx0 : Ideal.Quotient.mk P.asIdeal x ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    have hpow : (Ideal.Quotient.mk P.asIdeal x) ^ (N - 1) = 1 := by
      have h := @FiniteField.pow_card_sub_one_eq_one _ (Ideal.Quotient.groupWithZero P.asIdeal) _
        (Ideal.Quotient.mk P.asIdeal x) hx0
      rwa [← hNcard] at h
    have hmemP : x ^ (N - 1) - 1 ∈ P.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, hpow, sub_self]
    have h := (hker (x ^ (N - 1) - 1)).mpr hmemP
    rwa [map_sub, map_pow, map_one, sub_eq_zero] at h
  -- ## conclusion
  rw [NK.FrobeniusBridge.frobAtLevel_def, NK.Chebotarev.isFrobAt_def]
  intro x
  rw [hqnat]
  refine (hker (galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L)
    (AlgEquiv.restrictNormalHom L u) x - x ^ q)).mp ?_
  rw [map_sub, map_pow, hgal x]
  by_cases hx : x ∈ P.asIdeal
  · rw [hφ_kill (ρ' x) (by change ρ x = 0; exact (hker x).mpr hx), (hker x).mpr hx,
      zero_pow hqne, sub_zero]
  · rw [map_eq_pow_of_primitiveRoot φ hφ_kill hζbar hφ_ζ (hpowres x hx)]
    rw [show (IsLocalRing.residue ↥A.1 (ρ' x)) = ρ x from rfl]
    exact sub_self _

end NK.ResidueFrob
