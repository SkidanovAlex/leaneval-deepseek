import Mathlib
import Submission.Work.SSGRoute.InertiaArithImports
import Submission.Work.SSGRoute.fixes_rootsOfUnity_of_isInertia
import Submission.Work.SSGRoute.fixes_rootsOfUnity_of_localInertia
import Submission.Work.SSGRoute.finite_card_residueField_comap_bot
import Submission.Work.SSGRoute.pow_exists_eq_one_of_isIntegral_finite_base_pow
import Submission.NK.RamificationAudit.perfectField_residueField_comap
import Submission.Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia subgroup of a finite place: global versus local

For a finite place `A` of a separable closure `Ω` of a number field `K`, the *global* inertia
condition `SSGRoute.IsInertia K A.1 σ` (the element `σ` of the decomposition group acts trivially
on the residue field of `A`) is equivalent, under the local/global identification
`NK.FrobeniusBridge.localGaloisEquiv A : D_A ≃* Gal(κ̄/κ)`, to membership of the image of `σ` in
the *local* inertia subgroup `NK.LocalAnabelian.inertiaSubgroup p ≤ Gal(κ̄/κ)` (the fixing subgroup
of the prime-to-`p` roots of unity of `κ̄`), where `p` is the residue characteristic
`NK.TameStructureDeep.Tame.resCharAt (primeOf A.1 A.2)`.

The two directions are proved separately:

* `σ ∈ I_A → localGaloisEquiv A σ ∈ I_κ` (`→`): an inertia element acts trivially on the residue
  field of `A`, hence fixes every root of unity of `Ω` of prime-to-`p` order
  (`Work.SSGRoute.fixes_rootsOfUnity_of_isInertia`, using the hypothesis `hunit` that integers
  prime to `p` are units of `↥A.1`), and fixing the prime-to-`p` roots of unity of `Ω` puts the
  local image in `I_κ` (`NK.ResidueFrob.mem_inertiaSubgroup_of_fixes_rootsOfUnity`).

* `localGaloisEquiv A σ ∈ I_κ → σ ∈ I_A` (`←`): a local inertia element fixes the prime-to-`p`
  roots of unity of `Ω` (`Work.SSGRoute.fixes_rootsOfUnity_of_localInertia`), and an element
  fixing those acts trivially on the residue field of `A`
  (`Work.SSGRoute.isInertia_of_fixes_rootsOfUnity_general` below, using `hunit` and the fact that
  every element of the residue field is `0` or a root of unity of prime-to-`p` order,
  `Work.SSGRoute.residueField_residue_pow_eq_one_general_aux`).
-/

namespace Work.SSGRoute

set_option linter.style.haveILetI false

/-- **The residue field of the prime of `K` below a finite place `A` of `Ω`**, pulled back to the
copy `⊥ ≤ ↥L` of `K`: it is finite and of cardinality a positive power `p ^ f` of the residue
characteristic `p = resCharAt (primeOf A.1 A.2)`.

This is the general-number-field form of `Work.SSGRoute.finite_card_residueField_comap_bot`: the
residue field is computed as `𝓞 K ⧸ (primeOf A.1 A.2).asIdeal` through
`Work.SSGRoute.residueField_comap_bot_ringEquiv` and
`Work.SSGRoute.residueField_valuationSubringAtPrime_ringEquiv`, and the `p ^ f` statement is
`NK.TameStructureDeep.Tame.q_eq_of_charP`. -/
private theorem card_residueField_comap_bot_bot {K : Type} [Field K] [NumberField K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (A : NK.FrobeniusBridge.FinitePlaceOf K Ω) (L : IntermediateField K Ω) [FiniteDimensional K L] :
    Finite (IsLocalRing.ResidueField
        ↥((A.1.comap (algebraMap ↥L Ω)).comap (algebraMap ↥(⊥ : IntermediateField K ↥L) ↥L))) ∧
      ∃ f : ℕ, 0 < f ∧ Nat.card (IsLocalRing.ResidueField
        ↥((A.1.comap (algebraMap ↥L Ω)).comap (algebraMap ↥(⊥ : IntermediateField K ↥L) ↥L)))
        = (NK.TameStructureDeep.Tame.resCharAt
            (Submission.NeukirchUchida.primeOf A.1 A.2)) ^ f := by
  classical
  set 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    Submission.NeukirchUchida.primeOf A.1 A.2 with h𝔭
  obtain ⟨e1⟩ := residueField_comap_bot_ringEquiv (F := K) (E := ↥L)
    (V := A.1.comap (algebraMap ↥L Ω))
  have hcomap : (A.1.comap (algebraMap ↥L Ω)).comap (algebraMap K ↥L)
      = A.1.comap (algebraMap K Ω) := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq K ↥L Ω]
  have hprime : A.1.comap (algebraMap K Ω)
      = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 := by
    rw [h𝔭]
    exact Submission.NeukirchUchida.primeOf_spec A.1 A.2
  obtain ⟨e2⟩ := residueField_valuationSubringAtPrime_ringEquiv (K := K) 𝔭
  have e : IsLocalRing.ResidueField
        ↥((A.1.comap (algebraMap ↥L Ω)).comap (algebraMap ↥(⊥ : IntermediateField K ↥L) ↥L))
      ≃+* (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) :=
    ((hcomap.trans hprime) ▸ e1).trans e2
  have hcard : Nat.card (IsLocalRing.ResidueField
        ↥((A.1.comap (algebraMap ↥L Ω)).comap (algebraMap ↥(⊥ : IntermediateField K ↥L) ↥L)))
      = NK.LocalStructure.residueCard K 𝔭 := by
    rw [Nat.card_congr e.toEquiv]
    have h1 : Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) = Ideal.absNorm 𝔭.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h1]
    exact (Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm 𝔭).symm
  refine ⟨?_, ?_⟩
  · haveI : Finite (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum 𝔭
    exact Finite.of_equiv (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) e.symm
  · obtain ⟨f, hf, hfpow⟩ := NK.TameStructureDeep.q_eq_of_charP 𝔭
      (NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭)
      (NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭)
    exact ⟨f, hf, hcard.trans hfpow⟩

/-- **Every element of the residue field of a finite place of `Ω` over a number field `K` is `0`
or a root of unity of order prime to the residue characteristic.**

This is the general-number-field form of `Work.SSGRoute.residueField_residue_pow_eq_one_clean`: with
`L = K⟮a⟯`, `B = A.1.comap (algebraMap ↥L Ω)` and `F₀` the residue field of the prime of `K` below
`A`, the residue of `a` in `↥A.1` is integral over `F₀`
(`NK.RamificationAudit.exists_monic_aeval_eq_zero_natDegree_le`), and `F₀` is a finite field of
cardinality `p ^ f` (`card_residueField_comap_bot_bot`), so that the integrality statement
`Work.SSGRoute.pow_exists_eq_one_of_isIntegral_finite_base_pow` applies. -/
private theorem residueField_residue_pow_eq_one_general_aux {K : Type} [Field K] [NumberField K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (A : NK.FrobeniusBridge.FinitePlaceOf K Ω) (p : ℕ)
    (hp : p = NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2))
    (a : ↥A.1) :
    IsLocalRing.residue ↥A.1 a = 0 ∨
      ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (IsLocalRing.residue ↥A.1 a) ^ N = 1 := by
  by_cases hx : IsLocalRing.residue ↥A.1 a = 0
  · exact Or.inl hx
  · right
    let L : IntermediateField K Ω := IntermediateField.adjoin K ({(a : Ω)} : Set Ω)
    haveI hLfd : FiniteDimensional K L :=
      IntermediateField.adjoin.finiteDimensional
        ((Algebra.IsAlgebraic.isAlgebraic (a : Ω)).isIntegral)
    let B : ValuationSubring ↥L := A.1.comap (algebraMap ↥L Ω)
    have haL : (a : Ω) ∈ L := IntermediateField.mem_adjoin_simple_self K (a : Ω)
    let y : ↥B := ⟨⟨(a : Ω), haL⟩, by
      show algebraMap ↥L Ω ⟨(a : Ω), haL⟩ ∈ A.1
      simpa using a.2⟩
    have hcomapy : NK.RamificationAudit.comapToA A.1 L y = a := by
      ext
      simp [y, NK.RamificationAudit.comapToA]
    obtain ⟨f, hfmonic, _hfdeg, hf⟩ :=
      NK.RamificationAudit.exists_monic_aeval_eq_zero_natDegree_le B (⊥ : IntermediateField K ↥L)
        (IsLocalRing.residue ↥B y)
    let ψ : IsLocalRing.ResidueField ↥B →+* IsLocalRing.ResidueField ↥A.1 :=
      IsLocalRing.ResidueField.map (NK.RamificationAudit.comapToA A.1 L)
    let F0 := IsLocalRing.ResidueField ↥(B.comap (algebraMap ↥(⊥ : IntermediateField K ↥L) ↥L))
    letI : Algebra F0 (IsLocalRing.ResidueField ↥A.1) :=
      (ψ.comp (algebraMap F0 (IsLocalRing.ResidueField ↥B))).toAlgebra
    have hxψ : ψ (IsLocalRing.residue ↥B y) = IsLocalRing.residue ↥A.1 a := by
      rw [IsLocalRing.ResidueField.map_residue, hcomapy]
    have hzint : IsIntegral F0 (IsLocalRing.residue ↥B y) := ⟨f, hfmonic, hf⟩
    have hcompat : (algebraMap F0 (IsLocalRing.ResidueField ↥A.1)).comp (RingHom.id F0) =
        ψ.comp (algebraMap F0 (IsLocalRing.ResidueField ↥B)) := by
      ext z
      rfl
    have hint : IsIntegral F0 (IsLocalRing.residue ↥A.1 a) := by
      rw [← hxψ]
      exact IsIntegral.map_of_comp_eq (RingHom.id F0) ψ hcompat hzint
    obtain ⟨hFin, f', hf'pos, hcard⟩ := card_residueField_comap_bot_bot A L
    haveI : Finite F0 := hFin
    obtain ⟨N, hNpos, hNp, hNpow⟩ :=
      pow_exists_eq_one_of_isIntegral_finite_base_pow
        (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2))
        f' hf'pos hcard hx hint
    exact ⟨N, hNpos, by rwa [hp], hNpow⟩

/-- **Fixing the prime-to-`p` roots of unity of `Ω` forces the global inertia condition.**

Let `K` be a number field, `Ω` a separable closure of `K`, `A` a finite place of `Ω` over `K`,
`p` its residue characteristic, and assume that every integer prime to `p` is a unit of the
valuation ring `↥A.1`.  Then an element `σ` of the decomposition group of `A` fixing every root of
unity of `Ω` of order prime to `p` acts trivially on the residue field of `A`.

The residue field of `A` is the algebraic closure `𝔽̄_p` of `𝔽_p`
(`residueField_residue_pow_eq_one_general_aux`), so its elements are the residues of roots of unity
of prime-to-`p` order: for `b : ↥A.1` whose residue is nonzero there is `N > 0` with `p ∤ N` and
`(residue b)^N = 1`, a primitive `N`-th root of unity `ζ₀` of `Ω` lies in `A.1`, `N` is a unit of
`A.1` so reduction is injective on the `N`-torsion, and `σ` fixes `ζ₀`, hence its residue. -/
theorem isInertia_of_fixes_rootsOfUnity_general {K : Type} [Field K] [NumberField K] {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (A : NK.FrobeniusBridge.FinitePlaceOf K Ω) (p : ℕ)
    (hp : p = NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2))
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : ↥A.1))
    (σ : ↥(SSGRoute.decomp K A.1))
    (hfix : ∀ (n : ℕ), ¬ p ∣ n → ∀ ζ : Ω, IsPrimitiveRoot ζ n → (σ : Ω ≃ₐ[K] Ω) ζ = ζ) :
    SSGRoute.IsInertia K A.1 (σ : Ω ≃ₐ[K] Ω) := by
  haveI : CharZero Ω :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K Ω)
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  refine ⟨σ.property, ?_⟩
  intro x hx
  let g : ↥(A.1.decompositionSubgroup K) := ⟨σ, σ.property⟩
  have hfixres : ∀ b : ↥A.1,
      IsLocalRing.residue ↥A.1 (g • b) = IsLocalRing.residue ↥A.1 b := by
    intro b
    rw [IsLocalRing.ResidueField.residue_smul]
    rcases residueField_residue_pow_eq_one_general_aux A p hp b with
      h0 | ⟨N, hNpos, hNp, hNpow⟩
    · rw [h0, smul_zero]
    · haveI : NeZero N := ⟨hNpos.ne'⟩
      obtain ⟨ζ₀, hζ₀⟩ :=
        NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := Ω) (n := N)
      have hζ₀mem : ζ₀ ∈ A.1 :=
        NK.TameStructureDeep.Tame.mem_valuationSubring_of_isPrimitiveRoot A.1 hζ₀ hNpos.ne'
      let ζ₀A : ↥A.1 := ⟨ζ₀, hζ₀mem⟩
      have hζ₀A : IsPrimitiveRoot ζ₀A N :=
        (IsPrimitiveRoot.coe_submonoidClass_iff (N := A.1) (ζ := ζ₀A)).mp hζ₀
      have hunitN : IsUnit (N : ↥A.1) := hunit N hNp
      have hη : IsPrimitiveRoot (IsLocalRing.residue ↥A.1 ζ₀A) N :=
        NK.ResidueFrob.isPrimitiveRoot_residue hζ₀A
          (fun w hw hresw => NK.ResidueFrob.residue_injective_on_torsion hunitN hw hresw)
      obtain ⟨j, -, hj⟩ := hη.eq_pow_of_pow_eq_one hNpow
      have hgζ : g • ζ₀A = ζ₀A := by
        apply Subtype.ext
        rw [NK.Ramification.coe_smul]
        exact hfix N hNp ζ₀ hζ₀
      rw [← hj]
      calc (MulSemiringAction.toRingEquiv ↥(A.1.decompositionSubgroup K)
              (IsLocalRing.ResidueField ↥A.1)) g ((IsLocalRing.residue ↥A.1) ζ₀A ^ j)
          = (MulSemiringAction.toRingEquiv ↥(A.1.decompositionSubgroup K)
              (IsLocalRing.ResidueField ↥A.1)) g ((IsLocalRing.residue ↥A.1) ζ₀A) ^ j := by
            rw [map_pow]
        _ = ((IsLocalRing.residue ↥A.1) (g • ζ₀A)) ^ j := by
            rw [MulSemiringAction.toRingEquiv_apply_apply,
              ← IsLocalRing.ResidueField.residue_smul ↥(A.1.decompositionSubgroup K) g ζ₀A]
        _ = ((IsLocalRing.residue ↥A.1) ζ₀A) ^ j := by rw [hgζ]
  let w : ↥A.1 := g • (⟨x, hx⟩ : ↥A.1) - ⟨x, hx⟩
  have hmem : w ∈ IsLocalRing.maximalIdeal ↥A.1 := by
    change g • (⟨x, hx⟩ : ↥A.1) - ⟨x, hx⟩ ∈ IsLocalRing.maximalIdeal ↥A.1
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hfixres, sub_self]
  have hlt : A.1.valuation (w : Ω) < 1 :=
    (ValuationSubring.valuation_lt_one_iff A.1 w).mp hmem
  simpa [w, NK.Ramification.coe_smul] using hlt

theorem mem_localInertia_iff_isInertia {K : Type} [Field K] [NumberField K] {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (A : NK.FrobeniusBridge.FinitePlaceOf K Ω)
    (hunit : ∀ n : ℕ, ¬ (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2)) ∣ n →
      IsUnit (n : ↥A.1))
    (σ : ↥(SSGRoute.decomp K A.1)) :
    SSGRoute.IsInertia K A.1 (σ : Ω ≃ₐ[K] Ω) ↔
      NK.FrobeniusBridge.localGaloisEquiv A σ ∈
        NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField A)
          (K' := NK.FrobeniusBridge.localClosure A)
          (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2)) := by
  set p := NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2) with hp
  set q := NK.LocalStructure.residueCard K (Submission.NeukirchUchida.primeOf A.1 A.2) with hq
  have hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A) :=
    NK.TameData.TameDataInput.toTameData
      (NK.TameStructureDeep.Tame.tameDataInput_adicCompletion_residueChar
        (Submission.NeukirchUchida.primeOf A.1 A.2))
  constructor
  · intro h
    refine NK.ResidueFrob.mem_inertiaSubgroup_of_fixes_rootsOfUnity A hT σ.property ?_
    rintro ζ ⟨n, hpn, hζp⟩
    exact fixes_rootsOfUnity_of_isInertia A hunit σ h n hpn ζ hζp
  · intro h
    have hfix : ∀ (n : ℕ), ¬ p ∣ n → ∀ ζ : Ω, IsPrimitiveRoot ζ n →
        (σ : Ω ≃ₐ[K] Ω) ζ = ζ :=
      fixes_rootsOfUnity_of_localInertia K Ω A.1 A.2 p q hT σ.1 σ.property h
    exact isInertia_of_fixes_rootsOfUnity_general A p hp hunit σ hfix

end Work.SSGRoute
