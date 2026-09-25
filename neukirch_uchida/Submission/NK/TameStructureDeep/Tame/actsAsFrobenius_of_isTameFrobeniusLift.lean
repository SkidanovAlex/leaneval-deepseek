import Mathlib
import Submission.NK.TameStructureDeep.Tame.CorrectedInterface
import Submission.NK.TameStructureDeep.Tame.exists_smul_root_of_notMem_unramifiedClosure
import Submission.NK.TameStructureDeep.Tame.exists_smul_root_of_notMem_unramifiedClosure_odd_prime_pow
import Submission.NK.TameStructureDeep.Tame.kummer_tateTwist_of_pow_eq
import Submission.NK.TameStructureDeep.Tame.irreducible_X_pow_sub_C_unramifiedClosure_odd
import Submission.NK.TameStructureDeep.Tame.layerDegree
import Submission.NK.TameStructureDeep.Tame.exists_kummerLayer_of_mem_tameClosure
import Submission.NK.TameStructureDeep.Tame.exists_root_primeToPart
import Submission.NK.TameStructureDeep.Support.mem_unramifiedClosure_of_isPrimitiveRoot
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.LocalTame.All
import Submission.NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure

/-!
# The converse direction of the Frobenius normalisation for the corrected wild inertia

`NK.TameStructureDeep.Tame.isTameFrobeniusLift_correctedWildInertia` proves the `⟹` direction of
NSW (12.1.8) for the *corrected* wild inertia `V_κ = Gal(K'/κ^{tr})`: a Frobenius element
(`NK.LocalAnabelian.IsFrobeniusFor p q F`) is a tame Frobenius lift,
`NK.LocalTame.IsTameFrobeniusLift q V_κ I_κ F`.

This file proves the converse, which is the direction the local structure theorem consumes:
if `F ∈ Gal(K'/κ)` lies outside the inertia subgroup `I_κ = Gal(K'/κ^{ur})` and conjugates the
tame inertia `I_κ/V_κ` by the `q`-th power map, then `F` acts on the roots of unity of order
prime to `p` by `ζ ↦ ζ^q`, i.e. `F` is a Frobenius element for the residue cardinality `q`.

The proof is the Tate twist read through the Kummer pairing.  Fix `n` prime to `p` and an `n`-th
root `β` of a uniformiser `π` of `κ`.  The Kummer pairing
`σ ↦ σ β / β : I_κ → μ_n` is *onto* `μ_n`, because `[κ^{ur}(β) : κ^{ur}] = n`
(`NK.TameStructureDeep.Tame.finrank_adjoin_urCl`), so every primitive `n`-th root of unity `ζ`
is `σβ/β` for some `σ ∈ I_κ`.  For such `σ` the hypothesis `F σ F⁻¹ (σ^q)⁻¹ ∈ V_κ` together with
`β ∈ κ^{tr}` gives
  `(F σ F⁻¹) β = (σ^q) β = ζ^q β`,
while a direct computation (both `F⁻¹β/β` and `σβ/β` lie in `κ^{ur}`, hence are fixed by the
relevant elements) gives
  `(F σ F⁻¹) β = F ζ · β`.
Comparing and cancelling `β` yields `F ζ = ζ^q`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Classical
open IntermediateField Polynomial

namespace NK.TameStructureDeep.Tame

noncomputable section

/-- **The Kummer pairing over `κ^{ur}` is onto `μ_n`, for every `n` prime to `p`.**

For a uniformiser `π` of `κ = K_𝔭`, `n` prime to the residue characteristic and `β ∈ K'` with
`β ^ n = π`, every `n`-th root of unity `ζ` is the Kummer character of an element of the inertia
subgroup: there is `σ ∈ Gal(K'/κ^{ur})` with `σ β = ζ β`.

The point is that `κ^{ur}(β)` has degree exactly `n` over `κ^{ur}`
(`NK.TameStructureDeep.Tame.finrank_adjoin_urCl`), so `X ^ n - C π` is the minimal polynomial
of `β`, every `ζ β` is a conjugate root of `β`, and normality of `K'/κ^{ur}` realises conjugate
roots by automorphisms.  This is the general-`n` form of
`NK.TameStructureDeep.Tame.exists_smul_root_of_notMem_unramifiedClosure` (prime `ℓ`) and
`…_odd_prime_pow` (odd prime powers); unlike those it needs no Capelli condition, the degree
statement being available. -/
theorem exists_smul_root_of_coprime {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    {n : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n (resCharAt 𝔭))
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) {β : K'}
    (hβ : β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
    {ζ : K'} (hζ : ζ ^ n = 1) :
    ∃ σ : Gal(K'/𝔭.adicCompletion K),
      σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭)).fixingSubgroup ∧ σ β = ζ * β := by
  classical
  set L : IntermediateField (𝔭.adicCompletion K) K' :=
    NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) with hL
  haveI : CharZero (𝔭.adicCompletion K) := Algebra.charZero_of_charZero K _
  haveI : CharZero K' := charZero_of_algebra_adicCompletion 𝔭
  haveI : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  set a : ↥L := uniformizerInClosure 𝔭 (K' := K') π with ha
  have hβa : β ^ n = algebraMap ↥L K' a := by
    rw [hβ]; simp [ha, uniformizerInClosure]
  have hane : a ≠ 0 := by
    intro h
    have hirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
    apply hirr.ne_zero
    apply Subtype.ext
    have h1 : algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) = 0 := by
      have := congrArg (algebraMap ↥L K') h
      simpa [a, ha, uniformizerInClosure] using this
    exact (RingHom.injective (algebraMap (𝔭.adicCompletion K) K')) (by simpa using h1)
  have hβint : IsIntegral ↥L β :=
    ⟨X ^ n - C a, monic_X_pow_sub_C a hn.ne', by simp [hβa]⟩
  have hfin : Module.finrank ↥L ↥(IntermediateField.adjoin ↥L ({β} : Set K')) = n :=
    finrank_adjoin_urCl 𝔭 hn hcop hπ hβ
  have hminp : (minpoly ↥L β).natDegree = n := by
    rw [← adjoin.finrank hβint]; exact hfin
  have hdvd : minpoly ↥L β ∣ X ^ n - C a := by
    refine minpoly.dvd ↥L β ?_
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [sub_eq_zero]; exact hβa
  have hminpeq : X ^ n - C a = minpoly ↥L β :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβint)
      (monic_X_pow_sub_C a hn.ne') hdvd (by rw [natDegree_X_pow_sub_C, hminp])
  have hrootζ : aeval (ζ * β) (X ^ n - C a : Polynomial ↥L) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [sub_eq_zero, mul_pow, hζ, one_mul]
    exact hβa
  have hminpζ : X ^ n - C a = minpoly ↥L (ζ * β) :=
    minpoly.eq_of_irreducible_of_monic (hminpeq ▸ minpoly.irreducible hβint) hrootζ
      (monic_X_pow_sub_C a hn.ne')
  have hconj : IsConjRoot ↥L β (ζ * β) := hminpeq.symm.trans hminpζ
  obtain ⟨f, hf⟩ := IsConjRoot.exists_algEquiv hconj
  have hfsymm : f.symm β = ζ * β := (f.symm_apply_eq).mpr hf.symm
  refine ⟨(L.fixingSubgroupEquiv.symm f.symm : L.fixingSubgroup), ?_, ?_⟩
  · exact (L.fixingSubgroupEquiv.symm f.symm).2
  · exact hfsymm

/-- **The Tate twist, in the direction of the Frobenius normalisation.**

Let `π` be a uniformiser of `κ = K_𝔭`, `n` prime to `p`, `β ∈ K'` with `β ^ n = π` and
`β ∈ κ^{tr}`, and let `F ∈ Gal(K'/κ)` be an element which conjugates the tame inertia `I_κ` by
the `q`-th power map modulo `V_κ = Gal(K'/κ^{tr})` (the hypothesis
`NK.LocalTame.IsTameFrobeniusLift q V_κ I_κ F`).  Then `F` acts on the Kummer character
`σ β / β` of every `σ ∈ I_κ` by the `q`-th power map:
`F (σ β / β) = (σ β / β) ^ q`.

Both sides lie in `μ_n`; combined with the surjectivity of the Kummer pairing
(`exists_smul_root_of_coprime`) this gives `F ζ = ζ ^ q` for every `n`-th root of unity `ζ`. -/
theorem frobenius_apply_kummerChar {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    {n q : ℕ} (hn : ¬ resCharAt 𝔭 ∣ n)
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) {β : K'}
    (hβ : β ^ n = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
    {F : Gal(K'/𝔭.adicCompletion K)}
    (hF : ∀ σ : Gal(K'/𝔭.adicCompletion K),
      σ ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) →
      F * σ * F⁻¹ * (σ ^ q)⁻¹ ∈ correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭) π)
    {σ : Gal(K'/𝔭.adicCompletion K)}
    (hσ : σ ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭))
    (hβtr : β ∈ tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) (π : 𝔭.adicCompletion K)) :
    F (σ β / β) = (σ β / β) ^ q := by
  classical
  have hπcoe : (π : 𝔭.adicCompletion K) ≠ 0 := by
    have hirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
    exact fun h => hirr.ne_zero (Subtype.ext (by simpa using h))
  have hπne : algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) ≠ 0 :=
    fun h => hπcoe ((RingHom.injective (algebraMap (𝔭.adicCompletion K) K')) (by simpa using h))
  have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero (resCharAt 𝔭))
  have hβne : β ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hβ
    exact hπne hβ.symm
  have hσ' : σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭)).fixingSubgroup := by
    rw [← NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure]
    exact hσ
  set γ : K' := σ β / β with hγdef
  have hσβeq : σ β = γ * β := (div_mul_cancel₀ (σ β) hβne).symm
  have hγpow : γ ^ n = 1 := by
    rw [hγdef, div_pow, ← map_pow σ β n, hβ, AlgEquiv.commutes, div_self hπne]
  have hσγ : σ γ = γ := by
    have hmem : γ ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) :=
      mem_unramifiedClosure_of_pow_eq_one (κ := 𝔭.adicCompletion K) (K' := K') hn hγpow
    exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ' γ hmem
  set δ : K' := F.symm β / β with hδdef
  have hδpow : δ ^ n = 1 := by
    rw [hδdef, div_pow, ← map_pow F.symm β n, hβ, AlgEquiv.commutes, div_self hπne]
  have hσδ : σ δ = δ := by
    have hmem : δ ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) :=
      mem_unramifiedClosure_of_pow_eq_one (κ := 𝔭.adicCompletion K) (K' := K') hn hδpow
    exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ' δ hmem
  -- the Kummer character of `F σ F⁻¹` at `β` is `F γ`
  have hkey : (F * σ * F⁻¹) β = F γ * β := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    show F (σ (F.symm β)) = F γ * β
    have h1 : F.symm β = δ * β := (div_mul_cancel₀ (F.symm β) hβne).symm
    have h2 : σ (F.symm β) = γ * (F.symm β) := by
      rw [h1, map_mul, hσδ, hσβeq]
      ring
    rw [h2, map_mul, AlgEquiv.apply_symm_apply]
  have hσqβ : (σ ^ q) β = γ ^ q * β := by
    have hpoweq : ∀ k : ℕ, (σ ^ k) β = γ ^ k * β := by
      intro k; induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hσγ, hσβeq]
        ring
    exact hpoweq q
  -- the hypothesis: `F σ F⁻¹ (σ^q)⁻¹` lies in `V_κ = Gal(K'/κ^{tr})`, which fixes `β` and `γ`
  have hv := hF σ hσ
  have hvβ : (F * σ * F⁻¹ * (σ ^ q)⁻¹) β = β :=
    (IntermediateField.mem_fixingSubgroup_iff (tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K)) _).mp hv β hβtr
  have hγtr : γ ∈ tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K) :=
    unramifiedClosure_le_tameClosure (K' := K') (resCharAt 𝔭)
      ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)
      (mem_unramifiedClosure_of_pow_eq_one (κ := 𝔭.adicCompletion K) (K' := K') hn hγpow)
  have hvγ : (F * σ * F⁻¹ * (σ ^ q)⁻¹) γ = γ :=
    (IntermediateField.mem_fixingSubgroup_iff (tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K)) _).mp hv γ hγtr
  have hmain : (F * σ * F⁻¹) β = γ ^ q * β := by
    have heq : (F * σ * F⁻¹ * (σ ^ q)⁻¹) * (σ ^ q) = F * σ * F⁻¹ := by group
    rw [← heq, AlgEquiv.mul_apply, hσqβ, map_mul, map_pow, hvγ, hvβ]
  have hγeq : F γ = γ ^ q := by
    have h := hkey.symm.trans hmain
    exact mul_right_cancel₀ hβne h
  exact hγeq

theorem actsAsFrobenius_of_isTameFrobeniusLift {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {q : ℕ} {F : Gal(K'/𝔭.adicCompletion K)}
    (h : NK.LocalTame.IsTameFrobeniusLift q
      (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) π)
      (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)) F) :
    NK.LocalAnabelian.ActsAsFrobenius (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) q F := by
  intro n hn ζ hζ
  by_cases hn1 : n = 1
  · subst hn1
    have hζ1 : ζ = 1 := by simpa using hζ.pow_eq_one
    rw [hζ1, map_one, one_pow]
  · have hn0 : n ≠ 0 := fun hh => hn (hh ▸ dvd_zero (resCharAt 𝔭))
    have hp : (resCharAt 𝔭).Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
    have hcop : Nat.Coprime n (resCharAt 𝔭) :=
      Nat.coprime_comm.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
    haveI : CharZero K' := charZero_of_algebra_adicCompletion 𝔭
    haveI : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
    haveI : NeZero (n : K') := ⟨(Nat.cast_ne_zero).mpr hn0⟩
    have hπcoe : (π : 𝔭.adicCompletion K) ≠ 0 := by
      have hirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
      exact fun hh => hirr.ne_zero (Subtype.ext (by simpa using hh))
    have hπne : algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) ≠ 0 :=
      fun hh => hπcoe ((RingHom.injective (algebraMap (𝔭.adicCompletion K) K')) (by simpa using hh))
    -- an `n`-th root of the uniformiser, `n` prime to `p`
    obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
      (algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) n
    have hβne : β ≠ 0 := by
      intro hh
      rw [hh, zero_pow hn0] at hβ
      exact hπne hβ.symm
    -- the Kummer pairing attains the target root of unity
    obtain ⟨σ, hσmem, hσβ⟩ :=
      exists_smul_root_of_coprime 𝔭 (Nat.pos_of_ne_zero hn0) hcop hπ hβ hζ.pow_eq_one
    have hσmemI : σ ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) := by
      rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure]
      exact hσmem
    have hβtr : β ∈ tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) (π : 𝔭.adicCompletion K) :=
      adjoin_root_mem_tameClosure (K' := K') hn hβ
        (IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K) β)
    have hF' : ∀ σ : Gal(K'/𝔭.adicCompletion K),
        σ ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭) →
        F * σ * F⁻¹ * (σ ^ q)⁻¹ ∈ correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
            (resCharAt 𝔭) π :=
      fun σ hσ => h.2 σ hσ
    have key := frobenius_apply_kummerChar 𝔭 hn hπ hβ hF' hσmemI hβtr
    have hγζ : σ β / β = ζ := (div_eq_iff hβne).mpr hσβ
    rw [hγζ] at key
    exact key

end

end NK.TameStructureDeep.Tame
