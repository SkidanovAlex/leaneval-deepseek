import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.Chebotarev.FrobRestriction
import Submission.NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver
import Submission.NK.CFTLib.Arl.sum_ramificationIdx_mul_inertiaDeg_primesOverFinite

/-!
# The Frobenius product `∏_{𝔮 | 𝔭} Frob_𝔮 ^ e(𝔮|𝔭)` is trivial

Let `E / K` be a finite Galois extension of number fields, `L₀ M ≤ E` intermediate fields with
`L₀ ⊓ M = ⊥` and `L₀ ⊔ M = ⊤` (so that `E = L₀ M` and restriction is an isomorphism
`Gal(E/L₀) ≅ Gal(M/K)`), and assume `Gal(M/K)` abelian with exponent dividing `[L₀ : K]`.
If `M/K` is unramified at the prime `𝔭` of `K` and `E/L₀` is unramified at every prime of `L₀`
above `𝔭`, then

`∏_{𝔮 | 𝔭} Frob_𝔮(E/L₀) ^ e(𝔮|𝔭) = 1` in `Gal(E/L₀)`.

The proof restricts the product to `M`: the Frobenius at `𝔮` (for `E/L₀`) restricts to
`Frob(𝔓)^{f(𝔮|𝔭)}` for any prime `𝔓` of `M` above `𝔭`, so the product restricts to
`Frob(𝔓)^{∑_𝔮 e(𝔮|𝔭) f(𝔮|𝔭)} = Frob(𝔓)^{[L₀:K]} = 1` by the fundamental identity and the
exponent hypothesis, and `φ` is injective.

This is the "product of Frobenius elements over a prime" computation used in the reconstruction
step of Neukirch–Uchida.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

open NK.Chebotarev

/-! ## Restriction maps -/

/-- Restriction of scalars `Gal(E/L₀) →* Gal(E/K)`, for `K ≤ L₀ ≤ E`. -/
def restrictScalarsHom {K E' : Type*} [Field K] [Field E'] [Algebra K E']
    (L₀ : IntermediateField K E') : Gal(E'/↥L₀) →* Gal(E'/K) where
  toFun σ := AlgEquiv.restrictScalars K σ
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

lemma restrictScalarsHom_apply {K E' : Type*} [Field K] [Field E'] [Algebra K E']
    (L₀ : IntermediateField K E') (σ : Gal(E'/↥L₀)) :
    restrictScalarsHom L₀ σ = AlgEquiv.restrictScalars K σ := rfl

/-- Restriction `Gal(E/L₀) →* Gal(M/K)` for a normal intermediate field `M`. -/
def restrictGalEquiv {K E' : Type*} [Field K] [Field E'] [Algebra K E']
    (L₀ M : IntermediateField K E') [Normal K M] : Gal(E'/↥L₀) →* Gal(↥M/K) :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := E') ↥M).comp (restrictScalarsHom L₀)

lemma restrictGalEquiv_apply {K E' : Type*} [Field K] [Field E'] [Algebra K E']
    (L₀ M : IntermediateField K E') [Normal K M] (σ : Gal(E'/↥L₀)) :
    restrictGalEquiv L₀ M σ
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := E') ↥M
          (AlgEquiv.restrictScalars K σ) := rfl

/-! ## Base change and descent for `galRestrict` -/

/-- `galRestrict` does not depend on which base ring of integers is used, as long as the
underlying automorphism is the same. -/
theorem galRestrict_baseChange {K E' : Type*} [Field K] [NumberField K] [Field E']
    [NumberField E'] [Algebra K E'] [FiniteDimensional K E'] [IsGalois K E']
    (L₀ : IntermediateField K E') (σ : E' ≃ₐ[↥L₀] E') (x : NumberField.RingOfIntegers E') :
    galRestrict (NumberField.RingOfIntegers ↥L₀) ↥L₀ E' (NumberField.RingOfIntegers E') σ x
      = galRestrict (NumberField.RingOfIntegers K) K E' (NumberField.RingOfIntegers E')
          (AlgEquiv.restrictScalars K σ) x := by
  apply IsIntegralClosure.algebraMap_injective (NumberField.RingOfIntegers E')
    (NumberField.RingOfIntegers K) E'
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply,
    AlgEquiv.restrictScalars_apply]

/-- Compatibility of `galRestrict` with restriction to a normal intermediate field, phrased with
the top field: the image of `galRestrict ρ` on `𝓞 M` under `algebraMap` is `galRestrict ρ` on
`𝓞 E`. -/
theorem galRestrict_restrictNormalHom_apply {K E' : Type*} [Field K] [NumberField K] [Field E']
    [NumberField E'] [Algebra K E'] [FiniteDimensional K E'] [IsGalois K E']
    (M : IntermediateField K E') [Normal K M] (ρ : E' ≃ₐ[K] E')
    (x : NumberField.RingOfIntegers ↥M) :
    algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers E')
        (galRestrict (NumberField.RingOfIntegers K) K ↥M (NumberField.RingOfIntegers ↥M)
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := E') ↥M ρ) x)
      = galRestrict (NumberField.RingOfIntegers K) K E' (NumberField.RingOfIntegers E') ρ
          (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers E') x) := by
  apply IsIntegralClosure.algebraMap_injective (NumberField.RingOfIntegers E')
    (NumberField.RingOfIntegers K) E'
  rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M)
    (NumberField.RingOfIntegers E') E']
  rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M E']
  rw [algebraMap_galRestrict_apply]
  rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := E') ↥M ρ) = ρ.restrictNormal ↥M
    from rfl]
  rw [AlgEquiv.restrictNormal_commutes]
  rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M E']
  rw [algebraMap_galRestrict_apply]
  rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M)
    (NumberField.RingOfIntegers E') E']

/-! ## The residue action of a power of a Frobenius element -/

/-- A Frobenius element acting `k` times on the residue field acts as the `(N𝔭)^k`-th power. -/
theorem isFrobAt_pow_residue {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {𝔭 : PrimeIdeal K} {𝔓 : PrimeIdeal L} (h𝔓 : 𝔓.asIdeal.LiesOver 𝔭.asIdeal)
    {g : Gal(L/K)} (hg : IsFrobAt 𝔓 g) (k : ℕ) (x : NumberField.RingOfIntegers L) :
    galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) (g ^ k) x
      - x ^ ((Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal)) ^ k) ∈ 𝔓.asIdeal := by
  have hkey : ∀ k : ℕ, ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk 𝔓.asIdeal
        (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L)
          (g ^ k) x)
      = (Ideal.Quotient.mk 𝔓.asIdeal x)
          ^ ((Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal)) ^ k) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ]
      rw [map_mul]
      rw [AlgEquiv.mul_apply]
      rw [ih]
      rw [hg.mk_apply h𝔓]
      rw [← pow_mul, pow_succ, mul_comm]
  rw [← Ideal.Quotient.eq]
  exact hkey k x

/-! ## Injectivity of the restriction `Gal(E/L₀) →* Gal(M/K)` -/

/-- If `L₀ ⊓ M = ⊥` and `L₀ ⊔ M = ⊤` then restriction to `M` is injective on `Gal(E/L₀)`. -/
theorem restrictGalEquiv_injective {K E' : Type*} [Field K] [Field E'] [Algebra K E']
    (L₀ M : IntermediateField K E') [Normal K M]
    (hdisj : L₀ ⊓ M = ⊥) (hsup : L₀ ⊔ M = ⊤) :
    Function.Injective (restrictGalEquiv L₀ M) := by
  intro σ τ hστ
  have hker : restrictGalEquiv L₀ M (σ * τ⁻¹) = 1 := by
    rw [map_mul, hστ, map_inv, mul_inv_cancel]
  have hMle : M ≤ IntermediateField.fixedField
      (Subgroup.zpowers (AlgEquiv.restrictScalars K (σ * τ⁻¹))) := by
    rw [IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hc := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K (σ * τ⁻¹)) ↥M ⟨x, hx⟩
    rw [show (AlgEquiv.restrictScalars K (σ * τ⁻¹)).restrictNormal ↥M = 1 from hker] at hc
    simpa using hc.symm
  have hLle : L₀ ≤ IntermediateField.fixedField
      (Subgroup.zpowers (AlgEquiv.restrictScalars K (σ * τ⁻¹))) := by
    rw [IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (σ * τ⁻¹).commutes ⟨x, hx⟩
  have htop : (⊤ : IntermediateField K E') ≤ IntermediateField.fixedField
      (Subgroup.zpowers (AlgEquiv.restrictScalars K (σ * τ⁻¹))) := by
    rw [← hsup]
    exact sup_le hLle hMle
  have hfix : ∀ x : E', (σ * τ⁻¹) x = x := by
    intro x
    have hx0 : x ∈ (⊤ : IntermediateField K E') := IntermediateField.mem_top
    have hx := htop hx0
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact hx _ (Subgroup.mem_zpowers _)
  have hone : (σ * τ⁻¹ : Gal(E'/↥L₀)) = 1 := by
    ext x
    exact hfix x
  exact mul_inv_eq_one.mp hone


/-! ## Converting a residue congruence into an equality in the residue ring -/

lemma mk_eq_pow_of_sub_mem {R : Type*} [CommRing R] {I : Ideal R} {a b : R} {n : ℕ}
    (h : a - b ^ n ∈ I) : Ideal.Quotient.mk I a = (Ideal.Quotient.mk I b) ^ n := by
  rw [← map_pow, Ideal.Quotient.eq]
  exact h

/-! ## The residue degree identity -/

/-- The norm of a prime of `𝓞 L` is the `f(𝔮|𝔭)`-th power of the norm of the prime below it. -/
lemma cardQuot_pow_inertiaDeg_eq {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {𝔭 : PrimeIdeal K} {𝔮 : PrimeIdeal L} (h𝔮 : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    (Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal))
        ^ (𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))
      = Nat.card (NumberField.RingOfIntegers L ⧸ 𝔮.asIdeal) := by
  haveI := h𝔮
  have h1 : Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal)
      = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h2 : Nat.card (NumberField.RingOfIntegers L ⧸ 𝔮.asIdeal)
      = Ideal.absNorm 𝔮.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h1, h2]
  exact Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal 𝔮.asIdeal

/-! ## The Frobenius at `𝔮` restricted to `M` -/

/-- The restriction to `Gal(M/K)` of the Frobenius of `E/L₀` at the prime `𝔮` is the
`f(𝔮|𝔭)`-th power of a Frobenius element at `𝔭`. -/
theorem frobAtPrime_restrict_eq_pow {K E : Type*} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (L₀ M : IntermediateField K E) [IsGalois K ↥M]
    (𝔭 : PrimeIdeal K)
    (hunrM : ∀ Q : PrimeIdeal ↥M, Q.asIdeal.LiesOver 𝔭.asIdeal →
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (g : Gal(↥M/K))
    (hg : ∀ Q : PrimeIdeal ↥M, Q.asIdeal.LiesOver 𝔭.asIdeal → IsFrobAt Q g)
    (𝔮 : PrimeIdeal ↥L₀) (h𝔮 : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    restrictGalEquiv L₀ M (frobAtPrime (K := ↥L₀) (L := E) 𝔮)
      = g ^ (𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  classical
  haveI : Normal K ↥M := inferInstance
  set σ := frobAtPrime (K := ↥L₀) (L := E) 𝔮 with hσdef
  have hσfrob : IsFrobAtPrime (K := ↥L₀) (L := E) 𝔮 σ := by
    rw [hσdef, frobAtPrime,
      dif_pos (exists_isFrobAtPrime (K := ↥L₀) (L := E) 𝔮)]
    exact (exists_isFrobAtPrime (K := ↥L₀) (L := E) 𝔮).choose_spec
  obtain ⟨𝔔, h𝔔over, h𝔔⟩ := hσfrob
  set 𝔓 := 𝔔.under (NumberField.RingOfIntegers ↥M) with h𝔓def
  have h𝔓 : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    show 𝔭.asIdeal
      = Ideal.under (NumberField.RingOfIntegers K)
          (Ideal.under (NumberField.RingOfIntegers ↥M) 𝔔.asIdeal)
    rw [h𝔮.over, h𝔔over.over]
    simp only [Ideal.under_under]
  have hunr𝔓 : 𝔓.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := hunrM 𝔓 h𝔓
  -- the residue action of the restriction of the Frobenius at `𝔮`
  have hleft : ∀ x : NumberField.RingOfIntegers ↥M,
      galRestrict (NumberField.RingOfIntegers K) K ↥M (NumberField.RingOfIntegers ↥M)
          (restrictGalEquiv L₀ M σ) x
        - x ^ (Nat.card (NumberField.RingOfIntegers ↥L₀ ⧸ 𝔮.asIdeal)) ∈ 𝔓.asIdeal := by
    intro x
    show galRestrict (NumberField.RingOfIntegers K) K ↥M (NumberField.RingOfIntegers ↥M)
          (restrictGalEquiv L₀ M σ) x
        - x ^ (Nat.card (NumberField.RingOfIntegers ↥L₀ ⧸ 𝔮.asIdeal))
        ∈ Ideal.under (NumberField.RingOfIntegers ↥M) 𝔔.asIdeal
    rw [Ideal.mem_under, map_sub, map_pow]
    rw [restrictGalEquiv_apply]
    rw [galRestrict_restrictNormalHom_apply M (AlgEquiv.restrictScalars K σ) x]
    rw [← galRestrict_baseChange L₀ σ (algebraMap (NumberField.RingOfIntegers ↥M)
      (NumberField.RingOfIntegers E) x)]
    have h := h𝔔 (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers E) x)
    rwa [show 𝔔.asIdeal.under (NumberField.RingOfIntegers ↥L₀) = 𝔮.asIdeal
      from h𝔔over.over.symm] at h
  -- the residue action of the `f(𝔮|𝔭)`-th power of the Frobenius at `𝔭`
  have hright : ∀ x : NumberField.RingOfIntegers ↥M,
      galRestrict (NumberField.RingOfIntegers K) K ↥M (NumberField.RingOfIntegers ↥M)
          (g ^ (𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))) x
        - x ^ (Nat.card (NumberField.RingOfIntegers ↥L₀ ⧸ 𝔮.asIdeal)) ∈ 𝔓.asIdeal := by
    intro x
    have h := isFrobAt_pow_residue (K := K) (L := ↥M) h𝔓 (hg 𝔓 h𝔓)
      (𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) x
    rwa [cardQuot_pow_inertiaDeg_eq h𝔮] at h
  have hres := Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.eq_of_residue_mk_eq
    (K := K) (L := ↥M) 𝔭 𝔓 h𝔓 hunr𝔓 (restrictGalEquiv L₀ M σ)
    (g ^ (𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)))
    (fun x => by
      rw [mk_eq_pow_of_sub_mem (hleft x), mk_eq_pow_of_sub_mem (hright x)])
  rwa [hσdef] at hres

/-! ## The main theorem -/

/-- **The product of the Frobenius elements at the primes above `𝔭`, raised to the ramification
index, is trivial.** -/
theorem prod_frobAtPrime_ramificationIdx_eq_one {K E : Type*} [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (L₀ M : IntermediateField K E) [IsGalois K ↥M]
    [IsMulCommutative (↥M ≃ₐ[K] ↥M)]
    (hdisj : L₀ ⊓ M = ⊥) (hsup : L₀ ⊔ M = ⊤)
    (hexp : ∀ σ : ↥M ≃ₐ[K] ↥M, σ ^ (Module.finrank K ↥L₀) = 1)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunrM : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
      Q.asIdeal.LiesOver 𝔭.asIdeal → Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hunrE : ∀ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L₀) 𝔭,
      ∀ 𝔔 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E),
        𝔔.asIdeal.LiesOver 𝔮.asIdeal →
          𝔔.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L₀) = 1) :
    ((NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L₀) 𝔭).toList.map
      (fun 𝔮 => (NK.Chebotarev.frobAtPrime (K := ↥L₀) (L := E) 𝔮) ^
        (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)))).prod = 1 := by
  classical
  haveI : Normal K ↥M := inferInstance
  have hcomm : ∀ a b : Gal(↥M/K), a * b = b * a := fun a b => mul_comm' a b
  let φ : Gal(E/↥L₀) →* Gal(↥M/K) := restrictGalEquiv L₀ M
  have hφinj : Function.Injective φ := restrictGalEquiv_injective L₀ M hdisj hsup
  -- a Frobenius element at `𝔭`, valid at every prime of `M` above `𝔭`
  obtain ⟨𝔓₀, h𝔓₀⟩ := exists_primeIdeal_liesOver (K := K) (L := ↥M) 𝔭
  obtain ⟨g, hg⟩ := exists_isFrobAt (K := K) (L := ↥M) 𝔭 𝔓₀ h𝔓₀
  have hFrobAny : ∀ Q : PrimeIdeal ↥M, Q.asIdeal.LiesOver 𝔭.asIdeal → IsFrobAt Q g :=
    fun Q hQ => isFrobAt_of_isFrobAt_any_primeOver hcomm h𝔓₀ hQ hg
  -- the fundamental identity
  have hsum : ∑ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L₀) 𝔭,
      𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
        * 𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)
      = Module.finrank K ↥L₀ := by
    rw [Finset.sum_congr rfl (fun 𝔮 _ => mul_comm _ _)]
    exact sum_ramificationIdx_mul_inertiaDeg_primesOverFinite (K := K) (L := ↥L₀) 𝔭
  -- the image of the Frobenius at `𝔮` under the restriction, raised to the ramification index
  have hterm : ∀ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L₀) 𝔭,
      φ ((NK.Chebotarev.frobAtPrime (K := ↥L₀) (L := E) 𝔮) ^
          (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)))
        = g ^ (𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
            * 𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) := by
    intro 𝔮 h𝔮
    have h1 : φ (NK.Chebotarev.frobAtPrime (K := ↥L₀) (L := E) 𝔮)
        = g ^ (𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) :=
      frobAtPrime_restrict_eq_pow L₀ M 𝔭 hunrM g hFrobAny 𝔮
        ((NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := ↥L₀) (Q := 𝔭)).mp h𝔮)
    rw [map_pow, h1, ← pow_mul]
  -- evaluate the product over a list of primes
  have key : ∀ l : List (NK.Chebotarev.PrimeIdeal ↥L₀),
      (∀ 𝔮 ∈ l, 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := ↥L₀) 𝔭) →
      φ ((l.map (fun 𝔮 => (NK.Chebotarev.frobAtPrime (K := ↥L₀) (L := E) 𝔮) ^
            (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)))).prod)
        = g ^ ((l.map (fun 𝔮 => (𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))
            * (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)))).sum) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons 𝔮 l ih =>
      intro hl
      rw [List.map_cons, List.prod_cons, map_mul,
        ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)),
        hterm 𝔮 (hl 𝔮 List.mem_cons_self),
        List.map_cons, List.sum_cons, pow_add]
  apply hφinj
  rw [map_one, key _ (fun 𝔮 h𝔮 => Finset.mem_toList.mp h𝔮), Finset.sum_map_toList, hsum]
  exact hexp g

end NK.CFTLib.Arl

end
