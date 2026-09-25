import Mathlib
import Submission.NK.ChebotarevGeneral.Defs

/-!
# Descent of a Frobenius element to an intermediate field

Let `M` be an intermediate field of a finite Galois extension `N/K` of number fields, `P` a prime
of `𝓞 N` unramified over `𝔭 = P ∩ 𝓞 K`, and `σ ∈ Gal(N/K)` a Frobenius element at `P` which fixes
`M` pointwise.  Then

* the image of `σ` in `Gal(N/M)` (under `IntermediateField.fixingSubgroupEquiv`) is a Frobenius
  element at the prime `P ∩ 𝓞 M` of `𝓞 M`;
* the prime `P ∩ 𝓞 M` has residue degree one over `𝔭`.

The mathematical content is that `σ`, acting on the residue field `κ(P) = 𝓞 N / P` by the
`q`-th power map with `q = #κ(𝔭)`, fixes the residue field `κ(P ∩ 𝓞 M)` pointwise.  Hence every
element of `κ(P ∩ 𝓞 M)` satisfies `y ^ q = y`, and the `q`-th power map is the identity on the
residue field of `M`; by the finite field counting lemma
`Commons.NumberTheory.NumberField.le_of_forall_pow_eq_self` this forces
`f(P ∩ 𝓞 M | 𝔭) ≤ 1`, and the inertia degree is positive, so it is `1`.  The cardinality
`#κ(P ∩ 𝓞 M) = #κ(𝔭)` obtained from the same computation is exactly the compatibility of the
exponents which makes the defining congruence of a Frobenius element descend to the base field `M`.

The auxiliary statement `galRestrict_eq_of_apply_eq` records that the action of `galRestrict` on
`𝓞 N` only depends on the underlying permutation of `N`, so that the element of `Gal(N/K)` and its
image in `Gal(N/M)` induce the same automorphism of `𝓞 N`.
-/

namespace NK.ChebotarevGeneral

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Independence of `galRestrict` from the base field.**  If `τ : Gal(N/M)` and `σ : Gal(N/K)`
agree as permutations of `N`, they induce the same automorphism of `𝓞 N`; equivalently, the action
of `galRestrict` on `𝓞 N` only depends on the underlying function of the automorphism. -/
theorem galRestrict_eq_of_apply_eq {K M N : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field N] [NumberField N] [Algebra K M] [Algebra K N] [Algebra M N]
    [IsScalarTower K M N]
    (σ : Gal(N/K)) (τ : Gal(N/M)) (h : ∀ x : N, τ x = σ x) (x : NumberField.RingOfIntegers N) :
    galRestrict (NumberField.RingOfIntegers M) M N (NumberField.RingOfIntegers N) τ x =
      galRestrict (NumberField.RingOfIntegers K) K N (NumberField.RingOfIntegers N) σ x := by
  apply IsFractionRing.injective (NumberField.RingOfIntegers N) N
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply, h]

/-- **The defining congruence of a Frobenius element, descended to `𝓞 M`.**  If `σ` is a Frobenius
element at `P` and fixes `M` pointwise, then for every `x ∈ 𝓞 M` the class of `x` in the residue
field of `P` satisfies `x ^ #κ(𝔭) = x`. -/
theorem residue_pow_mk_eq_mk_under {K N : Type*} [Field K] [NumberField K] [Field N]
    [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (M : IntermediateField K N) {𝔭 : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal N}
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) {σ : Gal(N/K)} (hσ : σ ∈ M.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ) (x : NumberField.RingOfIntegers ↥M) :
    Ideal.Quotient.mk (P.under (NumberField.RingOfIntegers ↥M)).asIdeal
        (x ^ Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal)) =
      Ideal.Quotient.mk (P.under (NumberField.RingOfIntegers ↥M)).asIdeal x := by
  rw [Ideal.Quotient.eq,
    show (P.under (NumberField.RingOfIntegers ↥M)).asIdeal
        = Ideal.under (NumberField.RingOfIntegers ↥M) P.asIdeal from rfl,
    Ideal.mem_under]
  rw [map_sub, map_pow]
  -- `σ` fixes the image of `𝓞 M` in `𝓞 N` pointwise.
  have hfix : galRestrict (NumberField.RingOfIntegers K) K N (NumberField.RingOfIntegers N) σ
      (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x) =
      algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x := by
    apply IsFractionRing.injective (NumberField.RingOfIntegers N) N
    rw [algebraMap_galRestrict_apply,
      ← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M)
        (NumberField.RingOfIntegers N) N,
      IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥M) ↥M N]
    exact (IntermediateField.mem_fixingSubgroup_iff M σ).mp hσ
      (algebraMap (NumberField.RingOfIntegers ↥M) ↥M x)
      (algebraMap (NumberField.RingOfIntegers ↥M) ↥M x).2
  -- the Frobenius congruence at the image of `x`, with the exponent of the base field
  have hfrob' : galRestrict (NumberField.RingOfIntegers K) K N (NumberField.RingOfIntegers N) σ
      (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x) -
      (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x) ^
        Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) ∈ P.asIdeal := by
    have h := hfrob (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x)
    rwa [← hP.over] at h
  have h1 := hfrob'
  rw [hfix] at h1
  have h2 : (algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x) ^
      Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) -
      algebraMap (NumberField.RingOfIntegers ↥M) (NumberField.RingOfIntegers N) x ∈ P.asIdeal := by
    have := (Ideal.neg_mem_iff P.asIdeal).mpr h1
    rwa [neg_sub] at this
  exact h2

/-- The `#κ(𝔭)`-th power map is the identity on the residue field of `P ∩ 𝓞 M`. -/
theorem residue_pow_eq_self_under {K N : Type*} [Field K] [NumberField K] [Field N]
    [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (M : IntermediateField K N) {𝔭 : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal N}
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) {σ : Gal(N/K)} (hσ : σ ∈ M.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ) :
    ∀ y : NumberField.RingOfIntegers ↥M ⧸ (P.under (NumberField.RingOfIntegers ↥M)).asIdeal,
      y ^ Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) = y := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_pow]
  exact residue_pow_mk_eq_mk_under M hP hσ hfrob x

/-- **The residue degree of `P ∩ 𝓞 M` over `𝔭` is one.** -/
theorem inertiaDeg_under_eq_one {K N : Type*} [Field K] [NumberField K] [Field N]
    [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (M : IntermediateField K N) {𝔭 : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal N}
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) {σ : Gal(N/K)} (hσ : σ ∈ M.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ) :
    (P.under (NumberField.RingOfIntegers ↥M)).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers K) = 1 := by
  classical
  haveI hLies : (P.under (NumberField.RingOfIntegers ↥M)).asIdeal.LiesOver 𝔭.asIdeal :=
    Ideal.LiesOver.mk (by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
      exact hP.over)
  have hcard := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg
    (K := K) (L := ↥M) 𝔭 (P.under (NumberField.RingOfIntegers ↥M)) hLies
  haveI : Finite (NumberField.RingOfIntegers ↥M ⧸
      (P.under (NumberField.RingOfIntegers ↥M)).asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
      (P.under (NumberField.RingOfIntegers ↥M))
  haveI : Fintype (NumberField.RingOfIntegers ↥M ⧸
      (P.under (NumberField.RingOfIntegers ↥M)).asIdeal) := Fintype.ofFinite _
  haveI : Finite (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum 𝔭
  haveI : Fintype (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  letI : Field (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
  letI : Field (NumberField.RingOfIntegers ↥M ⧸
      (P.under (NumberField.RingOfIntegers ↥M)).asIdeal) := Ideal.Quotient.field _
  have hq2 : 2 ≤ Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hle : ((P.under (NumberField.RingOfIntegers ↥M)).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers K)) ≤ 1 :=
    Commons.NumberTheory.NumberField.le_of_forall_pow_eq_self hcard hq2 (by norm_num)
      (fun y => by
        rw [pow_one]
        exact residue_pow_eq_self_under M hP hσ hfrob y)
  have hpos := Ideal.inertiaDeg_pos (P.under (NumberField.RingOfIntegers ↥M)).asIdeal
    (NumberField.RingOfIntegers K)
  omega

/-- **The residue field of `P ∩ 𝓞 M` has the same cardinality as that of `𝔭`.** -/
theorem residue_card_under_eq {K N : Type*} [Field K] [NumberField K] [Field N]
    [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (M : IntermediateField K N) {𝔭 : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal N}
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) {σ : Gal(N/K)} (hσ : σ ∈ M.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ) :
    Nat.card (NumberField.RingOfIntegers ↥M ⧸ (P.under (NumberField.RingOfIntegers ↥M)).asIdeal) =
      Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := by
  classical
  haveI hLies : (P.under (NumberField.RingOfIntegers ↥M)).asIdeal.LiesOver 𝔭.asIdeal :=
    Ideal.LiesOver.mk (by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
      exact hP.over)
  have hcard := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg
    (K := K) (L := ↥M) 𝔭 (P.under (NumberField.RingOfIntegers ↥M)) hLies
  rw [hcard, inertiaDeg_under_eq_one M hP hσ hfrob, pow_one]

/-- The residue degree, in the `inertiaDeg'` form used in the statement of
`isFrobAtPrime_under_of_isFrobAt`. -/
theorem inertiaDeg'_under_eq_one {K N : Type*} [Field K] [NumberField K] [Field N]
    [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (M : IntermediateField K N) {𝔭 : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal N}
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) {σ : Gal(N/K)} (hσ : σ ∈ M.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ) :
    𝔭.asIdeal.inertiaDeg' (P.under (NumberField.RingOfIntegers ↥M)).asIdeal = 1 := by
  haveI hLies : (P.under (NumberField.RingOfIntegers ↥M)).asIdeal.LiesOver 𝔭.asIdeal :=
    Ideal.LiesOver.mk (by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
      exact hP.over)
  haveI : 𝔭.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal 𝔭.isPrime 𝔭.ne_bot
  haveI : (P.under (NumberField.RingOfIntegers ↥M)).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (P.under _).isPrime (P.under _).ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg]
  exact inertiaDeg_under_eq_one M hP hσ hfrob

/-- **Descent of a Frobenius element to an intermediate field.**  Let `M` be an intermediate field
of `N/K` and let `σ ∈ Gal(N/K)` fix `M` pointwise.  If `σ` is a Frobenius element at a prime `P` of
`𝓞 N` which is unramified over `𝔭 = P ∩ 𝓞 K`, then the image of `σ` in `Gal(N/M)` is a Frobenius
element at `P ∩ 𝓞 M`, and that prime has residue degree one over `𝔭`. -/
theorem isFrobAtPrime_under_of_isFrobAt {K N : Type*} [Field K] [NumberField K] [Field N]
    [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (M : IntermediateField K N) {𝔭 : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal N}
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal)
    (hram : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    {σ : Gal(N/K)} (hσ : σ ∈ M.fixingSubgroup)
    (hfrob : NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ) :
    NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N)
        (P.under (NumberField.RingOfIntegers ↥M)) (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
      𝔭.asIdeal.inertiaDeg' (P.under (NumberField.RingOfIntegers ↥M)).asIdeal = 1 := by
  have hcard := residue_card_under_eq M hP hσ hfrob
  -- the exponent in the definition of `IsFrobAt` over `M` is `#κ(𝔭)`
  have hfrobM : NK.Chebotarev.IsFrobAt (K := ↥M) (L := N) P
      (M.fixingSubgroupEquiv ⟨σ, hσ⟩) := by
    intro x
    rw [show Nat.card (NumberField.RingOfIntegers ↥M ⧸
          Ideal.under (NumberField.RingOfIntegers ↥M) P.asIdeal) =
        Nat.card (NumberField.RingOfIntegers ↥M ⧸
          (P.under (NumberField.RingOfIntegers ↥M)).asIdeal) from rfl,
      hcard, hP.over]
    show galRestrict (NumberField.RingOfIntegers ↥M) ↥M N (NumberField.RingOfIntegers N)
        (M.fixingSubgroupEquiv ⟨σ, hσ⟩) x -
        x ^ Nat.card (NumberField.RingOfIntegers K ⧸
          P.asIdeal.under (NumberField.RingOfIntegers K)) ∈ P.asIdeal
    rw [galRestrict_eq_of_apply_eq σ (M.fixingSubgroupEquiv ⟨σ, hσ⟩) (fun y => rfl) x]
    exact hfrob x
  exact ⟨⟨P, Ideal.LiesOver.mk rfl, hfrobM⟩, inertiaDeg'_under_eq_one M hP hσ hfrob⟩

end NK.ChebotarevGeneral
