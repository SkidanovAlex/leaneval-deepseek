import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocVal
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocAux
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletion_intCast_eq_padicValInt
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open scoped NumberField WithZero
open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- **Integrality descends along an injective algebra map.** -/
lemma isIntegral_of_injective_algebraMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (h : Function.Injective (algebraMap A B)) {y : A} (hy : IsIntegral R (algebraMap A B y)) :
    IsIntegral R y :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) h).mp hy

/-- In a commutative ring, a left factor of a unit is a unit. -/
lemma isUnit_of_mul_isUnit' {S : Type*} [CommRing S] {a b : S} (h : IsUnit (a * b)) : IsUnit a := by
  obtain ⟨u, hu⟩ := h
  refine ⟨⟨a, b * ↑u⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← mul_assoc, ← hu, Units.mul_inv]
  · rw [mul_assoc, mul_comm ↑u⁻¹ a, ← mul_assoc, mul_comm b a, ← hu, Units.mul_inv]

/-- **The derivative of the minimal polynomial of a root of unity is a unit.**

If `x ∈ S` satisfies `x ^ N = 1` and `(N : S) * x ^ (N - 1)` is a unit of `S`, then
`(minpoly A x)'(x)` is a unit of `S`.  This is the `A`-part of
`isUnit_aeval_derivative_minpoly` (which additionally requires a `K`-algebra structure on `S`,
something that is not available for the subring `C` used below). -/
lemma isUnit_aeval_derivative_minpoly_of_pow_eq_one {A S : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing S] [IsDomain S] [Algebra A S] [Module.IsTorsionFree A S]
    {x : S} (hx : IsIntegral A x) (N : ℕ)
    (hxN : x ^ N = 1) (hunit : IsUnit ((N : S) * x ^ (N - 1))) :
    IsUnit ((Polynomial.aeval x) (Polynomial.derivative (minpoly A x))) := by
  have hdvd : minpoly A x ∣ (Polynomial.X ^ N - 1 : Polynomial A) :=
    minpoly.isIntegrallyClosed_dvd hx (p := Polynomial.X ^ N - 1) (by
      rw [Polynomial.aeval_sub, Polynomial.aeval_one, Polynomial.aeval_X_pow, hxN, sub_self])
  obtain ⟨h, hh⟩ := hdvd
  have hderiv : Polynomial.derivative (Polynomial.X ^ N - 1 : Polynomial A) =
      Polynomial.derivative (minpoly A x) * h + minpoly A x * Polynomial.derivative h := by
    rw [hh, Polynomial.derivative_mul]
  have hval : (N : S) * x ^ (N - 1) =
      (Polynomial.aeval x) (Polynomial.derivative (minpoly A x)) *
        (Polynomial.aeval x) h := by
    have h1 : (Polynomial.aeval x)
        (Polynomial.derivative (Polynomial.X ^ N - 1 : Polynomial A)) =
        (Polynomial.aeval x) (Polynomial.derivative (minpoly A x) * h +
          minpoly A x * Polynomial.derivative h) := by rw [hderiv]
    rw [map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero] at h1
    rw [← h1]
    rw [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
      Polynomial.derivative_X_pow, Polynomial.aeval_mul, Polynomial.aeval_C,
      Polynomial.aeval_X_pow]
    simp
  exact isUnit_of_mul_isUnit' (hval ▸ hunit)

/-- **The value group of the inertia field of a completed number field.**

`E := ℚ_p(ζ) ⊆ M := Q.adicCompletion K` where `ζ ∈ B := Q.adicCompletionIntegers K` is a
Teichmüller lift of a generator of `κ_B` (`p ∤ N`, `N := Nat.card κ_B - 1 = p^f - 1`), and
`e := Q.asIdeal.ramificationIdx (𝓞 ℚ)`.  Then every *integral* element `x ∈ E` (i.e. `x ∈ B`)
has `adicValExp Q x` divisible by `e`.

Proof plan (all ingredients available in this workspace).
* `Nat.card κ_B = p ^ f` (`card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg`), so
  `N = p ^ f - 1` and `p ∤ N`; `ζ` has order `N`.
* `C := integralClosure ℤ_p E` is a local ring: `x ∈ C` is a unit iff its image in `B` is not in
  `𝔪_B` (if `x ∉ 𝔪_B` then `x⁻¹ ∈ E ∩ B = C`).  Its residue field is `𝔽_{p^f}` because `ζ̄`
  generates `κ_B`.  It is a Dedekind domain (`IsIntegralClosure.isDedekindDomain`), hence a
  discrete valuation ring.
* `𝔡_{ℤ_p → C} = ⊤`: `isUnit_aeval_derivative_minpoly` in
  `Submission/Work/SSGRoute/TatePoitouRoute/FinitenessHM/adicLocVal.lean` (applied with
  `A := ℤ_p`, `K := ℚ_p`, `S := C`, `x := ζ`, `N`, using that `N` is a unit of `ℤ_p` and `ζ` a
  unit of `C`) gives that `(minpoly ℤ_p ζ)'(ζ)` is a unit of `C`, and by
  `aeval_derivative_mem_differentIdeal` (with `A := ℤ_p`, `K := ℚ_p`, `B := C`, `L := E`) it lies
  in `𝔡_{ℤ_p → C}`; an ideal containing a unit is `⊤`.
* Hence `Algebra.IsUnramifiedAt ℤ_p 𝔪_C` (`not_dvd_differentIdeal_iff`) and so
  `Algebra.isUnramifiedAt_iff_map_eq` gives `𝔪_A · (C)_{𝔪_C} = 𝔪_C · (C)_{𝔪_C}`; since `C` is
  local, `(C)_{𝔪_C} = C` (`IsLocalization.of_le_isUnit` + `IsLocalization.algEquiv`), so
  `(p) C = 𝔪_C`, i.e. `p` is a uniformiser of the discrete valuation ring `C`.
* `v_M (p) = exp (-e)` from `val_adicCompletionMap_eq_pow` applied to `p : ℚ_p` (whose valuation is
  `exp (-1)`, cf. `val_adicCompletion_intCast_eq_padicValInt`).
* For `x ∈ E ∩ B` (so `x ∈ C` and `x ≠ 0`), `IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible`
  on `C` with the irreducible element `p` writes `x = u • (p : E)^n` with `u ∈ C^× ⊆ B^×`; hence
  `v x = v(p)^n = exp (-(n e))`, i.e. `adicValExp Q x = n * e`.-/
theorem adicValExp_mem_eZ_of_mem_adjoin_lift {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal)
    (ζ : Q.adicCompletionIntegers K)
    (hζ : IsPrimitiveRoot (ζ : Q.adicCompletion K)
      (Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) - 1)) :
    letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
    ∀ x : Q.adicCompletion K, x ≠ 0 →
      x ∈ (IntermediateField.adjoin (Q0.adicCompletion ℚ)
        {((ζ : Q.adicCompletionIntegers K) : Q.adicCompletion K)} : Set (Q.adicCompletion K)) →
      (x : Q.adicCompletion K) ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) →
      ∃ k : ℤ, adicValExp Q x = k * (Q.asIdeal.ramificationIdx
        (NumberField.RingOfIntegers ℚ) : ℤ) := by
  letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
  intro x hx0 hxE hxB
  -- ## 0. notation and the basic objects
  haveI : CharZero (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion Q
  have hmemA : (p : 𝓞 ℚ) ∈ Q0.asIdeal := by
    rw [hQ0]; exact Ideal.mem_span_singleton_self _
  let ℚp := Q0.adicCompletion ℚ
  let ℤp := Q0.adicCompletionIntegers ℚ
  let M := Q.adicCompletion K
  let B := Q.adicCompletionIntegers K
  letI : Algebra ℤp M := RingHom.toAlgebra
    ((Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ).comp ℤp.subtype)
  letI : Algebra ℤp B := RingHom.toAlgebra
    (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ)
  let E : IntermediateField ℚp M := IntermediateField.adjoin ℚp {((ζ : B) : M)}
  letI : Algebra ℤp E := RingHom.toAlgebra ((algebraMap ℚp E).comp (algebraMap ℤp ℚp))
  haveI hST1 : IsScalarTower ℤp ℚp E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hST2 : IsScalarTower ℤp E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hST3 : IsScalarTower ℤp B M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hST4 : IsScalarTower ℚp E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let C : Subalgebra ℤp E := integralClosure ℤp E
  -- the ring homomorphisms
  let iCE : C →+* E := algebraMap C E
  let iEM : E →+* M := algebraMap E M
  let iBM : B →+* M := algebraMap B M
  -- ## 1. `B` is the integral closure of `ℤp` in `M`, and `C = E ∩ B`
  haveI hIC : IsIntegralClosure B ℤp M :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
      Q0 Q hQ
  have hv : (Valued.v : Valuation M ℤᵐ⁰).Integers B :=
    Valuation.integer.integers (Valued.v : Valuation M ℤᵐ⁰)
  haveI hIC2 : IsIntegralClosure C ℤp E := integralClosure.isIntegralClosure ℤp E
  have hC_iff : ∀ y : E, y ∈ C ↔ iEM y ∈ B := by
    intro y
    constructor
    · intro hy
      have h1 : IsIntegral ℤp y :=
        IsIntegral.algebraMap (IsIntegralClosure.isIntegral ℤp E (⟨y, hy⟩ : ↥C))
      have h2 : IsIntegral ℤp (iEM y) :=
        IsIntegral.algebraMap (R := ℤp) (A := ↥E) (B := M) h1
      obtain ⟨b, hb⟩ :=
        (IsIntegralClosure.isIntegral_iff (A := ↥B) (R := ℤp) (B := M)).mp h2
      rw [← hb]
      exact b.2
    · intro hy
      refine (mem_integralClosure_iff ℤp E).mpr ?_
      refine isIntegral_of_injective_algebraMap (algebraMap E M).injective ?_
      let b : ↥B := ⟨iEM y, hy⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom ℤp ↥B M)
        (IsIntegralClosure.isIntegral ℤp M b)
  -- ## 2. the ring hom `C →+* B`
  have hCB : ∀ c : C, iEM (iCE c) ∈ B := fun c =>
    (hC_iff (iCE c)).mp (show iCE c ∈ C from c.2)
  let φ : C →+* B := (iEM.comp iCE).codRestrict B hCB
  have hφ_coe : ∀ c : C, iBM (φ c) = iEM (iCE c) := fun c => rfl
  have hφ_nat : ∀ n : ℕ, φ (n : C) = (n : B) := fun n => map_natCast φ n
  -- ## 3. `C` is a local ring
  have hunit_iff : ∀ c : C, IsUnit c ↔ IsUnit (φ c) := by
    intro c
    refine ⟨fun h => IsUnit.map φ.toMonoidHom h, fun h => ?_⟩
    obtain ⟨u, hu⟩ := h
    have hu' : (u : B) = φ c := hu
    have hcE : iCE c ≠ 0 := by
      intro h0
      have h1 : (u : B) = 0 := by
        rw [hu']
        apply Subtype.ext
        show iBM (φ c) = iBM 0
        rw [hφ_coe c, h0, map_zero, map_zero]
      exact u.ne_zero h1
    have hcoe : iBM ((u : B)) = iEM (iCE c) := by rw [hu', hφ_coe]
    have hinv' : iBM ((u⁻¹ : Bˣ) : B) = (iBM ((u : Bˣ) : B))⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← map_mul, ← Units.val_mul]
      simp
    have hinv : (iEM (iCE c))⁻¹ = iBM ((u⁻¹ : Bˣ) : B) := by rw [hinv', hcoe]
    have hmem : (iCE c)⁻¹ ∈ C := by
      rw [hC_iff, map_inv₀, hinv]
      exact ((u⁻¹ : Bˣ) : B).2
    refine ⟨⟨c, ⟨(iCE c)⁻¹, hmem⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show iCE c * iCE ⟨(iCE c)⁻¹, hmem⟩ = iCE (1 : C)
      rw [map_one]
      show iCE c * (iCE c)⁻¹ = 1
      exact mul_inv_cancel₀ hcE
    · apply Subtype.ext
      show iCE ⟨(iCE c)⁻¹, hmem⟩ * iCE c = iCE (1 : C)
      rw [map_one]
      show (iCE c)⁻¹ * iCE c = 1
      exact inv_mul_cancel₀ hcE
  haveI : IsLocalRing C := by
    refine { exists_pair_ne := ⟨0, 1, zero_ne_one⟩, isUnit_or_isUnit_of_add_one := ?_ }
    intro a b hab
    by_cases ha : IsUnit a
    · exact Or.inl ha
    · refine Or.inr ((hunit_iff b).mpr ?_)
      have hφa : φ a ∈ IsLocalRing.maximalIdeal B := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun h => ha ((hunit_iff a).mpr h)
      have hsum : φ a + φ b = 1 := by rw [← map_add, hab, map_one]
      have hone : (1 : B) ∉ IsLocalRing.maximalIdeal B := fun h =>
        (IsLocalRing.maximalIdeal.isMaximal B).ne_top (Ideal.eq_top_iff_one _ |>.mpr h)
      have hne : ¬ (1 - φ a ∈ IsLocalRing.maximalIdeal B) := by
        intro h
        apply hone
        rw [show (1 : B) = (1 - φ a) + φ a by ring]
        exact (IsLocalRing.maximalIdeal B).add_mem h hφa
      rw [show φ b = 1 - φ a by rw [← hsum]; ring]
      exact of_not_not fun h =>
        hne ((IsLocalRing.mem_maximalIdeal _).mpr ((mem_nonunits_iff).mpr h))
  have h𝔪C : IsLocalRing.maximalIdeal C = Ideal.comap φ (IsLocalRing.maximalIdeal B) := by
    ext c
    rw [IsLocalRing.mem_maximalIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff]
    exact (hunit_iff c).not
  -- ## 4. the element `ζ` as an element of `C`, and the basic arithmetic of `N`
  have hζE : ((ζ : B) : M) ∈ E := IntermediateField.mem_adjoin_simple_self ℚp ((ζ : B) : M)
  let ζE : E := ⟨((ζ : B) : M), hζE⟩
  have hζEeq : iEM ζE = ((ζ : B) : M) := rfl
  have hζCmem : ζE ∈ C := (hC_iff ζE).mpr (by rw [hζEeq]; exact ζ.2)
  let ζC : C := ⟨ζE, hζCmem⟩
  have hζCeq : iCE ζC = ζE := rfl
  have hpow : (ζC : C) ^ (Nat.card (IsLocalRing.ResidueField B) - 1) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hζ.pow_eq_one
  have hcard : Nat.card (IsLocalRing.ResidueField B) = p ^ Q.asIdeal.inertiaDeg (𝓞 ℚ) :=
    Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
      Q0 p (Fact.out) hmemA K Q hQ
  have hfpos : 0 < Q.asIdeal.inertiaDeg (𝓞 ℚ) := Q.asIdeal.inertiaDeg_pos (𝓞 ℚ)
  have hNpos : 0 < Nat.card (IsLocalRing.ResidueField B) - 1 := by
    rw [hcard]
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have : 1 < p ^ Q.asIdeal.inertiaDeg (𝓞 ℚ) := one_lt_pow₀ hp1 hfpos.ne'
    omega
  -- ## 5. the valuations of `p` and of `N`
  have hvalQp : Valued.v (R := ℚp) (Γ₀ := WithZero (Multiplicative ℤ)) ((p : ℚp)) =
      WithZero.exp (-1 : ℤ) := by
    have h : Valued.v (R := ℚp) (Γ₀ := WithZero (Multiplicative ℤ))
        (((p : ℤ) : ℚ) : ℚp) = WithZero.exp (-(padicValInt p (p : ℤ) : ℤ)) :=
      Commons.NumberTheory.NumberField.Completion.val_adicCompletion_intCast_eq_padicValInt
        Q0 p (Fact.out) hmemA (p : ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    rw [padicValInt.self (Fact.out : p.Prime).one_lt] at h
    simpa using h
  have hvalp : adicValExp Q ((p : M)) = (Q.asIdeal.ramificationIdx (𝓞 ℚ) : ℤ) := by
    have h := adicValExp_natCast p Q Q0 hQ0 hQ p (Fact.out : p.Prime).ne_zero
    rw [padicValNat_self] at h
    simpa using h
  have hvalpM : Valued.v (R := M) (Γ₀ := WithZero (Multiplicative ℤ)) ((p : M)) =
      WithZero.exp (-(Q.asIdeal.ramificationIdx (𝓞 ℚ) : ℤ)) := by
    have h := Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
      Q0 Q hQ (p : ℚp)
    rw [hvalQp, ← WithZero.exp_nsmul] at h
    have h2 : (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ) (p : ℚp) = (p : M) :=
      map_natCast _ p
    rw [h2] at h
    rw [h]
    congr 1
    simp [nsmul_eq_mul]
  have hpN : ¬ p ∣ Nat.card (IsLocalRing.ResidueField B) - 1 := by
    rw [hcard]
    intro h
    have hle : 1 ≤ p ^ Q.asIdeal.inertiaDeg (𝓞 ℚ) :=
      one_le_pow₀ (Fact.out : p.Prime).one_le
    have hint : ((((p ^ Q.asIdeal.inertiaDeg (𝓞 ℚ) - 1 : ℕ)) : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast h
    have hd : (((p ^ Q.asIdeal.inertiaDeg (𝓞 ℚ) - 1 : ℕ)) : ZMod p) = 0 := by
      simpa using hint
    rw [Nat.cast_sub hle, Nat.cast_pow, ZMod.natCast_self, zero_pow hfpos.ne', zero_sub] at hd
    have h1 : (1 : ZMod p) = 0 := by simpa using neg_eq_zero.mp hd
    exact one_ne_zero h1
  have hNval : adicValExp Q (((Nat.card (IsLocalRing.ResidueField B) - 1 : ℕ)) : M) = 0 := by
    have h := adicValExp_natCast p Q Q0 hQ0 hQ (Nat.card (IsLocalRing.ResidueField B) - 1)
      hNpos.ne'
    rw [padicValNat.eq_zero_of_not_dvd hpN] at h
    rw [h, mul_zero, Nat.cast_zero]
  have hNne : (((Nat.card (IsLocalRing.ResidueField B) - 1 : ℕ)) : M) ≠ 0 :=
    Nat.cast_ne_zero.mpr hNpos.ne'
  have hNunitB : IsUnit (((Nat.card (IsLocalRing.ResidueField B) - 1 : ℕ)) : B) := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    rw [show ((((Nat.card (IsLocalRing.ResidueField B) - 1 : ℕ)) : B) : M) =
        (((Nat.card (IsLocalRing.ResidueField B) - 1 : ℕ)) : M) from
      map_natCast (algebraMap B M) _]
    rw [← exp_neg_adicValExp Q hNne]
    rw [hNval, neg_zero, WithZero.exp_zero]
  have hNunitC : IsUnit (((Nat.card (IsLocalRing.ResidueField B) - 1 : ℕ)) : C) := by
    rw [hunit_iff]
    rw [hφ_nat]
    exact hNunitB
  -- ## 4b. the structural instances on `C` and on `E`
  haveI : CharZero ℚp := Commons.NumberTheory.NumberField.charZero_adicCompletion Q0
  haveI hEfin : Module.Finite ℚp E := by
    rw [show E = IntermediateField.adjoin ℚp {((ζ : B) : M)} from rfl]
    refine IntermediateField.adjoin.finiteDimensional (x := ((ζ : B) : M))
      ⟨Polynomial.X ^ (Nat.card (IsLocalRing.ResidueField B) - 1) - 1,
        Polynomial.monic_X_pow_sub_C 1 hNpos.ne', ?_⟩
    change Polynomial.aeval ((ζ : B) : M)
      (Polynomial.X ^ (Nat.card (IsLocalRing.ResidueField B) - 1) - 1) = 0
    rw [Polynomial.aeval_sub, Polynomial.aeval_one, Polynomial.aeval_X_pow, hζ.pow_eq_one,
      sub_self]
  haveI hIsInt : Algebra.IsIntegral ℚp E := ⟨fun y => IsIntegral.of_finite ℚp y⟩
  haveI hSep : Algebra.IsSeparable ℚp E := Algebra.IsSeparable.of_integral ℚp E
  haveI hFinC : Module.Finite ℤp C := IsIntegralClosure.finite ℤp ℚp E C
  haveI hEss : Algebra.EssFiniteType ℤp C := Algebra.EssFiniteType.of_finiteType ℤp C
  haveI hDedekind : IsDedekindDomain C := integralClosure.isDedekindDomain ℤp ℚp E
  have hCEinj : Function.Injective (algebraMap C E) := fun x y hxy => Subtype.ext hxy
  have hZEinj : Function.Injective (algebraMap ℤp E) := by
    intro x y hxy
    apply Subtype.ext
    exact (algebraMap ℚp E).injective hxy
  haveI hTF : Module.IsTorsionFree ℤp C :=
    Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr ?_
        have h1 : algebraMap ℤp C r * m = 0 := by rwa [Algebra.smul_def] at h
        have h2 : algebraMap C E (algebraMap ℤp C r) * algebraMap C E m = 0 := by
          have h3 := congrArg (fun z : C => algebraMap C E z) h1
          rwa [map_mul, map_zero] at h3
        have hrE : algebraMap C E (algebraMap ℤp C r) ≠ 0 := by
          intro h0
          refine hr ?_
          have h4 : algebraMap ℤp E r = 0 := by
            rwa [← IsScalarTower.algebraMap_apply ℤp C E r] at h0
          exact hZEinj (h4.trans (map_zero _).symm)
        exact hCEinj ((mul_eq_zero.mp h2).resolve_left hrE)
  -- ## 6. the different of `C` over `ℤp` is trivial
  have h𝔪ℤp : IsLocalRing.maximalIdeal ℤp = Ideal.span {(p : ℤp)} :=
    Commons.NumberTheory.NumberField.Completion.maximalIdeal_eq_span_of_valuation_eq_exp_neg_one
      (Valued.v : Valuation ℚp ℤᵐ⁰) hvalQp
  have hpNotUnitB : ¬ IsUnit ((p : B)) := by
    intro h
    have h1 : Valued.v ((p : B) : M) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp h
    rw [show (((p : B)) : M) = (p : M) from map_natCast (algebraMap B M) p] at h1
    rw [hvalpM,
      show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from WithZero.exp_zero.symm,
      WithZero.exp_inj] at h1
    have hzero : Q.asIdeal.ramificationIdx (𝓞 ℚ) = 0 := by omega
    exact (Ideal.ramificationIdx_pos (𝓞 ℚ) Q.asIdeal).ne' hzero
  have hpNotUnitC : ¬ IsUnit ((p : C)) := by
    intro h
    have h1 : IsUnit (φ (p : C)) := IsUnit.map φ.toMonoidHom h
    rw [hφ_nat] at h1
    exact hpNotUnitB h1
  haveI hlocHom : IsLocalHom (algebraMap ℤp C) :=
    ⟨fun a ha => by
      by_contra ha'
      have hmem : a ∈ IsLocalRing.maximalIdeal ℤp := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact ha'
      rw [h𝔪ℤp, Ideal.mem_span_singleton] at hmem
      obtain ⟨b, hb⟩ := hmem
      have hsplit : (p : C) * algebraMap ℤp C b = algebraMap ℤp C a := by
        rw [← map_natCast (algebraMap ℤp C) p, ← map_mul, ← hb]
      have h1 : IsUnit ((p : C) * algebraMap ℤp C b) := by rw [hsplit]; exact ha
      exact hpNotUnitC (isUnit_of_mul_isUnit' h1)⟩
  have hζunit : IsUnit (ζC : C) := by
    refine ⟨⟨ζC, (ζC) ^ (Nat.card (IsLocalRing.ResidueField B) - 1 - 1), ?_, ?_⟩, rfl⟩
    · rw [← pow_succ', Nat.sub_add_cancel hNpos, hpow]
    · rw [← pow_succ, Nat.sub_add_cancel hNpos, hpow]
  have hunit_prod : IsUnit (((Nat.card (IsLocalRing.ResidueField B) - 1 : ℕ) : C) *
      (ζC : C) ^ (Nat.card (IsLocalRing.ResidueField B) - 1 - 1)) := by
    refine IsUnit.mul hNunitC ?_
    exact IsUnit.pow _ hζunit
  have hderiv_unit : IsUnit ((Polynomial.aeval ζC) (Polynomial.derivative (minpoly ℤp ζC))) :=
    isUnit_aeval_derivative_minpoly_of_pow_eq_one (A := ℤp) (S := C) (x := ζC)
      (IsIntegralClosure.isIntegral ℤp E ζC)
      (Nat.card (IsLocalRing.ResidueField B) - 1) hpow hunit_prod
  have hgen : Algebra.adjoin ℚp {iCE ζC} = ⊤ := by
    rw [show iCE ζC = ζE from rfl]
    rw [← IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic (F := ℚp)
      (IsAlgebraic.of_finite ℚp ζE)]
    rw [eq_top_iff]
    intro y _
    have hmap : E ≤ (IntermediateField.adjoin ℚp ({ζE} : Set E)).map
        (IsScalarTower.toAlgHom ℚp E M) := by
      show IntermediateField.adjoin ℚp {((ζ : B) : M)} ≤ _
      rw [IntermediateField.adjoin_le_iff]
      intro z hz'
      rw [Set.mem_singleton_iff] at hz'
      rw [hz']
      exact ⟨ζE, IntermediateField.mem_adjoin_simple_self ℚp ζE, hζEeq⟩
    obtain ⟨z, hzmem, hzy⟩ := hmap (show ((algebraMap E M) y) ∈ (E : Set M) from y.2)
    rw [show z = y from (algebraMap E M).injective hzy] at hzmem
    exact hzmem
  have hdiffmem : (Polynomial.aeval ζC) (Polynomial.derivative (minpoly ℤp ζC)) ∈
      differentIdeal ℤp C :=
    aeval_derivative_mem_differentIdeal ℤp ℚp E ζC hgen
  have hdiff : differentIdeal ℤp C = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨u, hu⟩ := hderiv_unit
    have hy : y = (y * ↑u⁻¹) * (Polynomial.aeval ζC) (Polynomial.derivative (minpoly ℤp ζC)) := by
      rw [← hu, mul_assoc, Units.inv_mul, mul_one]
    rw [hy]
    exact Ideal.mul_mem_left _ _ hdiffmem
  -- ## 7. `𝔪_C = (p)`
  have hUnram : Algebra.IsUnramifiedAt ℤp (IsLocalRing.maximalIdeal C) := by
    rw [← not_dvd_differentIdeal_iff]
    intro hdvd
    rw [hdiff] at hdvd
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top
      (eq_top_iff.mpr (Ideal.dvd_iff_le.mp hdvd))
  haveI hloc : IsLocalization (IsLocalRing.maximalIdeal C).primeCompl C :=
    IsLocalization.of_le_isUnit fun x hx => by
      have hx' : ¬ (x ∈ IsLocalRing.maximalIdeal C) := hx
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx'
      exact of_not_not hx'
  have hFF : Algebra.FormallyUnramified ℤp C := by
    have e : Localization.AtPrime (IsLocalRing.maximalIdeal C) ≃ₐ[C] C :=
      IsLocalization.algEquiv (IsLocalRing.maximalIdeal C).primeCompl _ C
    exact (Algebra.FormallyUnramified.iff_of_equiv (e.restrictScalars ℤp)).mp hUnram
  have h𝔪Cspan : IsLocalRing.maximalIdeal C = Ideal.span {(p : C)} := by
    have hmain : (IsLocalRing.maximalIdeal ℤp).map (algebraMap ℤp C) = IsLocalRing.maximalIdeal C :=
      ((Algebra.FormallyUnramified.iff_map_maximalIdeal_eq).mp hFF).2
    rw [← hmain, h𝔪ℤp, Ideal.map_span, Set.image_singleton, map_natCast]
  -- ## 8. `C` is a discrete valuation ring with uniformiser `p`
  haveI hNoeth : IsNoetherianRing C := IsNoetherianRing.of_finite ℤp C
  have hp_notfield : ¬ IsField C := by
    intro hf
    have hbot : IsLocalRing.maximalIdeal C = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hf
    have hmem : (p : C) ∈ IsLocalRing.maximalIdeal C :=
      (IsLocalRing.mem_maximalIdeal _).mpr ((mem_nonunits_iff).mpr hpNotUnitC)
    rw [hbot] at hmem
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (Ideal.mem_bot.mp hmem)
  haveI hDVR : IsDiscreteValuationRing C := by
    rw [IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime]
    refine ⟨IsDedekindDomain.isPrincipalIdealRing C,
      IsLocalRing.maximalIdeal C, ⟨?_, (IsLocalRing.maximalIdeal.isMaximal C).isPrime⟩, ?_⟩
    · intro hbot
      exact hp_notfield ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot)
    · rintro Q ⟨hQne, hQprime⟩
      exact Ideal.IsMaximal.eq_of_le (Ideal.IsPrime.isMaximal hQprime hQne)
        (IsLocalRing.maximalIdeal.isMaximal C).ne_top
        (IsLocalRing.le_maximalIdeal hQprime.ne_top)
  have hpirr : Irreducible (p : C) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : C)).mpr h𝔪Cspan
  -- ## 9. the final value computation
  have hxC : (⟨x, hxE⟩ : E) ∈ C :=
    (hC_iff ⟨x, hxE⟩).mpr (by rw [show iEM (⟨x, hxE⟩ : E) = x from rfl]; exact hxB)
  set ξC : C := ⟨⟨x, hxE⟩, hxC⟩ with hξCdef
  have hξCval : iEM (iCE ξC) = x := rfl
  have hξCne : ξC ≠ 0 := by
    intro h0
    apply hx0
    have h1 : iEM (iCE ξC) = 0 := by rw [h0]; rfl
    rwa [hξCval] at h1
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hξCne hpirr
  refine ⟨(n : ℤ), ?_⟩
  have hx_eq : x = iBM (φ (u : C)) * (p : M) ^ n := by
    have h := congrArg (fun c : C => iEM (iCE c)) hu
    have h2 : iEM (iCE ((u : C) * (p : C) ^ n)) = iBM (φ (u : C)) * (p : M) ^ n := by
      rw [map_mul iCE, map_pow iCE, map_natCast iCE, map_mul iEM, map_pow iEM, map_natCast iEM]
      rw [show iEM (iCE (u : C)) = iBM (φ (u : C)) from (hφ_coe (u : C)).symm]
    rw [← h2]
    rwa [hξCval] at h
  rw [hx_eq]
  have hφu_unit : IsUnit (φ (u : C)) := IsUnit.map φ.toMonoidHom u.isUnit
  have hφu_val : Valued.v (R := M) (Γ₀ := WithZero (Multiplicative ℤ)) (iBM (φ (u : C))) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp
      hφu_unit
  have hpne : (p : M) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hφune : iBM (φ (u : C)) ≠ 0 := by
    intro h0
    rw [h0] at hφu_val
    simp at hφu_val
  rw [adicValExp_mul Q hφune (pow_ne_zero n hpne), adicValExp_pow Q hpne n]
  have h1 : adicValExp Q (iBM (φ (u : C))) = 0 := by
    rw [adicValExp, hφu_val, WithZero.log_one, neg_zero]
  rw [h1, hvalp]
  ring
end Work.SSGRoute.TatePoitouRoute.FinitenessHM
