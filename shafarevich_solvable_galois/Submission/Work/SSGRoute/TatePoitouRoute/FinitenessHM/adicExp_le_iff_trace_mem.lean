import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.ValExp
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicCompletionExp
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.count_different_le_count_different_of_algebra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local trace criterion for the exponent of the different

For a number field `K`, a rational prime `Q₀` of `𝓞 ℚ`, a prime `Q | Q₀` of `𝓞 K` and an element
`y` of the `Q`-adic completion `L = Q.adicCompletion K`, the trace of `y` against the ring of
integers `𝒪_L` of `L` lies in `ℤ_p = 𝒪_{ℚ_p}` precisely when the valuation of `y` is bounded by
`exp (adicLocExp Q₀ Q hQ)`:

`(∀ c ∈ 𝒪_L, Tr_{L/ℚ_p} (y * c) ∈ ℤ_p) ↔ v_L (y) ≤ exp (adicLocExp Q₀ Q hQ)`.

This is the trace-dual description of the inverse different: the trace dual
`{y : Tr(y·𝒪_L) ⊆ ℤ_p}` is the inverse of `differentIdeal ℤ_p 𝒪_L = 𝔪^{adicLocExp}`.

The proof decomposes into the general tools below:
`eq_maximalIdeal_pow_count_normalizedFactors`, `mem_one_fractionalIdeal_iff`,
`mem_dual_one_iff_forall_mem_differentIdeal`, `mem_dual_one_iff_forall_trace_mem`,
`forall_mul_mem_span_pow_iff` and `mul_uniformizer_pow_mem_iff`.
-/

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open IsDedekindDomain

open scoped nonZeroDivisors WithZero

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ## General tools

* `eq_maximalIdeal_pow_count_normalizedFactors`: in a discrete valuation ring `B`, a nonzero ideal
  is the `n`-th power of the maximal ideal, where `n` is the multiplicity of the maximal ideal in
  `normalizedFactors`;
* `mem_one_fractionalIdeal_iff`: membership in the unit fractional ideal is membership in `B`;
* `mem_dual_one_iff_forall_mem_differentIdeal`: the trace dual of the unit ideal is the inverse of
  the different ideal (Mathlib's `coeIdeal_differentIdeal` + `mem_inv_iff`);
* `mem_dual_one_iff_forall_trace_mem`: the trace dual of the unit ideal, in terms of the trace
  form against `B`;
* `forall_mul_mem_span_pow_iff`: testing a principal ideal `(π^n)` is testing `π^n`;
* `mul_uniformizer_pow_mem_iff`: `y * π^n` is integral iff `v y ≤ exp n`.
-/

/-- In a discrete valuation ring, a nonzero ideal is the power of the maximal ideal whose exponent
is the multiplicity of the maximal ideal in `normalizedFactors`. -/
theorem eq_maximalIdeal_pow_count_normalizedFactors {B : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsDedekindDomain B] {𝔡 : Ideal B} (h : 𝔡 ≠ ⊥) :
    𝔡 = IsLocalRing.maximalIdeal B ^
      (UniqueFactorizationMonoid.normalizedFactors 𝔡).count (IsLocalRing.maximalIdeal B) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (R := B) h hϖ
  have hmax : IsLocalRing.maximalIdeal B = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan0 : Ideal.span {ϖ} ≠ ⊥ := fun hc => hϖ.ne_zero (Ideal.span_singleton_eq_bot.mp hc)
  have hprime : Prime (Ideal.span {ϖ}) := by
    refine Ideal.prime_of_isPrime hspan0 ?_
    rw [← hmax]
    exact (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  rw [hk, hmax, ← Ideal.span_singleton_pow]
  congr 1
  classical
  haveI : Subsingleton (Ideal B)ˣ := ⟨fun a b => Units.ext (by
    rw [Ideal.isUnit_iff.mp a.isUnit, Ideal.isUnit_iff.mp b.isUnit])⟩
  rw [← Multiset.prod_replicate (a := Ideal.span {ϖ}) k,
    UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
      (m := Multiset.replicate k (Ideal.span {ϖ}))]
  · rw [Multiset.count_replicate_self]
  · intro p hp
    rw [Multiset.mem_replicate] at hp
    exact hp.2 ▸ hprime

/-- Membership in the unit fractional ideal, as a range condition. -/
theorem mem_one_fractionalIdeal_iff {B : Type*} {L : Type*} [CommRing B] [Field L]
    [Algebra B L] (x : L) :
    x ∈ (1 : FractionalIdeal (nonZeroDivisors B) L) ↔ x ∈ Set.range (algebraMap B L) := by
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one, Submodule.mem_one]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩

/-- **The trace dual of the unit ideal is the inverse of the different ideal.**  For an AKLB
extension `B/A` with fraction fields `L/F`, an element `y ∈ L` lies in the trace dual of `B`
precisely when it multiplies the different ideal `𝔡_{B/A}` into `B`. -/
theorem mem_dual_one_iff_forall_mem_differentIdeal {A F B L : Type*} [CommRing A] [Field F]
    [CommRing B] [Field L] [Algebra A F] [Algebra B L] [Algebra A B] [Algebra F L] [Algebra A L]
    [IsScalarTower A F L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A F]
    [FiniteDimensional F L] [Algebra.IsSeparable F L] [IsIntegralClosure B A L]
    [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    (y : L) :
    y ∈ FractionalIdeal.dual A F (1 : FractionalIdeal (nonZeroDivisors B) L) ↔
      ∀ d ∈ differentIdeal A B, y * algebraMap B L d ∈ Set.range (algebraMap B L) := by
  have h1 : (FractionalIdeal.dual A F (1 : FractionalIdeal (nonZeroDivisors B) L)) =
      ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L)⁻¹ := by
    rw [coeIdeal_differentIdeal A F L B, inv_inv]
  rw [h1]
  have hne0 : ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 := by
    rw [coeIdeal_differentIdeal A F L B]
    exact inv_ne_zero (FractionalIdeal.dual_ne_zero A F (by simp))
  rw [FractionalIdeal.mem_inv_iff hne0]
  constructor
  · intro h d hd
    have hd' : algebraMap B L d ∈
        ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L) :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors B)).mpr ⟨d, hd, rfl⟩
    exact (mem_one_fractionalIdeal_iff _).mp (h _ hd')
  · intro h e he
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors B)).mp he
    exact (mem_one_fractionalIdeal_iff _).mpr (h d hd)

/-- Membership in the trace dual of the unit ideal, in terms of the trace form against the ring
of integers. -/
theorem mem_dual_one_iff_forall_trace_mem {A F B L : Type*} [CommRing A] [Field F]
    [CommRing B] [Field L] [Algebra A F] [Algebra B L] [Algebra A B] [Algebra F L] [Algebra A L]
    [IsScalarTower A F L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A F]
    [FiniteDimensional F L] [Algebra.IsSeparable F L] [IsIntegralClosure B A L]
    [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B] (y : L) :
    y ∈ FractionalIdeal.dual A F (1 : FractionalIdeal (nonZeroDivisors B) L) ↔
      ∀ c : B, Algebra.trace F L (y * algebraMap B L c) ∈ Set.range (algebraMap A F) := by
  rw [FractionalIdeal.mem_dual (by simp)]
  constructor
  · intro h c
    have hc : algebraMap B L c ∈ (1 : FractionalIdeal (nonZeroDivisors B) L) :=
      (mem_one_fractionalIdeal_iff _).mpr ⟨c, rfl⟩
    have hmem := h _ hc
    rwa [Algebra.traceForm_apply] at hmem
  · intro h a ha
    obtain ⟨c, rfl⟩ := (mem_one_fractionalIdeal_iff _).mp ha
    rw [Algebra.traceForm_apply]
    exact h c

/-- Testing a principal ideal `(π ^ n)`: an element `y` multiplies every element of `(π ^ n)` into
`B` exactly when `y * π ^ n` is in `B` (both as subsets of `L`). -/
theorem forall_mul_mem_span_pow_iff {B : Type*} {L : Type*} [CommRing B] [Field L] [Algebra B L]
    (π : B) (n : ℕ) (y : L) :
    (∀ d : B, d ∈ Ideal.span {π ^ n} → y * algebraMap B L d ∈ Set.range (algebraMap B L)) ↔
      y * (algebraMap B L π) ^ n ∈ Set.range (algebraMap B L) := by
  constructor
  · intro h
    have hπn : (π ^ n : B) ∈ Ideal.span {π ^ n} := Ideal.mem_span_singleton_self _
    have hmem := h (π ^ n) hπn
    rwa [map_pow] at hmem
  · rintro ⟨z, hz⟩ d hd
    rw [Ideal.mem_span_singleton] at hd
    obtain ⟨c, rfl⟩ := hd
    refine ⟨z * c, ?_⟩
    rw [map_mul, map_mul, map_pow, hz]
    ring

/-- For a uniformiser `π` of a valuation ring `v.valuationSubring`, `y * π ^ n` is in the ring
exactly when `v y ≤ exp n`. -/
theorem mul_uniformizer_pow_mem_iff {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    {π : v.valuationSubring} (hπ : v (π : F) = WithZero.exp (-1 : ℤ)) (y : F) (n : ℕ) :
    y * (π : F) ^ n ∈ v.valuationSubring ↔ v y ≤ WithZero.exp (n : ℤ) := by
  have h3 : ((WithZero.exp (-1 : ℤ)) ^ n : ℤᵐ⁰) = WithZero.exp (-(n : ℤ)) := by
    rw [← WithZero.exp_nsmul]; congr 1; simp
  rw [Valuation.mem_valuationSubring_iff, map_mul, map_pow, hπ, h3,
    mul_comm (v y) (WithZero.exp (-(n : ℤ)))]
  have h2 : (WithZero.exp (-(n : ℤ)) : ℤᵐ⁰) * WithZero.exp (n : ℤ) = 1 := by
    rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  rw [← h2, mul_le_mul_iff_right₀ (WithZero.exp_pos (a := -(n : ℤ)))]

/-- **The local trace criterion for the exponent of the different.** -/
theorem adicExp_le_iff_trace_mem {K : Type*} [Field K] [NumberField K]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal) (y : Q.adicCompletion K) :
    letI : Algebra (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers
        Q0 Q hQ)
    letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
    ((∀ c : Q.adicCompletionIntegers K,
        Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K)
          (y * (c : Q.adicCompletion K))
        ∈ (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ)))
      ↔ Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) y
          ≤ WithZero.exp
            ((Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ : ℤ))) := by
  classical
  letI : Algebra (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
    RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers
      Q0 Q hQ)
  letI : Algebra (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
  letI : Algebra (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ).comp
      (Q0.adicCompletionIntegers ℚ).subtype)
  haveI hST1 : IsScalarTower (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)
      (Q.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hST2 : IsScalarTower (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)
      (Q.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hIC : IsIntegralClosure (Q.adicCompletionIntegers K) (Q0.adicCompletionIntegers ℚ)
      (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
      Q0 Q hQ
  haveI hFD : FiniteDimensional (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q0 Q hQ
  haveI hTF : Module.IsTorsionFree (Q0.adicCompletionIntegers ℚ)
      (Q.adicCompletionIntegers K) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr ?_
        have hinj : Function.Injective
            (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)) :=
          Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicCompletionMapIntegers_injective Q0 Q hQ
        have h1 : algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) r * m = 0 := by
          rwa [Algebra.smul_def] at h
        rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd (hinj (by rw [h2, map_zero])) hr
        · exact h2
  haveI hCZ : CharZero (Q0.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (Q0.adicCompletion ℚ)).injective
  haveI hPF : PerfectField (Q0.adicCompletion ℚ) := inferInstance
  haveI hAL : Algebra.IsAlgebraic (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI hSep : Algebra.IsSeparable (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨π, hπv, hπm⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one Q
  -- the different ideal is the `adicLocExp`-th power of the maximal ideal
  have hdne0 : ((differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :
      Ideal (Q.adicCompletionIntegers K)) :
      FractionalIdeal (nonZeroDivisors (Q.adicCompletionIntegers K)) (Q.adicCompletion K)) ≠ 0 := by
    rw [coeIdeal_differentIdeal (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)
      (Q.adicCompletion K) (Q.adicCompletionIntegers K)]
    exact inv_ne_zero (FractionalIdeal.dual_ne_zero (Q0.adicCompletionIntegers ℚ)
      (Q0.adicCompletion ℚ) (by simp))
  have hdne : differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) ≠ ⊥ := by
    intro h0
    exact hdne0 (by rw [h0, FractionalIdeal.coeIdeal_bot])
  have hadic : Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ =
      (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K))).count
        (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := rfl
  have hmaxpow : differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) =
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ^
        (Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ) := by
    rw [hadic]
    exact eq_maximalIdeal_pow_count_normalizedFactors
      (B := Q.adicCompletionIntegers K)
      (𝔡 := differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)) hdne
  have hdiff : differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) =
      Ideal.span {π ^ (Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ)} := by
    calc differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)
        = IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ^
            (Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ) := hmaxpow
      _ = Ideal.span {π} ^ (Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ) := by
            rw [hπm]
      _ = Ideal.span {π ^ (Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ)} := by
            rw [Ideal.span_singleton_pow]
  -- the left-hand side is the trace-dual condition, phrased as in the helper lemmas
  have hmem : ∀ z : Q0.adicCompletion ℚ,
      (z ∈ (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ))) ↔
      (z ∈ Set.range (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ))) := by
    intro z
    constructor
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨a, ha⟩
      have ha' : (a : Q0.adicCompletion ℚ) = z := ha
      rw [← ha']
      exact a.2
  have hcoe : ∀ c : Q.adicCompletionIntegers K,
      (c : Q.adicCompletion K) = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c :=
    fun c => rfl
  have hmemB : ∀ z : Q.adicCompletion K,
      (z ∈ (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))).valuationSubring) ↔
      (z ∈ Set.range (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K))) := by
    intro z
    constructor
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨a, ha⟩
      have ha' : (a : Q.adicCompletion K) = z := ha
      rw [← ha']
      exact a.2
  have step1 : (∀ c : Q.adicCompletionIntegers K,
        Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K)
          (y * (c : Q.adicCompletion K))
        ∈ (Q0.adicCompletionIntegers ℚ : Set (Q0.adicCompletion ℚ))) ↔
      (∀ c : Q.adicCompletionIntegers K,
        Algebra.trace (Q0.adicCompletion ℚ) (Q.adicCompletion K)
          (y * algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c)
        ∈ Set.range (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ))) := by
    simp only [hmem, hcoe]
  refine step1.trans ?_
  rw [← mem_dual_one_iff_forall_trace_mem (A := Q0.adicCompletionIntegers ℚ)
    (F := Q0.adicCompletion ℚ) (B := Q.adicCompletionIntegers K) (L := Q.adicCompletion K) y]
  rw [mem_dual_one_iff_forall_mem_differentIdeal (A := Q0.adicCompletionIntegers ℚ)
    (F := Q0.adicCompletion ℚ) (B := Q.adicCompletionIntegers K) (L := Q.adicCompletion K) y]
  rw [hdiff]
  rw [forall_mul_mem_span_pow_iff (B := Q.adicCompletionIntegers K) (L := Q.adicCompletion K)
    π (Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ) y]
  rw [← mul_uniformizer_pow_mem_iff
    (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))) hπv y
      (Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ)]
  simp only [hmemB, hcoe]

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
