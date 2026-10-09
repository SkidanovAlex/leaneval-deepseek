import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
import Submission.Commons.RingTheory.Norm.residue_norm_eq
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.NumberTheory.NumberField.Completion

/-! ## Auxiliary estimate for products -/

/-- **Valuation bound for the product expansion of `∏ (1 + yᵢ)`.**

Let `v` be a valuation on a field `F` with values in a linearly ordered commutative group with
zero `Γ₀`.  If `q ≤ 1` and `v (y i) ≤ q` for all `i ∈ s`, then the difference between
`∏_{i ∈ s} (1 + y i)` and its first-order expansion `1 + ∑_{i ∈ s} y i` has valuation at most
`q ^ 2`. -/
private theorem val_prod_one_add_sub_one_sub_sum_le {F : Type*} [Field F] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
    {ι : Type*} (s : Finset ι) (y : ι → F) {q : Γ₀}
    (hq : q ≤ 1) (hy : ∀ i ∈ s, v (y i) ≤ q) :
    v (∏ i ∈ s, (1 + y i) - 1 - ∑ i ∈ s, y i) ≤ q ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hy' : ∀ i ∈ t, v (y i) ≤ q := fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hya : v (y a) ≤ q := hy a (Finset.mem_insert_self a t)
    have hS : v (∑ i ∈ t, y i) ≤ q := v.map_sum_le hy'
    have hP : v (∏ i ∈ t, (1 + y i) - 1 - ∑ i ∈ t, y i) ≤ q ^ 2 := ih hy'
    have hone : v (1 + y a) ≤ 1 := v.map_add_le (g := 1) (by rw [map_one]) (hya.trans hq)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      show (1 + y a) * (∏ i ∈ t, (1 + y i)) - 1 - (y a + ∑ i ∈ t, y i)
        = y a * (∑ i ∈ t, y i) + (1 + y a) * (∏ i ∈ t, (1 + y i) - 1 - ∑ i ∈ t, y i)
        from by ring]
    have h1 : v (y a * (∑ i ∈ t, y i)) ≤ q ^ 2 := by
      rw [map_mul]
      calc v (y a) * v (∑ i ∈ t, y i) ≤ q * q := mul_le_mul' hya hS
        _ = q ^ 2 := (pow_two q).symm
    have h2 : v ((1 + y a) * (∏ i ∈ t, (1 + y i) - 1 - ∑ i ∈ t, y i)) ≤ q ^ 2 := by
      rw [map_mul]
      calc v (1 + y a) * v (∏ i ∈ t, (1 + y i) - 1 - ∑ i ∈ t, y i) ≤ 1 * q ^ 2 :=
            mul_le_mul' hone hP
        _ = q ^ 2 := one_mul _
    exact v.map_add_le (g := q ^ 2) h1 h2


/-! ## Compatibility of the field norm with the norm on the rings of integers -/

open IsDedekindDomain.HeightOneSpectrum

/-- The field norm `N_{L_q/K_Q}` of an element of the ring of integers of `L_q` is the image of
its norm over the ring of integers of `K_Q`. -/
private theorem norm_adicCompletionIntegers_eq {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (a : q.adicCompletionIntegers L) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
      RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
          (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
        (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
    Algebra.norm (Q.adicCompletion K) (a : q.adicCompletion L) =
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (Algebra.norm (Q.adicCompletionIntegers K) a) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
      (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers Q q hq
  haveI hfr : IsFractionRing (Q.adicCompletionIntegers K) (Q.adicCompletion K) := inferInstance
  haveI hic : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension Q q hq
  haveI : IsDomain (Q.adicCompletionIntegers K) := inferInstance
  haveI : IsDomain (q.adicCompletionIntegers L) := inferInstance
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.norm_localization (R := Q.adicCompletionIntegers K)
    (S := q.adicCompletionIntegers L) (Rₘ := Q.adicCompletion K) (Sₘ := q.adicCompletion L)
    (nonZeroDivisors (Q.adicCompletionIntegers K)) a



/-- The field trace `Tr_{L_q/K_Q}` of an element of the ring of integers of `L_q` is the image of
its trace over the ring of integers of `K_Q`. -/
private theorem trace_adicCompletionIntegers_eq {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (a : q.adicCompletionIntegers L) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
      RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
          (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
        (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
    Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (a : q.adicCompletion L) =
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) a) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
      (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers Q q hq
  haveI hfr : IsFractionRing (Q.adicCompletionIntegers K) (Q.adicCompletion K) := inferInstance
  haveI hic : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension Q q hq
  haveI : IsDomain (Q.adicCompletionIntegers K) := inferInstance
  haveI : IsDomain (q.adicCompletionIntegers L) := inferInstance
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.trace_localization (R := Q.adicCompletionIntegers K)
    (S := q.adicCompletionIntegers L) (Rₘ := Q.adicCompletion K) (Sₘ := q.adicCompletion L)
    (nonZeroDivisors (Q.adicCompletionIntegers K)) a

/-! ## Surjectivity of the norm on residue fields -/

open IsDedekindDomain.HeightOneSpectrum

/-- For an unramified prime `q | Q`, every unit of the ring of integers of `K_Q` is congruent
modulo the maximal ideal to the norm of an element of the ring of integers of `L_q`. -/
private theorem exists_norm_sub_lt_one_of_val_eq_one {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (y : Q.adicCompletion K) (hy : Valued.v y = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ a : q.adicCompletionIntegers L,
      Valued.v (Algebra.norm (Q.adicCompletion K) (a : q.adicCompletion L) - y) < 1 := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
      (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers Q q hq
  haveI hlies : Ideal.LiesOver (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers Q q hq
  haveI hloc : IsLocalHom (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)) :=
    inferInstance
  haveI hfiniteL : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L q
  have hyR : Valued.v y ≤ 1 := by rw [hy]
  let yR : Q.adicCompletionIntegers K := ⟨y, hyR⟩
  have hram := Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow Q q hq
  have hmap : Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
    rw [hram, hunr, pow_one]
  obtain ⟨α, hα⟩ := FiniteField.norm_surjective (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))
    (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) (IsLocalRing.residue _ yR)
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective α
  refine ⟨a, ?_⟩
  have hres := Commons.RingTheory.Norm.residue_norm_eq (R := Q.adicCompletionIntegers K)
    (S := q.adicCompletionIntegers L) hmap a
  have hresy : IsLocalRing.residue (Q.adicCompletionIntegers K)
      (Algebra.norm (Q.adicCompletionIntegers K) a) = IsLocalRing.residue _ yR := by
    rw [← hres, ha, hα]
  have hmem : Algebra.norm (Q.adicCompletionIntegers K) a - yR ∈
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hresy, sub_self]
  rw [norm_adicCompletionIntegers_eq Q q hq a]
  rw [show (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (Algebra.norm (Q.adicCompletionIntegers K) a) - y)
      = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (Algebra.norm (Q.adicCompletionIntegers K) a - yR) from by
    rw [map_sub]; rfl]
  exact (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
    Q (Algebra.norm (Q.adicCompletionIntegers K) a - yR)).mp hmem


/-! ## Compatibility of the residue with the trace -/

/-- The residue of a trace is the trace of the residue, in the unramified case
`𝔪_R S = 𝔪_S`. -/
private theorem residue_trace_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Free R S] [Module.Finite R S]
    (h : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (u : S) :
    Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (IsLocalRing.residue S u) =
      IsLocalRing.residue R (Algebra.trace R S u) := by
  have he : RingHom.comp (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
        ((RingEquiv.refl (R ⧸ IsLocalRing.maximalIdeal R)) :
          (R ⧸ IsLocalRing.maximalIdeal R) →+* (R ⧸ IsLocalRing.maximalIdeal R)) =
      RingHom.comp (Ideal.quotEquivOfEq h : (S ⧸ Ideal.map (algebraMap R S)
            (IsLocalRing.maximalIdeal R)) →+* (S ⧸ IsLocalRing.maximalIdeal S))
        (algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
          (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))) := by
    apply Ideal.Quotient.ringHom_ext
    ext y
    change algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (IsLocalRing.residue R y)
      = Ideal.quotEquivOfEq h (algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
          (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) y))
    rw [IsLocalRing.ResidueField.algebraMap_residue,
      Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.quotEquivOfEq_mk]
    rfl
  have key := Algebra.trace_eq_of_equiv_equiv
    (RingEquiv.refl (R ⧸ IsLocalRing.maximalIdeal R)) (Ideal.quotEquivOfEq h) he
    (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) u)
  rw [Algebra.trace_quotient_mk] at key
  exact key.symm

/-! ## Surjectivity of the trace modulo the maximal ideal -/

open IsDedekindDomain.HeightOneSpectrum

/-- For an unramified prime `q | Q`, the trace `Tr_{L_q/K_Q}` maps the ring of integers of `L_q`
onto the ring of integers of `K_Q` modulo the maximal ideal: every `c` in `𝓞 K_Q` is congruent
modulo `𝔪` to the trace of an element of `𝓞 L_q`. -/
private theorem exists_trace_sub_lt_one_of_ramificationIdx_eq_one {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (c : Q.adicCompletionIntegers K) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ a : q.adicCompletionIntegers L,
      Valued.v (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (a : q.adicCompletion L)
        - (c : Q.adicCompletion K)) < 1 := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
      (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers Q q hq
  haveI hlies : Ideal.LiesOver (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers Q q hq
  haveI hloc : IsLocalHom (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)) :=
    inferInstance
  haveI hfinR : Finite (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K Q
  haveI hfinL : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L q
  haveI hfr : IsFractionRing (Q.adicCompletionIntegers K) (Q.adicCompletion K) := inferInstance
  haveI hic : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension Q q hq
  haveI : IsDomain (Q.adicCompletionIntegers K) := inferInstance
  haveI : IsDomain (q.adicCompletionIntegers L) := inferInstance
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hram := Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow Q q hq
  have hmap : Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
    rw [hram, hunr, pow_one]
  have htrace_surj : Function.Surjective
      (Algebra.trace (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))
        (IsLocalRing.ResidueField (q.adicCompletionIntegers L))) :=
    Algebra.trace_surjective _ _
  obtain ⟨z, hz⟩ := htrace_surj (IsLocalRing.residue (Q.adicCompletionIntegers K) c)
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective z
  refine ⟨a, ?_⟩
  have hrt := residue_trace_eq hmap a
  have hres : IsLocalRing.residue (Q.adicCompletionIntegers K)
      (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) a) =
      IsLocalRing.residue (Q.adicCompletionIntegers K) c := by
    rw [← hrt, ha, hz]
  have hmem : Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) a - c ∈
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  rw [trace_adicCompletionIntegers_eq Q q hq a]
  have hsq : (c : Q.adicCompletion K)
      = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c := rfl
  rw [hsq, ← map_sub]
  exact (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
    Q (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) a - c)).mp hmem





/-! ## The product expansion of the norm at `1 + π^m a` -/

open IsDedekindDomain.HeightOneSpectrum

/-- **Expansion of the norm at `1 + π ^ m * a`.**

For `π` a uniformizer of `𝓞 K_Q` and `a` an element of `𝓞 L_q`, and `m ≥ 1`, the norm of
`1 + π ^ m * a` agrees with its first order expansion `1 + Tr(π ^ m * a)` up to an error of
valuation at most `e^{-2m}`. -/
private theorem norm_one_add_sub_one_sub_trace_le {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (π : Q.adicCompletionIntegers K)
    (hπ : Valued.v (π : Q.adicCompletion K) = WithZero.exp (-1))
    (m : ℕ) (hm : 1 ≤ m) (a : q.adicCompletionIntegers L) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Valued.v (Algebra.norm (Q.adicCompletion K)
          (1 + (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (π : Q.adicCompletion K)) ^ m
              * (a : q.adicCompletion L))
        - 1 - Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
            ((algebraMap (Q.adicCompletion K) (q.adicCompletion L) (π : Q.adicCompletion K)) ^ m
              * (a : q.adicCompletion L)))
      ≤ WithZero.exp (-(2 * m : ℤ)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  set πL : q.adicCompletion L :=
    algebraMap (Q.adicCompletion K) (q.adicCompletion L) (π : Q.adicCompletion K) with hπLdef
  set x : q.adicCompletion L := πL ^ m * (a : q.adicCompletion L) with hxdef
  have hnorm := Algebra.norm_eq_prod_automorphisms (Q.adicCompletion K) (1 + x)
  have htr := trace_eq_sum_automorphisms (K := Q.adicCompletion K) x
  have hkey : algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) (1 + x) - 1
          - Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) x)
      = (∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, (1 + σ x))
        - 1 - ∑ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ x := by
    rw [map_sub, map_sub, map_one, hnorm, htr]
    simp only [map_add, map_one]
  have hval : ∀ t : Q.adicCompletion K,
      Valued.v t = Valued.v (algebraMap (Q.adicCompletion K) (q.adicCompletion L) t) := by
    intro t
    change Valued.v t = Valued.v
      (Commons.RingTheory.Henselian.adicCompletionMap Q q hq t)
    rw [Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq t,
      hunr, pow_one]
  have hq1 : WithZero.exp (-(m : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hπL : Valued.v πL = WithZero.exp (-1) := by
    rw [hπLdef, ← hval (π : Q.adicCompletion K), hπ]
  have hπm : Valued.v (πL ^ m) = WithZero.exp (-(m : ℤ)) := by
    rw [map_pow, hπL]
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hbnd : ∀ σ ∈ (Finset.univ : Finset (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)),
      Valued.v (σ x) ≤ WithZero.exp (-(m : ℤ)) := by
    intro σ _
    have hσa : σ (a : q.adicCompletion L) ∈ q.adicCompletionIntegers L :=
      (algEquiv_mem_adicCompletionIntegers_iff_adicCompletion Q q hq σ (a : q.adicCompletion L)).mpr
        a.2
    have hva : Valued.v (σ (a : q.adicCompletion L)) ≤ 1 := hσa
    have hxσ : σ x = πL ^ m * σ (a : q.adicCompletion L) := by
      rw [hxdef, map_mul, map_pow]
      congr 1
      congr 1
      rw [hπLdef]
      exact σ.commutes (π : Q.adicCompletion K)
    rw [hxσ, map_mul, hπm]
    exact mul_le_of_le_one_right' hva
  have hprod := val_prod_one_add_sub_one_sub_sum_le
    (Valued.v : Valuation (q.adicCompletion L) (WithZero (Multiplicative ℤ)))
    (Finset.univ : Finset (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L))
    (fun σ => σ x) hq1 hbnd
  rw [hval (Algebra.norm (Q.adicCompletion K) (1 + x) - 1
    - Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) x), hkey]
  refine hprod.trans ?_
  rw [← WithZero.exp_nsmul]
  simp [two_mul]


/-! ## One step of the approximation -/

open IsDedekindDomain.HeightOneSpectrum

/-- **One Newton step towards writing a principal unit of `K_Q` as a norm.**

For `m ≥ 1`, `π` a uniformizer of `𝓞 K_Q` and `c ∈ 𝓞 K_Q`, there is `a ∈ 𝓞 L_q` such that
`N(1 + π ^ m a)` agrees with `1 + π ^ m c` up to valuation `e^{-(m+1)}`. -/
private theorem one_step {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (π : Q.adicCompletionIntegers K)
    (hπ : Valued.v (π : Q.adicCompletion K) = WithZero.exp (-1))
    (m : ℕ) (hm : 1 ≤ m) (c : Q.adicCompletionIntegers K) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ a : q.adicCompletionIntegers L,
      Valued.v ((1 + (π : Q.adicCompletion K) ^ m * (c : Q.adicCompletion K))
        - Algebra.norm (Q.adicCompletion K)
            (1 + (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (π : Q.adicCompletion K)) ^ m
              * (a : q.adicCompletion L)))
      ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  obtain ⟨a, ha⟩ := exists_trace_sub_lt_one_of_ramificationIdx_eq_one Q q hq hunr c
  refine ⟨a, ?_⟩
  set πL : q.adicCompletion L :=
    algebraMap (Q.adicCompletion K) (q.adicCompletion L) (π : Q.adicCompletion K) with hπLdef
  set u : q.adicCompletion L := 1 + πL ^ m * (a : q.adicCompletion L) with hudef
  have h5 := norm_one_add_sub_one_sub_trace_le Q q hq hunr π hπ m hm a
  rw [← hπLdef] at h5
  have hac : Valued.v (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
      (a : q.adicCompletion L) - (c : Q.adicCompletion K)) ≤ WithZero.exp (-1) :=
    (le_exp_neg_one_iff).mpr ha
  have htr : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (πL ^ m * (a : q.adicCompletion L))
      = (π : Q.adicCompletion K) ^ m *
        Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (a : q.adicCompletion L) := by
    have hpow : πL ^ m = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        ((π : Q.adicCompletion K) ^ m) := by rw [hπLdef, map_pow]
    rw [hpow, ← Algebra.smul_def]
    rw [(Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)).map_smul]
    rw [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
  have hπm : Valued.v ((π : Q.adicCompletion K) ^ m) = WithZero.exp (-(m : ℤ)) := by
    rw [map_pow, hπ]
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have h2 : Valued.v (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
        (πL ^ m * (a : q.adicCompletion L)) - (π : Q.adicCompletion K) ^ m * (c : Q.adicCompletion K))
      ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) := by
    rw [htr]
    rw [show (π : Q.adicCompletion K) ^ m *
          Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (a : q.adicCompletion L)
        - (π : Q.adicCompletion K) ^ m * (c : Q.adicCompletion K)
        = (π : Q.adicCompletion K) ^ m *
          (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (a : q.adicCompletion L)
            - (c : Q.adicCompletion K)) from by ring]
    rw [map_mul, hπm]
    refine (mul_le_mul' (le_refl _) hac).trans ?_
    rw [← WithZero.exp_add]
    exact WithZero.exp_le_exp.mpr (by omega)
  have h1 : Valued.v (Algebra.norm (Q.adicCompletion K) u - 1
      - Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (πL ^ m * (a : q.adicCompletion L)))
      ≤ WithZero.exp (-(2 * m : ℤ)) := h5
  have h1' : Valued.v (Algebra.norm (Q.adicCompletion K) u - 1
      - Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (πL ^ m * (a : q.adicCompletion L)))
      ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) :=
    h1.trans (WithZero.exp_le_exp.mpr (by omega))
  rw [(Valued.v).map_sub_swap]
  rw [show Algebra.norm (Q.adicCompletion K) u
        - (1 + (π : Q.adicCompletion K) ^ m * (c : Q.adicCompletion K))
      = (Algebra.norm (Q.adicCompletion K) u - 1
            - Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (πL ^ m * (a : q.adicCompletion L)))
          + (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (πL ^ m * (a : q.adicCompletion L))
            - (π : Q.adicCompletion K) ^ m * (c : Q.adicCompletion K)) from by ring]
  exact (Valued.v).map_add_le (g := WithZero.exp (-((m + 1 : ℕ) : ℤ))) h1' h2






/-! ## Every principal unit is a norm -/

open IsDedekindDomain.HeightOneSpectrum

/-- **Every principal unit of `K_Q` is the norm of an element of `L_q`** (unramified case). -/
private theorem exists_norm_eq_of_val_sub_one_le {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (z : Q.adicCompletion K) (hz : Valued.v (z - 1) ≤ WithZero.exp (-1)) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ x : q.adicCompletion L, Algebra.norm (Q.adicCompletion K) x = z := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  set ϖ : Q.adicCompletionIntegers K :=
    Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q with hϖdef
  have hϖ : Valued.v (ϖ : Q.adicCompletion K) = WithZero.exp (-1) :=
    Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q
  set ϖL : q.adicCompletion L :=
    algebraMap (Q.adicCompletion K) (q.adicCompletion L) (ϖ : Q.adicCompletion K) with hϖLdef
  have hvalmap : ∀ t : Q.adicCompletion K,
      Valued.v t = Valued.v (algebraMap (Q.adicCompletion K) (q.adicCompletion L) t) := by
    intro t
    change Valued.v t = Valued.v (Commons.RingTheory.Henselian.adicCompletionMap Q q hq t)
    rw [Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq t,
      hunr, pow_one]
  have hϖL : Valued.v ϖL = WithZero.exp (-1) := by
    rw [hϖLdef, ← hvalmap (ϖ : Q.adicCompletion K), hϖ]
  have hϖLpow : ∀ m : ℕ, Valued.v (ϖL ^ m) = WithZero.exp (-(m : ℤ)) := by
    intro m
    rw [map_pow, hϖL, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hϖpow : ∀ m : ℕ, Valued.v ((ϖ : Q.adicCompletion K) ^ m) = WithZero.exp (-(m : ℤ)) := by
    intro m
    rw [map_pow, hϖ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hϖ0 : (ϖ : Q.adicCompletion K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact (WithZero.exp_ne_zero (a := (-1 : ℤ))) hϖ.symm
  have hexp_neg : ∀ m : ℕ, (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ^ m
      = WithZero.exp (-(m : ℤ)) := by
    intro m
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hz1 : Valued.v z = 1 := by
    have hlt : Valued.v (z - 1) < Valued.v (1 : Q.adicCompletion K) := by
      rw [map_one]
      refine lt_of_le_of_lt hz ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    have h := Valuation.map_add_eq_of_lt_right (Valued.v) (x := z - 1)
      (y := (1 : Q.adicCompletion K)) hlt
    rw [map_one] at h
    simpa using h
  have htr_small : ∀ w : q.adicCompletionIntegers L,
      Valued.v (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
        (w : q.adicCompletion L)) ≤ 1 := by
    intro w
    rw [hvalmap (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (w : q.adicCompletion L)),
      trace_eq_sum_automorphisms (K := Q.adicCompletion K) (w : q.adicCompletion L)]
    refine Valuation.map_sum_le (v := Valued.v) (g := (1 : WithZero (Multiplicative ℤ))) ?_
    intro σ _
    exact (algEquiv_mem_adicCompletionIntegers_iff_adicCompletion Q q hq σ
      (w : q.adicCompletion L)).mpr w.2
  -- the recursion
  let P : ℕ → q.adicCompletionIntegers L × q.adicCompletionIntegers L → Prop := fun n p =>
    Valued.v (z - Algebra.norm (Q.adicCompletion K) (p.1 : q.adicCompletion L))
        ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) ∧
      Valued.v ((p.1 : q.adicCompletion L) - (p.2 : q.adicCompletion L))
        ≤ WithZero.exp (-(n : ℤ))
  have hbase : P 0 (1, 1) := by
    constructor
    · show Valued.v (z - Algebra.norm (Q.adicCompletion K)
          (((1, 1) : q.adicCompletionIntegers L × q.adicCompletionIntegers L).1 :
            q.adicCompletion L)) ≤ WithZero.exp (-(((0 + 1 : ℕ)) : ℤ))
      simpa using hz
    · show Valued.v ((((1, 1) : q.adicCompletionIntegers L × q.adicCompletionIntegers L).1 :
          q.adicCompletion L)
        - (((1, 1) : q.adicCompletionIntegers L × q.adicCompletionIntegers L).2 :
          q.adicCompletion L)) ≤ WithZero.exp (-(0 : ℤ))
      simp
  have hstep : ∀ (n : ℕ) (p : q.adicCompletionIntegers L × q.adicCompletionIntegers L),
      P n p → ∃ p' : q.adicCompletionIntegers L × q.adicCompletionIntegers L,
        p'.2 = p.1 ∧ P (n + 1) p' := by
    intro n p hp
    obtain ⟨hp1, -⟩ := hp
    set u : q.adicCompletionIntegers L := p.1 with hudef
    set Nu : Q.adicCompletion K := Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L)
      with hNudef
    have hp1' : Valued.v (z - Nu) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := hp1
    have hlt : Valued.v (z - Nu) < Valued.v z := by
      rw [hz1]
      refine lt_of_le_of_lt hp1' ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    have hNu : Valued.v Nu = 1 := by
      rcases lt_trichotomy (Valued.v z) (Valued.v Nu) with h | h | h
      · have hh := Valuation.map_sub_eq_of_lt_right (Valued.v) (x := z) (y := Nu) h
        rw [hh] at hlt
        exact absurd (h.trans hlt) (lt_irrefl _)
      · exact h.symm.trans hz1
      · have hh := Valuation.map_sub_eq_of_lt_left (Valued.v) (x := z) (y := Nu) h
        rw [hh] at hlt
        exact absurd hlt (lt_irrefl _)
    have hNuz : Nu ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hNu
      exact zero_ne_one hNu
    have hnum : Valued.v ((z - Nu) / ((ϖ : Q.adicCompletion K) ^ (n + 1))) ≤ 1 := by
      rw [Valuation.map_div, hϖpow (n + 1)]
      exact div_le_one_of_le₀ hp1' zero_le
    set d : Q.adicCompletionIntegers K :=
      ⟨(z - Nu) / ((ϖ : Q.adicCompletion K) ^ (n + 1)), hnum⟩ with hddef
    have hc : Valued.v ((d : Q.adicCompletion K) / Nu) ≤ 1 := by
      rw [Valuation.map_div, hNu, div_one]
      exact d.2
    set c : Q.adicCompletionIntegers K := ⟨(d : Q.adicCompletion K) / Nu, hc⟩ with hcdef
    obtain ⟨a, ha⟩ := one_step Q q hq hunr ϖ hϖ (n + 1) (by omega) c
    have hnum' : (1 : Q.adicCompletion K) + (ϖ : Q.adicCompletion K) ^ (n + 1)
        * (c : Q.adicCompletion K) = z / Nu := by
      simp only [c, d]
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      field_simp
      ring
    have hwu : Valued.v ((1 : q.adicCompletion L) + ϖL ^ (n + 1)
        * (a : q.adicCompletion L)) ≤ 1 := by
      have hle : Valued.v (ϖL ^ (n + 1) * (a : q.adicCompletion L))
          ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
        rw [map_mul, hϖLpow (n + 1)]
        calc WithZero.exp (-((n + 1 : ℕ) : ℤ)) * Valued.v (a : q.adicCompletion L)
            ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) * 1 := mul_le_mul' (le_refl _) a.2
          _ = WithZero.exp (-((n + 1 : ℕ) : ℤ)) := mul_one _
      have hx_lt : Valued.v (ϖL ^ (n + 1) * (a : q.adicCompletion L))
          < Valued.v (1 : q.adicCompletion L) := by
        rw [map_one]
        refine lt_of_le_of_lt hle ?_
        rw [← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by omega)
      rw [Valuation.map_add_eq_of_lt_left (Valued.v) (x := (1 : q.adicCompletion L))
        (y := ϖL ^ (n + 1) * (a : q.adicCompletion L)) hx_lt, map_one]
    set wu : q.adicCompletionIntegers L :=
      ⟨1 + ϖL ^ (n + 1) * (a : q.adicCompletion L), hwu⟩ with hwudef
    have hwu_coe : (wu : q.adicCompletion L)
        = 1 + ϖL ^ (n + 1) * (a : q.adicCompletion L) := rfl
    have hwu_sub : (wu : q.adicCompletion L) - 1
        = ϖL ^ (n + 1) * (a : q.adicCompletion L) := by
      rw [hwu_coe]; ring
    refine ⟨(u * wu, u), rfl, ?_, ?_⟩
    · show Valued.v (z - Algebra.norm (Q.adicCompletion K)
          ((u * wu : q.adicCompletionIntegers L) : q.adicCompletion L))
        ≤ WithZero.exp (-((n + 1 + 1 : ℕ) : ℤ))
      have hcoemu : ((u * wu : q.adicCompletionIntegers L) : q.adicCompletion L)
          = (u : q.adicCompletion L) * wu := by push_cast; ring
      rw [hcoemu, hwu_coe, map_mul]
      have ha' : Valued.v (z / Nu - Algebra.norm (Q.adicCompletion K)
          (1 + ϖL ^ (n + 1) * (a : q.adicCompletion L))) ≤
          WithZero.exp (-((n + 1 + 1 : ℕ) : ℤ)) := by
        rw [← hnum']
        exact ha
      rw [show z - Nu * Algebra.norm (Q.adicCompletion K)
            (1 + ϖL ^ (n + 1) * (a : q.adicCompletion L))
          = Nu * (z / Nu - Algebra.norm (Q.adicCompletion K)
            (1 + ϖL ^ (n + 1) * (a : q.adicCompletion L))) from by
        rw [mul_sub, mul_div_cancel₀ _ hNuz]]
      rw [map_mul, hNu, one_mul]
      exact ha'
    · show Valued.v (((u * wu : q.adicCompletionIntegers L) :
          q.adicCompletion L) - (u : q.adicCompletion L)) ≤
        WithZero.exp (-(((n + 1 : ℕ)) : ℤ))
      have hcoemu : ((u * wu : q.adicCompletionIntegers L) : q.adicCompletion L)
          = (u : q.adicCompletion L) * wu := by push_cast; ring
      rw [hcoemu]
      rw [show (u : q.adicCompletion L) * wu - (u : q.adicCompletion L)
          = (u : q.adicCompletion L) * (wu - 1) from by ring]
      rw [hwu_sub, map_mul, map_mul, hϖLpow (n + 1)]
      refine (mul_le_mul' u.2 (mul_le_mul' (le_refl _) a.2)).trans ?_
      simp
  let motive : ℕ → Type _ := fun n =>
    {p : q.adicCompletionIntegers L × q.adicCompletionIntegers L // P n p}
  let stepF : (n : ℕ) → motive n → motive (n + 1) := fun n p =>
    ⟨Classical.choose (hstep n p.1 p.2), (Classical.choose_spec (hstep n p.1 p.2)).2⟩
  let g : (n : ℕ) → motive n := Nat.rec ⟨(1, 1), hbase⟩ stepF
  let u : ℕ → q.adicCompletionIntegers L := fun n => (g n).1.1
  have hu_norm : ∀ n : ℕ,
      Valued.v (z - Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L))
      ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := fun n => (g n).2.1
  have hg_prev : ∀ n : ℕ, (g (n + 1)).1.2 = u n := by
    intro n
    exact (Classical.choose_spec (hstep n (g n).1 (g n).2)).1
  have hu_diff : ∀ n : ℕ, Valued.v ((u (n + 1) : q.adicCompletion L) - (u n : q.adicCompletion L))
      ≤ WithZero.exp (-(((n + 1 : ℕ)) : ℤ)) := by
    intro n
    have h := (g (n + 1)).2.2
    rw [hg_prev n] at h
    exact h
  have hcompat : ∀ n m : ℕ, m ≤ n →
      Valued.v ((u n : q.adicCompletion L) - (u m : q.adicCompletion L))
        ≤ WithZero.exp (-(m : ℤ)) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      obtain rfl : m = 0 := Nat.le_zero.mp hm
      simp
    | succ n ih =>
      intro m hm
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · simp
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        have h1 := ih m hmn
        have h2 := hu_diff n
        rw [show (u (n + 1) : q.adicCompletion L) - (u m : q.adicCompletion L)
            = ((u (n + 1) : q.adicCompletion L) - (u n : q.adicCompletion L))
              + ((u n : q.adicCompletion L) - (u m : q.adicCompletion L)) from by ring]
        refine (Valuation.map_add_le (Valued.v) (g := WithZero.exp (-(m : ℤ)))
          (le_of_lt (lt_of_le_of_lt h2 ?_)) h1)
        rw [WithZero.exp_lt_exp]
        omega
  have hmem_iff : ∀ (x : q.adicCompletionIntegers L) (m : ℕ),
      x ∈ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ m ↔
        Valued.v (x : q.adicCompletion L) ≤ WithZero.exp (-(m : ℤ)) := by
    intro x m
    rw [Commons.RingTheory.Henselian.mem_pow_maximalIdeal_iff]
    have hkey : Valued.v ((algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L))
        (Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q)) = WithZero.exp (-1) :=
      Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one q
    have hkey2 : Valued.v ((algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)) x)
        = Valued.v (x : q.adicCompletion L) := rfl
    rw [hkey, hkey2, hexp_neg m]
  obtain ⟨ell, hL⟩ := (Commons.RingTheory.Henselian.isPrecomplete_adicCompletionIntegers
    (R := 𝓞 L) (K := L) q).prec' (fun n => u n) (by
      intro m n hmn
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, hmem_iff]
      rw [show ((u m - u n : q.adicCompletionIntegers L) : q.adicCompletion L)
          = -((u n : q.adicCompletion L) - (u m : q.adicCompletion L)) from by push_cast; ring,
        Valuation.map_neg]
      exact hcompat n m hmn)
  have hLdiff : ∀ n : ℕ, Valued.v ((u n : q.adicCompletion L) - (ell : q.adicCompletion L))
      ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    have h := hL n
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, hmem_iff] at h
    rw [show ((u n - ell : q.adicCompletionIntegers L) : q.adicCompletion L)
        = (u n : q.adicCompletion L) - (ell : q.adicCompletion L) from by push_cast; ring] at h
    exact h
  have hvu : ∀ n : ℕ, Valued.v (u n : q.adicCompletion L) = 1 := by
    intro n
    have hb : Valued.v (u n : q.adicCompletion L) ≤ 1 := (u n).2
    have hN1 : Valued.v (Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L)) = 1 := by
      have h := hu_norm n
      have hlt : Valued.v (z - Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L))
          < Valued.v z := by
        rw [hz1]
        refine lt_of_le_of_lt h ?_
        rw [← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by omega)
      rcases lt_trichotomy (Valued.v z)
        (Valued.v (Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L))) with hh | hh | hh
      · have h2 := Valuation.map_sub_eq_of_lt_right (Valued.v) (x := z)
          (y := Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L)) hh
        rw [h2] at hlt
        exact absurd (hh.trans hlt) (lt_irrefl _)
      · exact hh.symm.trans hz1
      · have h2 := Valuation.map_sub_eq_of_lt_left (Valued.v) (x := z)
          (y := Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L)) hh
        rw [h2] at hlt
        exact absurd hlt (lt_irrefl _)
    rcases lt_trichotomy (Valued.v (u n : q.adicCompletion L)) 1 with h | h | h
    · exfalso
      have hpow := Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
        Q q hq (u n : q.adicCompletion L)
      rw [← hvalmap (Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L))] at hpow
      rw [hN1] at hpow
      have hlt : Valued.v (u n : q.adicCompletion L) ^
          Module.finrank (Q.adicCompletion K) (q.adicCompletion L) < 1 :=
        pow_lt_one₀ zero_le h
          (Module.finrank_pos (R := Q.adicCompletion K) (M := q.adicCompletion L)).ne'
      exact absurd (hpow ▸ hlt) (lt_irrefl _)
    · exact h
    · exact absurd hb (not_le_of_gt h)
  refine ⟨(ell : q.adicCompletion L), ?_⟩
  have key : ∀ n : ℕ, Valued.v (z - Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L))
      ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hb : Valued.v (z - Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L))
          ≤ 1 := by
        have h1 : Valued.v z ≤ 1 := by rw [hz1]
        have h2 : Valued.v (Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L))
            ≤ 1 := by
          rw [hvalmap (Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L)),
            Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow Q q hq
              (ell : q.adicCompletion L)]
          exact pow_le_one₀ zero_le ell.2
        simpa using (Valuation.map_sub_le (Valued.v) (g := (1 : WithZero (Multiplicative ℤ)))
          h1 h2)
      simpa using hb
    · have hun1 : Valued.v (u n : q.adicCompletion L) = 1 := hvu n
      have hNu1 : Valued.v (Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L)) = 1 := by
        rw [hvalmap (Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L)),
          Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow Q q hq
            (u n : q.adicCompletion L), hun1]
        simp
      have hδ : Valued.v ((u n : q.adicCompletion L) - (ell : q.adicCompletion L))
          ≤ WithZero.exp (-(n : ℤ)) := hLdiff n
      have hδ' : Valued.v ((ell : q.adicCompletion L) - (u n : q.adicCompletion L))
          ≤ WithZero.exp (-(n : ℤ)) := by
        rw [Valuation.map_sub_swap]; exact hδ
      have hδS : Valued.v ((ell : q.adicCompletion L) - (u n : q.adicCompletion L)) ≤ 1 := by
        refine le_trans hδ' ?_
        rw [← WithZero.exp_zero]
        exact WithZero.exp_le_exp.mpr (by simp)
      have hun0 : (u n : q.adicCompletion L) ≠ 0 := by
        intro h0; rw [h0, map_zero] at hun1; exact zero_ne_one hun1
      have hδuv : Valued.v (((ell : q.adicCompletion L) - (u n : q.adicCompletion L))
          / (u n : q.adicCompletion L)) ≤ WithZero.exp (-(n : ℤ)) := by
        rw [Valuation.map_div, hun1, div_one]; exact hδ'
      have hδuS : Valued.v (((ell : q.adicCompletion L) - (u n : q.adicCompletion L))
          / (u n : q.adicCompletion L)) ≤ 1 := by
        refine le_trans hδuv ?_
        rw [← WithZero.exp_zero]
        exact WithZero.exp_le_exp.mpr (by simp)
      set δu : q.adicCompletionIntegers L :=
        ⟨((ell : q.adicCompletion L) - (u n : q.adicCompletion L)) / (u n : q.adicCompletion L),
          hδuS⟩ with hδudef
      have hδu_coe : (δu : q.adicCompletion L)
          = ((ell : q.adicCompletion L) - (u n : q.adicCompletion L))
            / (u n : q.adicCompletion L) := rfl
      have hϖLn0 : ϖL ^ n ≠ 0 := by
        intro h0
        have hh := hϖLpow n
        rw [h0, map_zero] at hh
        exact (WithZero.exp_ne_zero (a := -(n : ℤ))) hh.symm
      have haS : Valued.v ((δu : q.adicCompletion L) / ϖL ^ n) ≤ 1 := by
        rw [Valuation.map_div, hϖLpow n]
        exact div_le_one_of_le₀ hδuv zero_le
      set a : q.adicCompletionIntegers L := ⟨(δu : q.adicCompletion L) / ϖL ^ n, haS⟩ with hadef
      have ha_coe : (a : q.adicCompletion L) = (δu : q.adicCompletion L) / ϖL ^ n := rfl
      have hδueq : (δu : q.adicCompletion L) = ϖL ^ n * (a : q.adicCompletion L) := by
        rw [ha_coe, div_eq_mul_inv, mul_comm]
        field_simp
      have h5 := norm_one_add_sub_one_sub_trace_le Q q hq hunr ϖ hϖ n hn a
      have h5' : Valued.v (Algebra.norm (Q.adicCompletion K)
          (1 + ϖL ^ n * (a : q.adicCompletion L)) - 1
          - Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
              (ϖL ^ n * (a : q.adicCompletion L))) ≤ WithZero.exp (-(2 * n : ℤ)) := h5
      have htrval : Valued.v ((ϖ : Q.adicCompletion K) ^ n *
          Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (a : q.adicCompletion L))
          ≤ WithZero.exp (-(n : ℤ)) := by
        rw [map_mul, hϖpow n]
        refine (mul_le_mul' (le_refl _) (htr_small a)).trans ?_
        rw [mul_one]
      have htr' : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
          (ϖL ^ n * (a : q.adicCompletion L))
          = (ϖ : Q.adicCompletion K) ^ n *
            Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (a : q.adicCompletion L) := by
        have hpow : ϖL ^ n = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            ((ϖ : Q.adicCompletion K) ^ n) := by rw [hϖLdef, map_pow]
        rw [hpow, ← Algebra.smul_def]
        rw [(Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)).map_smul]
        rw [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
      have hsmall : Valued.v (Algebra.norm (Q.adicCompletion K)
          (1 + (δu : q.adicCompletion L)) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
        rw [hδueq]
        have h5r := h5'
        rw [htr'] at h5r
        rw [show Algebra.norm (Q.adicCompletion K) (1 + ϖL ^ n * (a : q.adicCompletion L)) - 1
            = (Algebra.norm (Q.adicCompletion K) (1 + ϖL ^ n * (a : q.adicCompletion L)) - 1
                - (ϖ : Q.adicCompletion K) ^ n * Algebra.trace (Q.adicCompletion K)
                    (q.adicCompletion L) (a : q.adicCompletion L))
              + (ϖ : Q.adicCompletion K) ^ n * Algebra.trace (Q.adicCompletion K)
                  (q.adicCompletion L) (a : q.adicCompletion L) from by ring]
        exact Valuation.map_add_le (Valued.v) (g := WithZero.exp (-(n : ℤ)))
          (h5r.trans (WithZero.exp_le_exp.mpr (by omega))) htrval
      have hLun : (ell : q.adicCompletion L)
          = (u n : q.adicCompletion L) * (1 + (δu : q.adicCompletion L)) := by
        rw [hδu_coe]
        field_simp
        ring
      have hNL : Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L)
          = Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L)
            * Algebra.norm (Q.adicCompletion K) (1 + (δu : q.adicCompletion L)) := by
        rw [hLun, map_mul]
      rw [hNL]
      rw [show z - Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L)
            * Algebra.norm (Q.adicCompletion K) (1 + (δu : q.adicCompletion L))
          = (z - Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L))
            + Algebra.norm (Q.adicCompletion K) (u n : q.adicCompletion L)
              * (1 - Algebra.norm (Q.adicCompletion K) (1 + (δu : q.adicCompletion L)))
          from by ring]
      rw [show (1 : Q.adicCompletion K) - Algebra.norm (Q.adicCompletion K)
            (1 + (δu : q.adicCompletion L))
          = -(Algebra.norm (Q.adicCompletion K) (1 + (δu : q.adicCompletion L)) - 1)
          from by ring]
      refine Valuation.map_add_le (Valued.v) (g := WithZero.exp (-(n : ℤ))) ?_ ?_
      · exact (hu_norm n).trans (WithZero.exp_le_exp.mpr (by omega))
      · rw [map_mul, Valuation.map_neg, hNu1, one_mul]
        exact hsmall
  by_contra hne
  have hw : z - Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hne)
  have hpos : Valued.v (z - Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hw
  set k : ℤ := (Valued.v (z - Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L))).log
    with hk
  have hvk : Valued.v (z - Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L))
      = WithZero.exp k := (WithZero.exp_log hpos).symm
  have hle : ∀ n : ℕ, k ≤ -((n : ℕ) : ℤ) := by
    intro n
    have h := key n
    rw [hvk] at h
    exact WithZero.exp_le_exp.mp h
  have hcontra := hle (Int.natAbs (-k) + 1)
  omega


theorem norm_units_surjective_of_ramificationIdx_eq_one {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ y : Q.adicCompletion K,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) y = 1 →
      ∃ x : q.adicCompletion L, Algebra.norm (Q.adicCompletion K) x = y := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro y hy
  obtain ⟨a₀, ha₀⟩ := exists_norm_sub_lt_one_of_val_eq_one Q q hq hunr y hy
  have hN0 : Valued.v (Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L)) = 1 := by
    have hylt : Valued.v (Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L) - y)
        < Valued.v y := by
      rw [hy]; exact ha₀
    rcases lt_trichotomy (Valued.v (Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L)))
      (Valued.v y) with h | h | h
    · have hh := Valuation.map_sub_eq_of_lt_right (Valued.v)
        (x := Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L)) (y := y) h
      rw [hh] at hylt
      exact absurd (hh ▸ hylt) (lt_irrefl _)
    · exact h.trans hy
    · have hh := Valuation.map_sub_eq_of_lt_left (Valued.v)
        (x := Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L)) (y := y) h
      rw [hh] at hylt
      exact absurd (h.trans (hh ▸ hylt)) (lt_irrefl _)
  have hN0ne : Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN0
    exact zero_ne_one hN0
  have hz : Valued.v (y / Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L) - 1)
      ≤ WithZero.exp (-1) := by
    have h1 : Valued.v (y - Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L))
        ≤ WithZero.exp (-1) := by
      rw [show y - Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L)
          = -(Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L) - y) from by ring,
        Valuation.map_neg]
      exact le_exp_neg_one_iff.mpr ha₀
    rw [show y / Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L) - 1
        = (y - Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L))
          / Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L) from by
      field_simp]
    rw [Valuation.map_div, hN0, div_one]
    exact h1
  obtain ⟨x, hx⟩ := exists_norm_eq_of_val_sub_one_le Q q hq hunr
    (y / Algebra.norm (Q.adicCompletion K) (a₀ : q.adicCompletion L)) hz
  refine ⟨x * (a₀ : q.adicCompletion L), ?_⟩
  rw [map_mul, hx]
  exact div_mul_cancel₀ y hN0ne

end Commons.NumberTheory.NumberField.Completion
