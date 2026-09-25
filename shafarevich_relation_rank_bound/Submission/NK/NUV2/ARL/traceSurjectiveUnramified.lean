import Mathlib
import Submission.NK.NUV2.ARL.CommonsBridge

/-!
# Surjectivity of the trace on the rings of integers of an unramified local extension

Let `L / K` be a finite extension of number fields (no Galois hypothesis), `Q` a height-one
prime of `𝓞 K` and `q` a height-one prime of `𝓞 L` lying over `Q`, with ramification index
`e (q | Q) = 1`.  Writing `K_Q` for the `Q`-adic completion of `K` and `L_q` for the
`q`-adic completion of `L`, the extension `L_q / K_Q` is unramified, hence its different is
trivial, hence the trace `Tr_{L_q / K_Q}` maps the ring of integers `𝒪_{L_q}` **onto** the
ring of integers `𝒪_{K_Q}`.

The main result is `NK.NUV2.ARL.traceSurjectiveUnramified`.

The commons library proves the analogous statement
`Commons.NumberTheory.NumberField.Completion.trace_adicCompletionIntegers_surjective_of_ramificationIdx_eq_one`
under the additional hypothesis `[IsGalois K L]`; its proof, however, never uses the Galois
hypothesis.  The proof below repeats that argument without it: the ring of integers
`q.adicCompletionIntegers L` is a finite free `Q.adicCompletionIntegers K`-module, the trace
`Tr (𝒪_{L_q})` is an ideal of the discrete valuation ring `𝒪_{K_Q}`, and reducing modulo the
maximal ideal turns `Tr` into the field trace of the *residue* extension `κ_L / κ_R`, which is
finite separable (finite fields are perfect) and hence surjective; surjectivity mod `𝔪` of an
ideal of a local ring forces the ideal to be the whole ring.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace NK.NUV2.ARL

attribute [local instance] Ideal.Quotient.field

/-- **Surjectivity of the trace on the rings of integers (unramified case, no Galois
hypothesis).**

Let `q` lie over `Q` with ramification index one.  Then every element of the ring of integers
`Q.adicCompletionIntegers K` is the trace of an element of the ring of integers
`q.adicCompletionIntegers L`. -/
theorem traceSurjectiveUnramified {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ c : Q.adicCompletionIntegers K, ∃ s : q.adicCompletionIntegers L,
      Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) =
      (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) c : Q.adicCompletion K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hfree : Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers Q q hq
  haveI hfin : Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers Q q hq
  haveI hST : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletionIntegers_adicCompletion
      Q q hq
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K)
      (q.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : IsFractionRing (Q.adicCompletionIntegers K) (Q.adicCompletion K) := inferInstance
  haveI : IsFractionRing (q.adicCompletionIntegers L) (q.adicCompletion L) := inferInstance
  have hmax : Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
    have h :=
      Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow Q q hq
    rw [hunr, pow_one] at h
    exact h
  have trace_eq : ∀ x : q.adicCompletionIntegers L,
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
          (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x) =
      Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
        (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) x) := by
    intro x
    rw [← Algebra.intTrace_eq_trace (A := Q.adicCompletionIntegers K)
      (B := q.adicCompletionIntegers L)]
    exact Algebra.algebraMap_intTrace (A := Q.adicCompletionIntegers K)
      (B := q.adicCompletionIntegers L) (K := Q.adicCompletion K) (L := q.adicCompletion L) x
  let J : Ideal (q.adicCompletionIntegers L) :=
    Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
  have hJ : J = IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := hmax
  haveI : J.IsMaximal := by rw [hJ]; infer_instance
  haveI hfK : Finite (Q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := by
    obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists Q
    haveI : Finite (𝓞 K ⧸ Q.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
    exact Finite.of_equiv (𝓞 K ⧸ Q.asIdeal) e.symm.toEquiv
  haveI hfL : Finite (q.adicCompletionIntegers L ⧸ J) := by
    obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists q
    haveI : Finite (𝓞 L ⧸ q.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q
    exact Finite.of_equiv (𝓞 L ⧸ q.asIdeal) (e.symm.trans (Ideal.quotEquivOfEq hJ).symm).toEquiv
  haveI : Module.Finite (Q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) (q.adicCompletionIntegers L ⧸ J) :=
    Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (Q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) (q.adicCompletionIntegers L ⧸ J) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : PerfectField (Q.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := PerfectField.ofFinite
  have hT : ∀ c : Q.adicCompletionIntegers K, ∃ x : q.adicCompletionIntegers L,
      Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x - c ∈
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
    intro c
    obtain ⟨ybar, hy⟩ := Algebra.trace_surjective
      (Q.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      (q.adicCompletionIntegers L ⧸ J)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) c)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective ybar
    refine ⟨x, ?_⟩
    have hkey : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) c := by
      rw [← Algebra.trace_quotient_mk (R := Q.adicCompletionIntegers K)
        (S := q.adicCompletionIntegers L) x, hy]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hkey, sub_self]
  have hunit : ∃ (t : (Q.adicCompletionIntegers K)ˣ) (x₀ : q.adicCompletionIntegers L),
      Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x₀ =
        (t : Q.adicCompletionIntegers K) := by
    obtain ⟨x, hx⟩ := hT 1
    have hu : IsUnit (Algebra.trace (Q.adicCompletionIntegers K)
        (q.adicCompletionIntegers L) x) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have h1 : (1 : Q.adicCompletionIntegers K) ∈
          IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
        have := (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).sub_mem hmem hx
        simpa using this
      exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one h1
    exact ⟨hu.unit, x, (IsUnit.unit_spec hu).symm⟩
  have hsurjR : ∀ c : Q.adicCompletionIntegers K, ∃ x : q.adicCompletionIntegers L,
      Algebra.trace (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x = c := by
    obtain ⟨t, x₀, ht⟩ := hunit
    intro c
    refine ⟨(c * ((t⁻¹ : (Q.adicCompletionIntegers K)ˣ) : Q.adicCompletionIntegers K)) • x₀, ?_⟩
    rw [map_smul, ht, smul_eq_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mul_one]
  intro c
  obtain ⟨x, hx⟩ := hsurjR c
  exact ⟨x, by rw [← trace_eq x, hx]⟩

end NK.NUV2.ARL
