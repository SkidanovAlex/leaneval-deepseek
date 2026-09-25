import Mathlib
import Submission.NK.NUV2.ARL.CommonsBridge

/-!
# Residue surjectivity of the local norm for an unramified prime

Let `L / K` be an extension of number fields, `q | Q` a prime of `L` over a prime `Q` of `K` with
ramification index one.  The local norm `N_{L_q / K_Q}` maps the ring of integers `𝒪_{L_q}` of the
completion *onto the residue field* of `K_Q`: for every unit `g` of `K_Q` there is `s ∈ 𝒪_{L_q}`
with `N (s) ≡ g (mod 𝔪_{K_Q})`.

This is the residue-level part of the unramified norm theorem and, unlike the full statement
`Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one`, it
needs **no** Galois hypothesis on `L / K`: the residue of the norm is the norm of the residue
(`Commons.RingTheory.Norm.residue_norm_eq`), and the norm of a finite extension of finite fields is
surjective (`FiniteField.norm_surjective`).  The formal proof is the Galois-free part of the proof
of the commons lemma, made self-contained here.
-/

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace NK.NUV2.ARL

/-- The field norm `N_{L_q/K_Q}` of an element of the ring of integers of `L_q` is the image of
its norm over the ring of integers of `K_Q`. -/
private theorem norm_adicCompletionIntegers_eq' {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
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
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
      Q q hq
  haveI : IsDomain (Q.adicCompletionIntegers K) := inferInstance
  haveI : IsDomain (q.adicCompletionIntegers L) := inferInstance
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.norm_localization (R := Q.adicCompletionIntegers K)
    (S := q.adicCompletionIntegers L) (Rₘ := Q.adicCompletion K) (Sₘ := q.adicCompletion L)
    (nonZeroDivisors (Q.adicCompletionIntegers K)) a

/-- **Residue surjectivity of the local norm** (Galois-free form): for an unramified prime `q | Q`,
every unit of the ring of integers of `K_Q` is congruent modulo the maximal ideal to the norm of an
element of the ring of integers of `L_q`. -/
private theorem exists_norm_sub_lt_one_of_val_eq_one' {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
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
  have hram :=
    Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow Q q hq
  have hmap : Ideal.map (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
    rw [hram, hunr, pow_one]
  obtain ⟨α, hα⟩ :=
    FiniteField.norm_surjective (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))
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
  rw [norm_adicCompletionIntegers_eq' Q q hq a]
  rw [show (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (Algebra.norm (Q.adicCompletionIntegers K) a) - y)
      = algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (Algebra.norm (Q.adicCompletionIntegers K) a - yR) from by
    rw [map_sub]; rfl]
  exact (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
    Q (Algebra.norm (Q.adicCompletionIntegers K) a - yR)).mp hmem

/-- **Unramified local norm is surjective modulo `𝔪`.**  For `L / K` an extension of number fields,
`q | Q` a prime with ramification index one, every unit `g` of the `Q`-adic completion of `K` is
congruent modulo `𝔪` to the norm from the integers of the `q`-adic completion of `L`. -/
theorem normResidueUnramified {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ g : Q.adicCompletion K, Valued.v g = 1 →
      ∃ s : q.adicCompletionIntegers L,
        Valued.v (Algebra.norm (Q.adicCompletion K)
            (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) s) - g) ≤
          (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) := by
  intro g hg
  obtain ⟨s, hs⟩ := exists_norm_sub_lt_one_of_val_eq_one' Q q hq hunr g hg
  exact ⟨s, Commons.NumberTheory.NumberField.Completion.le_exp_neg_one_iff.mpr (by simpa using hs)⟩

end NK.NUV2.ARL
