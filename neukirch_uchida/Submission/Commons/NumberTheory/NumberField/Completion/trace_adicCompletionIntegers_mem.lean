import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension

/-!
# Integrality of the trace on the ring of integers of an adic completion

Let `L / K` be a finite Galois extension of number fields, `Q` a height-one prime of `𝓞 K`
and `q` a height-one prime of `𝓞 L` lying over `Q`.  Via the ring homomorphism
`Commons.RingTheory.Henselian.adicCompletionMap Q q hq : Q.adicCompletion K →+* q.adicCompletion L`,
view the local field `L_q = q.adicCompletion L` as an extension of `K_Q = Q.adicCompletion K`.

Then the trace `Tr_{L_q / K_Q}` maps the ring of integers `q.adicCompletionIntegers L` into the
ring of integers `Q.adicCompletionIntegers K`.

This is the standard argument for the integrality of traces in an AKLB setup: the ring of
integers of `L_q` is integral over the ring of integers of `K_Q`
(`Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension`),
the trace of an integral element of a finite extension is integral
(`Algebra.isIntegral_trace`), and the ring of integers `Q.adicCompletionIntegers K` is
integrally closed in `K_Q`, so it contains every element of `K_Q` integral over it.
-/

open scoped NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

theorem trace_adicCompletionIntegers_mem {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ x : q.adicCompletionIntegers L,
      Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) (x : q.adicCompletion L) ∈
        Q.adicCompletionIntegers K := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- The `Q.adicCompletionIntegers K`-algebra structure on the field `L_q`.
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  -- The `Q.adicCompletionIntegers K`-algebra structure on the ring of integers of `L_q`.
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (adicCompletionMapIntegers Q q hq)
  -- The two towers used below are scalar towers.
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K)
      (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- `q.adicCompletionIntegers L` is the integral closure of `Q.adicCompletionIntegers K`.
  haveI : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    isIntegralClosure_adicCompletionIntegers_extension Q q hq
  -- `L_q` is a finite extension of `K_Q`.
  haveI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    module_finite_adicCompletion Q q hq
  intro x
  -- `x` is integral over the ring of integers of `K_Q`.
  have hx : IsIntegral (Q.adicCompletionIntegers K)
      ((x : q.adicCompletionIntegers L) : q.adicCompletion L) :=
    IsIntegralClosure.isIntegral_iff.mpr ⟨x, rfl⟩
  -- hence its trace is integral over the ring of integers of `K_Q`.
  have htr : IsIntegral (Q.adicCompletionIntegers K)
      (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
        ((x : q.adicCompletionIntegers L) : q.adicCompletion L)) :=
    Algebra.isIntegral_trace (R := Q.adicCompletionIntegers K) (L := Q.adicCompletion K)
      (F := q.adicCompletion L) hx
  -- the ring of integers of `K_Q` is integrally closed in `K_Q`, so it contains the trace.
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
  rw [← ha]
  exact a.2

end Commons.NumberTheory.NumberField.Completion
