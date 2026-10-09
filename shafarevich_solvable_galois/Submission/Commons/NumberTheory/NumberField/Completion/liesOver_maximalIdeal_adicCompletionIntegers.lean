import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.RingTheory.Henselian.valuation_completion_liesOver
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

open Commons.NumberTheory.NumberField

theorem liesOver_maximalIdeal_adicCompletionIntegers {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
      RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
          (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
        (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
    Ideal.LiesOver (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := by
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
      (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
  have he : Q.asIdeal.ramificationIdx' q.asIdeal ≠ 0 := by
    haveI : q.asIdeal.LiesOver Q.asIdeal := hq
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q.asIdeal Q.ne_bot
  have hval : ∀ x : Q.adicCompletionIntegers K,
      Valued.v ((algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x :
          q.adicCompletionIntegers L) : q.adicCompletion L) =
        (Valued.v (x : Q.adicCompletion K)) ^ Q.asIdeal.ramificationIdx' q.asIdeal := by
    intro x
    have hco : ((algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x :
        q.adicCompletionIntegers L) : q.adicCompletion L) =
        Commons.RingTheory.Henselian.adicCompletionMap Q q hq (x : Q.adicCompletion K) := rfl
    rw [hco]
    exact Commons.RingTheory.Henselian.valuation_completion_liesOver Q q hq (x : Q.adicCompletion K)
  have hiff : ∀ x : Q.adicCompletionIntegers K,
      (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x ∈
          IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ↔
        x ∈ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
    intro x
    rw [adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one Q x,
      adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one q
        (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) x)]
    rw [hval x]
    exact pow_lt_one_iff_of_nonneg zero_le he
  refine ⟨?_⟩
  ext x
  rw [Ideal.mem_under]
  exact (hiff x).symm

end Commons.NumberTheory.NumberField.Completion
