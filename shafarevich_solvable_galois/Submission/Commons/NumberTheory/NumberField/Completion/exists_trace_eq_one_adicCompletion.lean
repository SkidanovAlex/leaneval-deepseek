import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

set_option linter.style.haveILetI false

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

theorem exists_trace_eq_one_adicCompletion {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ D : ℕ, ∃ u : q.adicCompletion L,
      Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) u = 1 ∧
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) u ≤
        (WithZero.exp (D : ℤ) : WithZero (Multiplicative ℤ)) := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    module_finite_adicCompletion Q q hq
  haveI hchar : CharZero (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion Q
  set n : ℕ := Module.finrank (Q.adicCompletion K) (q.adicCompletion L) with hn
  have hnpos : 0 < n := by
    rw [hn]
    exact Module.finrank_pos
  have hnF : (n : Q.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  let u : q.adicCompletion L :=
    algebraMap (Q.adicCompletion K) (q.adicCompletion L) ((n : Q.adicCompletion K))⁻¹
  have hu0 : u ≠ 0 := by
    change algebraMap (Q.adicCompletion K) (q.adicCompletion L)
      ((n : Q.adicCompletion K))⁻¹ ≠ 0
    exact fun h => inv_ne_zero hnF
      ((algebraMap (Q.adicCompletion K) (q.adicCompletion L)).injective (by simpa using h))
  have hv0 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) u ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hu0
  refine ⟨(WithZero.log (Valued.v (R := q.adicCompletion L)
      (Γ₀ := WithZero (Multiplicative ℤ)) u)).natAbs, u, ?_, ?_⟩
  · change Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) ((n : Q.adicCompletion K))⁻¹) = 1
    rw [Algebra.trace_algebraMap]
    rw [← hn, nsmul_eq_mul]
    exact mul_inv_cancel₀ hnF
  · calc Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) u
        = WithZero.exp (WithZero.log (Valued.v (R := q.adicCompletion L)
            (Γ₀ := WithZero (Multiplicative ℤ)) u)) := (WithZero.exp_log hv0).symm
      _ ≤ WithZero.exp ((((WithZero.log (Valued.v (R := q.adicCompletion L)
            (Γ₀ := WithZero (Multiplicative ℤ)) u)).natAbs : ℕ) : ℤ)) :=
          WithZero.exp_le_exp.mpr Int.le_natAbs

end Commons.NumberTheory.NumberField.Completion