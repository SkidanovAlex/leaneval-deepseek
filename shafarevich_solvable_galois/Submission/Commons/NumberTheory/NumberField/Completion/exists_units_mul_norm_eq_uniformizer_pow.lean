import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.exists_norm_uniformizer_mul_unit_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

theorem exists_units_mul_norm_eq_uniformizer_pow {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ u : (Q.adicCompletionIntegers K)ˣ, ∃ x : (q.adicCompletion L)ˣ,
      (((Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K)
            (K := K) Q : Q.adicCompletionIntegers K)) : Q.adicCompletion K) ^
          (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) =
        (u : Q.adicCompletion K) * Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  obtain ⟨u, x, hx⟩ := exists_norm_uniformizer_mul_unit_adicCompletion Q q hq
  -- the uniformizer is nonzero
  have hϖne : ((Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K)
      (K := K) Q : Q.adicCompletionIntegers K) : Q.adicCompletion K) ≠ 0 := by
    intro h
    have hv := Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) Q
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have huK : ((u : Q.adicCompletionIntegers K) : Q.adicCompletion K) ≠ 0 :=
    fun h => Units.ne_zero u (Subtype.coe_injective h)
  have hRHSne : (u : Q.adicCompletion K) *
      ((Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K)
        (K := K) Q : Q.adicCompletionIntegers K) : Q.adicCompletion K) ^
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) ≠ 0 :=
    mul_ne_zero huK (pow_ne_zero _ hϖne)
  haveI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    module_finite_adicCompletion Q q hq
  have hxne : x ≠ 0 := by
    refine (Algebra.norm_ne_zero_iff (R := Q.adicCompletion K)).mp ?_
    rw [hx]
    exact hRHSne
  refine ⟨u⁻¹, Units.mk0 x hxne, ?_⟩
  have hu_inv : ((u⁻¹ : (Q.adicCompletionIntegers K)ˣ) : Q.adicCompletion K)
      = ((u : Q.adicCompletion K))⁻¹ := by
    exact map_inv ((algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)).toMonoidHom.comp
      (Units.coeHom (Q.adicCompletionIntegers K))) u
  rw [Units.val_mk0, hx, hu_inv, ← mul_assoc, inv_mul_cancel₀ huK, one_mul]

end Commons.NumberTheory.NumberField.Completion
