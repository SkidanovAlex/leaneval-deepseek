import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

theorem exists_units_mul_uniformizer_zpow_adicCompletion {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : (Q.adicCompletion K)ˣ) :
    ∃ u : (Q.adicCompletionIntegers K)ˣ, ∃ m : ℤ,
      (x : Q.adicCompletion K) = (u : Q.adicCompletionIntegers K) *
        (((Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K)
            (K := K) Q : Q.adicCompletionIntegers K)) : Q.adicCompletion K) ^ m := by
  let A := Q.adicCompletionIntegers K
  let ϖ : A := Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K) (K := K) Q
  have hϖ : Irreducible ϖ := Commons.RingTheory.Henselian.uniformizer_irreducible Q
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (R := A) (K := Q.adicCompletion K) hϖ (Units.ne_zero x)
  refine ⟨u, m, ?_⟩
  rw [hu]
  simp [A, ϖ, Units.smul_def, Algebra.smul_def]

end Commons.NumberTheory.NumberField.Completion