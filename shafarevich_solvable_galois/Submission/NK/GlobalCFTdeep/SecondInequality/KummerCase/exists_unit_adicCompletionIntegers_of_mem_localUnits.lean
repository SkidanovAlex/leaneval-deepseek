import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- If the principal idèle attached to `b : Kˣ` is a local unit at the finite place `Q`, then the
image of `b` in the `Q`-adic completion is a unit of the ring of integers `𝒪_Q` of that
completion.

Concretely, `b` is a local unit at `Q` exactly when `algebraMap K (Q.adicCompletion K) b` lies in
`𝒪_Q` together with its inverse; that is the same as saying it is a unit of `𝒪_Q`, and by
`adicCompletionIntegers.mem_units_iff_valued_eq_one` this is the same as its `Q`-adic valuation
being `1`. -/
theorem exists_unit_adicCompletionIntegers_of_mem_localUnits
    {K : Type*} [Field K] [NumberField K] (b : Kˣ)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hb : NK.GlobalCFT.Idele.principalIdele K b (NK.GlobalCFT.Place.ofFinite Q) ∈
      NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q)) :
    ∃ u : (Q.adicCompletionIntegers K)ˣ,
      (u : Q.adicCompletion K) = algebraMap K (Q.adicCompletion K) (b : K) ∧
      Valued.v (algebraMap K (Q.adicCompletion K) (b : K)) = 1 := by
  have hb' : Units.map (algebraMap K (Q.adicCompletion K)) b ∈
      (Q.adicCompletionIntegers K).units := hb
  have h1 : ((Units.map (algebraMap K (Q.adicCompletion K)) b : (Q.adicCompletion K)ˣ) :
      Q.adicCompletion K) ∈ Q.adicCompletionIntegers K := hb'.1
  have hy : (algebraMap K (Q.adicCompletion K) (b : K)) ∈ Q.adicCompletionIntegers K := h1
  have hv : Valued.v ((Units.map (algebraMap K (Q.adicCompletion K)) b :
      (Q.adicCompletion K)ˣ) : Q.adicCompletion K) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (v := Q)).1 hb'
  have hyv : Valued.v (algebraMap K (Q.adicCompletion K) (b : K)) = 1 := hv
  have hunit : IsUnit (⟨algebraMap K (Q.adicCompletion K) (b : K), hy⟩ :
      Q.adicCompletionIntegers K) := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hyv
  refine ⟨hunit.unit, ?_, hyv⟩
  rw [IsUnit.unit_spec]

end NK.GlobalCFTdeep.SecondInequality.KummerCase
