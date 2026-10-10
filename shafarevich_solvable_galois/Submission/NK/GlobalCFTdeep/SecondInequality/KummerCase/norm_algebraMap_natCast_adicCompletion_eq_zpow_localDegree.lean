import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.GlobalCFTdeep.SecondInequality.adicAbv_prime_eq_zpow_localDegree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- **The `𝔮`-adic norm of the rational prime below `𝔮`.**

The canonical embedding `K → 𝔮.adicCompletion K` is `NumberField.FinitePlace.embedding 𝔮`,
and Mathlib's `NumberField.FinitePlace.norm_embedding` computes its norm as the `𝔮`-adic
absolute value `adicAbv K 𝔮`.  Combining that with
`adicAbv_prime_eq_zpow_localDegree` gives `|p|_𝔮 = p ^ (-[K_𝔮 : ℚ_p])`. -/
theorem norm_algebraMap_natCast_adicCompletion_eq_zpow_localDegree {K : Type} [Field K]
    [NumberField K] (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {p : ℕ} (hp : p.Prime) (hmem : (p : NumberField.RingOfIntegers K) ∈ q.asIdeal) :
    ‖algebraMap K (q.adicCompletion K) (p : K)‖ =
      (p : ℝ) ^ (-(NK.LocalInputs.localDegree K q : ℤ)) := by
  have halg : algebraMap K (q.adicCompletion K) (p : K)
      = NumberField.FinitePlace.embedding q (p : K) := by
    rw [NumberField.FinitePlace.embedding_apply]
    rfl
  rw [halg, NumberField.FinitePlace.norm_embedding]
  exact adicAbv_prime_eq_zpow_localDegree q hp hmem

end NK.GlobalCFTdeep.SecondInequality.KummerCase
