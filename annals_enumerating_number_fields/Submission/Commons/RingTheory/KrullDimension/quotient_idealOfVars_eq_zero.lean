import Mathlib.RingTheory.KrullDimension.Field
import Submission.Commons.Algebra.MvPolynomial.idealOfVars_isMaximal

namespace Commons.RingTheory.KrullDimension

/-- The quotient of `k[x₁,…,x_m]` by the ideal of the variables is the field `k`, so it has
Krull dimension zero. -/
theorem quotient_idealOfVars_eq_zero {k : Type} [Field k] {m : ℕ} :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ MvPolynomial.idealOfVars (Fin m) k) = 0 := by
  have hmax : (MvPolynomial.idealOfVars (Fin m) k).IsMaximal :=
    Commons.Algebra.MvPolynomial.idealOfVars_isMaximal
  exact ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)

end Commons.RingTheory.KrullDimension