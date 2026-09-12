import Submission.Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep

namespace Commons.LinearAlgebra.Independence

/-- The values (in the ambient real vector space `E`) of a `ℤ`-basis of a discrete
`ℤ`-submodule `ℒ` of a finite-dimensional real vector space are linearly independent
over `ℝ`.  Variant name of `discrete_basis_values_linIndep` kept for callers that use the
`_general` suffix. -/
theorem discrete_basis_values_linIndep_general {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    {m : ℕ} (b : Module.Basis (Fin m) ℤ ℒ) :
    LinearIndependent ℝ (fun i : Fin m => ((b i : ℒ) : E)) :=
  discrete_basis_values_linIndep ℒ b

end Commons.LinearAlgebra.Independence
