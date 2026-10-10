import Mathlib
import Submission.Work.TwistModel.BaseChange

set_option linter.unusedVariables false -- v435-speed

namespace Work.TwistModel

/-- Base change of a polynomial algebra along a field extension: `𝕜[X₁,…,Xₙ] ⊗_𝕜 K ≃ₐ[𝕜] K[X₁,…,Xₙ]`.

This is the `𝕜`-algebra form of `MvPolynomial.algebraTensorAlgEquiv` (which is stated over the
larger base `K`), composed with the commutativity of the tensor product. -/
theorem mvPolynomial_tensorBaseChange (𝕜 : Type) [Field 𝕜] (n : ℕ) (K : Type) [Field K]
    [Algebra 𝕜 K] :
    Nonempty (TensorProduct 𝕜 (MvPolynomial (Fin n) 𝕜) K ≃ₐ[𝕜] MvPolynomial (Fin n) K) :=
  ⟨(Algebra.TensorProduct.comm 𝕜 (MvPolynomial (Fin n) 𝕜) K).trans
     ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) 𝕜 K).restrictScalars 𝕜)⟩

end Work.TwistModel
