import Mathlib
import Submission.Work.CY3Stab.Prod.isPrime_map_includeRight_tensor

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.height_map_includeRight_tensor_transfer`

For a field `𝕜`, a `𝕜`-algebra `A` and an ideal `𝔭 ≤ A`, the height of the extension
`𝔭 · (𝕜[X_σ] ⊗[𝕜] A)` of `𝔭` along `includeRight` (inside the tensor product) equals the height
of the extension `𝔭 · A[X_σ]` of `𝔭` inside the polynomial ring `A[X_σ]`.

## Mathematical content

The tensor product `𝕜[X_σ] ⊗[𝕜] A` is identified with the polynomial ring `A[X_σ]` by the
`𝕜`-algebra isomorphism `scalarTensorMvPolynomialAlgEquiv 𝕜 σ A`
(`Submission/Work/CY3Stab/Prod/isPrime_map_includeRight_tensor.lean`), which sends
`includeRight c = 1 ⊗ₜ c` to the constant polynomial `C c`.  Hence it intertwines the two
extension maps:
`scalarTensorMvPolynomialAlgEquiv 𝕜 σ A ∘ includeRight = algebraMap A (MvPolynomial σ A)`.

Since the height of an ideal is invariant under a ring isomorphism (`RingEquiv.height_map`), the
heights of the two extended ideals agree.  No hypothesis on `𝔭` (prime, Noetherian) is needed: the
statement is pure transport of an ideal along an isomorphism.
-/

namespace Work.CY3Stab.Prod

/-- **Transfer of height along `𝕜[X_σ] ⊗[𝕜] A ≅ A[X_σ]`.**  Extending an ideal `𝔭 ≤ A` along
`includeRight` into `𝕜[X_σ] ⊗[𝕜] A` and extending it along `algebraMap A (MvPolynomial σ A)` into
`MvPolynomial σ A` give ideals of the same height. -/
theorem height_map_includeRight_tensor_transfer (𝕜 : Type) [Field 𝕜] (σ : Type) (A : Type)
    [CommRing A] [Algebra 𝕜 A] (𝔭 : Ideal A) :
    (Ideal.map (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜)
      (B := A)).toRingHom 𝔭).height
      = (𝔭.map (algebraMap A (MvPolynomial σ A))).height := by
  let e := (scalarTensorMvPolynomialAlgEquiv 𝕜 σ A).toRingEquiv
  -- `e` intertwines the two extension maps.
  have hcomp : (algebraMap A (MvPolynomial σ A)) =
      (e : TensorProduct 𝕜 (MvPolynomial σ 𝕜) A →+* MvPolynomial σ A).comp
        (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom := by
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, MvPolynomial.algebraMap_eq]
    exact (scalarTensorMvPolynomialAlgEquiv_includeRight 𝕜 σ A a).symm
  rw [hcomp, ← Ideal.map_map]
  exact (RingEquiv.height_map e
    (Ideal.map (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜)
      (B := A)).toRingHom 𝔭)).symm

end Work.CY3Stab.Prod
