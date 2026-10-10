import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `K ⊗[𝕜] 𝕜(σ)` is a domain

Let `𝕜` be a field, `K` a `𝕜`-algebra which is a domain, and let `𝕜(σ) = FractionRing (MvPolynomial σ 𝕜)`
be the field of rational functions in the variables `σ` over `𝕜`.  Then the tensor product
`K ⊗[𝕜] 𝕜(σ)` (over `𝕜`) is again a domain.

The proof goes as follows.  `𝕜(σ)` is the localization of `𝕜[σ] = MvPolynomial σ 𝕜` at its
non-zero-divisors, and tensoring a localization with `K` produces the localization of
`K ⊗[𝕜] 𝕜[σ]` at the image of this submonoid (`IsLocalization.tensorProduct_tensorProduct_right`).
Since `K ⊗[𝕜] 𝕜[σ] ≃ₐ[K] MvPolynomial σ K` is a polynomial ring over the domain `K`, it is itself a
domain, and the image of the non-zero-divisors of `𝕜[σ]` consists of non-zero-divisors (as
`𝕜[σ] → K ⊗[𝕜] 𝕜[σ]` is injective because `𝕜[σ]` is free, hence flat, over the field `𝕜`).
A localization of a domain at a submonoid of non-zero-divisors is a domain
(`IsLocalization.isDomain_of_le_nonZeroDivisors`).
-/

namespace Work.CY3Stab.Prod

open TensorProduct

/-- If `𝕜` is a field, `K` a domain which is a `𝕜`-algebra, then
`K ⊗[𝕜] FractionRing (MvPolynomial σ 𝕜)` is a domain. -/
theorem isDomain_tensor_fractionRing (𝕜 : Type) [Field 𝕜] (σ : Type) (K : Type) [CommRing K]
    [IsDomain K] [Algebra 𝕜 K] :
    IsDomain (TensorProduct 𝕜 K (FractionRing (MvPolynomial σ 𝕜))) := by
  -- `𝕜[σ]` is a domain.
  haveI : IsDomain (MvPolynomial σ 𝕜) := inferInstance
  -- `K ⊗[𝕜] 𝕜[σ] ≃ₐ[K] K[σ]` is a polynomial ring over the domain `K`, hence a domain.
  haveI hbase : IsDomain (K ⊗[𝕜] MvPolynomial σ 𝕜) :=
    Function.Injective.isDomain (MvPolynomial.algebraTensorAlgEquiv 𝕜 K).toRingEquiv
      (MvPolynomial.algebraTensorAlgEquiv 𝕜 K).injective
  -- `𝕜[σ]` is a free (hence flat) module over the field `𝕜`, so it injects into `K ⊗[𝕜] 𝕜[σ]`.
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := 𝕜) (A := K) (B := MvPolynomial σ 𝕜)) := by
    haveI : FaithfulSMul 𝕜 K := inferInstance
    exact Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective 𝕜 K)
  -- The non-zero-divisors of `𝕜[σ]` map to non-zero-divisors of `K ⊗[𝕜] 𝕜[σ]`.
  have hM : (nonZeroDivisors (MvPolynomial σ 𝕜)).map
      (Algebra.TensorProduct.includeRight (R := 𝕜) (A := K) (B := MvPolynomial σ 𝕜)) ≤
      nonZeroDivisors (K ⊗[𝕜] MvPolynomial σ 𝕜) := by
    rintro x ⟨a, ha, rfl⟩
    have ha0 : a ≠ 0 := by simpa using ha
    have h1 : (Algebra.TensorProduct.includeRight (R := 𝕜) (A := K)
        (B := MvPolynomial σ 𝕜)) a ≠ 0 := by
      intro h
      exact ha0 (hinj (by simpa using h))
    simpa using h1
  -- `K ⊗[𝕜] 𝕜(σ)` is the localization of `K ⊗[𝕜] 𝕜[σ]` at the image of the non-zero-divisors.
  let φ : K ⊗[𝕜] MvPolynomial σ 𝕜 →ₐ[K] K ⊗[𝕜] FractionRing (MvPolynomial σ 𝕜) :=
    Algebra.TensorProduct.map (AlgHom.id K K)
      (IsScalarTower.toAlgHom 𝕜 (MvPolynomial σ 𝕜) (FractionRing (MvPolynomial σ 𝕜)))
  algebraize [φ.toRingHom]
  haveI : IsScalarTower K (K ⊗[𝕜] MvPolynomial σ 𝕜)
      (K ⊗[𝕜] FractionRing (MvPolynomial σ 𝕜)) :=
    .of_algebraMap_eq <| by
      intro x
      show (algebraMap K (K ⊗[𝕜] FractionRing (MvPolynomial σ 𝕜))) x =
        (algebraMap (K ⊗[𝕜] MvPolynomial σ 𝕜) (K ⊗[𝕜] FractionRing (MvPolynomial σ 𝕜)))
          ((algebraMap K (K ⊗[𝕜] MvPolynomial σ 𝕜)) x)
      rw [RingHom.algebraMap_toAlgebra]
      exact (φ.commutes x).symm
  haveI hloc : IsLocalization ((nonZeroDivisors (MvPolynomial σ 𝕜)).map
      (Algebra.TensorProduct.includeRight (R := 𝕜) (A := K)))
      (K ⊗[𝕜] FractionRing (MvPolynomial σ 𝕜)) := by
    refine IsLocalization.tensorProduct_tensorProduct_right 𝕜 K (nonZeroDivisors (MvPolynomial σ 𝕜))
      (FractionRing (MvPolynomial σ 𝕜)) ?_
    exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_restrictScalars_comp_includeRight
      (f := AlgHom.id K K)
      (g := IsScalarTower.toAlgHom 𝕜 (MvPolynomial σ 𝕜) (FractionRing (MvPolynomial σ 𝕜))))
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (K ⊗[𝕜] FractionRing (MvPolynomial σ 𝕜)) hM

end Work.CY3Stab.Prod
