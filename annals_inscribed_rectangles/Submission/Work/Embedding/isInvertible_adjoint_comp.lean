import Mathlib

namespace Work.Embedding

open ContinuousLinearMap

/-- If `A : E →L[𝕜] F` is injective, then the self-adjoint operator `A† ∘ A` on `E` is
invertible (as a continuous linear map); over a finite-dimensional space, injectivity of `A`
forces the positive-definite operator `A† ∘ A` to be a linear equivalence, and every linear
equivalence of a finite-dimensional normed space is continuous. -/
theorem isInvertible_adjoint_comp {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) (hA : Function.Injective A) : (A.adjoint ∘L A).IsInvertible := by
  -- `A† ∘ A` has trivial kernel: `⟪(A† ∘ A) x, x⟫ = ‖A x‖ ^ 2`.
  have hker : ∀ x, (A.adjoint ∘L A) x = 0 → x = 0 := by
    intro x hx
    have h1 : ‖A x‖ ^ 2 = 0 := by
      rw [apply_norm_sq_eq_inner_adjoint_left A x, hx]
      simp
    have h2 : A x = 0 := by
      have h3 : ‖A x‖ = 0 := by
        rw [← pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), h1]
      simpa using h3
    exact hA (by rw [h2, map_zero])
  have hinj : Function.Injective (((A.adjoint ∘L A) : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
    intro x y hxy
    have hxy' : (A.adjoint ∘L A) x = (A.adjoint ∘L A) y := hxy
    have hsub : (A.adjoint ∘L A) (x - y) = 0 := by rw [map_sub, hxy', sub_self]
    exact sub_eq_zero.mp (hker (x - y) hsub)
  -- An injective endomorphism of a finite-dimensional space is a linear equivalence, and on a
  -- finite-dimensional normed space every linear equivalence is continuous.
  refine ⟨(LinearEquiv.ofInjectiveEndo (((A.adjoint ∘L A) : E →L[𝕜] E) : E →ₗ[𝕜] E)
      hinj).toContinuousLinearEquiv, ?_⟩
  ext x
  simp [LinearEquiv.coe_ofInjectiveEndo, LinearEquiv.coe_toContinuousLinearEquiv']

end Work.Embedding
