import Mathlib

open Filter
open scoped Topology

namespace Work.TMC13

/-- If `ℓ` is a continuous logarithm of `f` (`exp ∘ ℓ = f`) and `f` is differentiable at `x` with
`f x ≠ 0`, then `ℓ` is differentiable at `x` with derivative `f' / f x`.

This is the (real-)inverse-function-theorem "easy half" applied to the complex exponential, which is
a local diffeomorphism with derivative `exp (ℓ x) = f x` at `ℓ x` and whose real derivative is an
invertible real-linear map. -/
theorem log_lift_deriv {f ℓ : ℝ → ℂ} {x : ℝ} {f' : ℂ}
    (hf : HasDerivAt f f' x) (hf0 : f x ≠ 0) (hℓ : ContinuousAt ℓ x)
    (heq : ∀ t : ℝ, Complex.exp (ℓ t) = f t) :
    HasDerivAt ℓ (f' / f x) x := by
  have he0 : Complex.exp (ℓ x) ≠ 0 := Complex.exp_ne_zero (ℓ x)
  -- The (real) derivative of `exp` at `ℓ x` is multiplication by `exp (ℓ x)`, and
  -- multiplication by its inverse is a left inverse.
  let de : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ (Complex.exp (ℓ x))
  let dei : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ (Complex.exp (ℓ x))⁻¹
  have hde : ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp (ℓ x))) = de := by
    rw [Complex.restrictScalars_toSpanSingleton]
    ext z
    simp [de, ContinuousLinearMap.mul_apply', smul_eq_mul]
  have hexp : HasFDerivAt Complex.exp de (ℓ x) := by
    have h :=
      ((Complex.hasStrictDerivAt_exp (ℓ x)).hasStrictFDerivAt.restrictScalars ℝ).hasFDerivAt
    rwa [hde] at h
  have hleft : Function.LeftInverse dei de := by
    intro z
    simp only [de, dei, ContinuousLinearMap.mul_apply']
    rw [← mul_assoc, inv_mul_cancel₀ he0, one_mul]
  have hcomp : Complex.exp ∘ ℓ =ᶠ[𝓝 x] f := Filter.Eventually.of_forall fun t => heq t
  -- Inverse function theorem, easy half: `ℓ` is differentiable because `f = exp ∘ ℓ`.
  have key := HasFDerivAt.of_comp_of_leftInverse (g := ℓ) (f := Complex.exp) (h := f)
      (f' := de) (h' := ContinuousLinearMap.toSpanSingleton ℝ f') (f'symm := dei)
      hℓ hexp hf.hasFDerivAt hcomp hleft
  have hval : (dei ∘L ContinuousLinearMap.toSpanSingleton ℝ f') 1 = f' / f x := by
    simp only [dei, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, div_eq_mul_inv]
    rw [heq x, mul_comm]
  have hd : HasDerivAt ℓ ((dei ∘L ContinuousLinearMap.toSpanSingleton ℝ f') 1) x :=
    key.hasDerivAt
  rw [hval] at hd
  exact hd

end Work.TMC13
