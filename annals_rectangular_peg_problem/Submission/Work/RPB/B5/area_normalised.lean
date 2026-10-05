import Mathlib
import Submission.Work.RPB.Defs

/-!
# `area_normalised`: normalising the area of a family of plane curves by a real scaling

Node B5 of the rectangular-peg route rescales a glued family of closed curves by a *constant*
factor `λ τ σ = √(2π(1+σ) / signedArea (shape τ σ))` in order to force the exact area law
`signedArea (Γc τ σ) = 2π (1+σ)` required by the collar (see `collar_exists`, conclusion (4),
where this identity is "`λ²·signedArea shape`").

The mathematical content is the elementary scaling law of the signed area
`(1/2) ∮ ω_ℂ(c, c')`: multiplying a closed plane curve by a **real** scalar `λ` (i.e. by the
complex number `(λ : ℂ)`) multiplies its signed area by `λ ^ 2`, since the area form
`ω_ℂ = Im(conj ·)` is a real bilinear form of determinant `λ²` under the diagonal scaling
`z ↦ λ z`.  Combining this with `Real.sq_sqrt` and `(A / signedArea) * signedArea = A` for
`A = 2π(1+σ) ≥ 0` and `signedArea > 0` gives `area_normalised`.

`deriv_const_mul` in Mathlib asks for differentiability of the curve; here the curve
`V τ σ` is *arbitrary* (the hypotheses only say that its signed area is positive), so the
proof goes through the hypothesis-free variant `deriv_const_mul_field`, valid because
Mathlib's `deriv` is `0` at points of non-differentiability (where also `deriv` of the
scalar multiple vanishes).

## Contents

* `signedArea_const_mul` — the scaling law `signedArea (λ · c) = λ^2 · signedArea c` for every
  real `λ` and every `c : ℝ → ℂ` (no regularity assumption);
* `area_normalised` — the requested normalisation lemma.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- **The signed area scales by the square of a real factor.**
`signedArea (t ↦ (λ : ℂ) * c t) = λ ^ 2 * signedArea c` for every real `λ` and every
`c : ℝ → ℂ`.  No differentiability is assumed: at a point where `c` is not differentiable,
so is `t ↦ (λ : ℂ) * c t`, and Mathlib's `deriv` returns `0` for both, which is exactly what
the hypothesis-free lemma `deriv_const_mul_field` records. -/
theorem signedArea_const_mul (c : ℝ → ℂ) (lam : ℝ) :
    Work.RPB.signedArea (fun t => (lam : ℂ) * c t) = lam ^ 2 * Work.RPB.signedArea c := by
  have hpoint : ∀ t, Work.RPV.ωC ((lam : ℂ) * c t) (deriv (fun u => (lam : ℂ) * c u) t)
      = lam ^ 2 * Work.RPV.ωC (c t) (deriv c t) := by
    intro t
    rw [deriv_const_mul_field]
    simp [Work.RPV.ωC, map_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hint : ∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC ((lam : ℂ) * c t) (deriv (fun u => (lam : ℂ) * c u) t)
      = ∫ t in (0 : ℝ)..(2 * Real.pi), lam ^ 2 * Work.RPV.ωC (c t) (deriv c t) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact hpoint t
  rw [Work.RPB.signedArea, Work.RPB.signedArea, hint, intervalIntegral.integral_const_mul]
  ring

theorem area_normalised (V : ℝ → ℝ → ℝ → ℂ) (τ σ : ℝ) (hσ : (0 : ℝ) ≤ σ) (hpos : 0 < Work.RPB.signedArea (V τ σ)) : Work.RPB.signedArea (fun t => (Real.sqrt (2 * Real.pi * (1 + σ) / Work.RPB.signedArea (V τ σ)) : ℂ) * V τ σ t) = 2 * Real.pi * (1 + σ) := by
  have hnum : (0 : ℝ) ≤ 2 * Real.pi * (1 + σ) := by positivity
  have hsqrt : (Real.sqrt (2 * Real.pi * (1 + σ) / Work.RPB.signedArea (V τ σ))) ^ 2
      = 2 * Real.pi * (1 + σ) / Work.RPB.signedArea (V τ σ) :=
    Real.sq_sqrt (div_nonneg hnum hpos.le)
  rw [signedArea_const_mul (V τ σ) (Real.sqrt (2 * Real.pi * (1 + σ) / Work.RPB.signedArea (V τ σ))),
    hsqrt, div_mul_cancel₀ _ (ne_of_gt hpos)]

end Work.RPB.B5
