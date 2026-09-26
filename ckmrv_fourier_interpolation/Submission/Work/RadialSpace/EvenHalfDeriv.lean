import Mathlib
import Submission.Work.RadialSpace.Basic
import Submission.Work.RadialSpace.contDiff_parametric_integral

/-!
# The half-derivative operator on even smooth functions

For an even smooth function `g : ℝ → ℂ`, the "half-derivative" `evenHalfDeriv g`
is the even smooth function with

`evenHalfDeriv g u = deriv g u / (2 * u)`  for `u ≠ 0`.

It is defined by the integral `u ↦ (1/2) ∫_0^1 g''(u t) dt`, which is manifestly
smooth in `u` (see `contDiff_evenHalfDeriv`), even when `g` is even, and whose
value at `u ≠ 0` is `deriv g u / (2u)` by the fundamental theorem of calculus.

Iterating `evenHalfDeriv` produces the one-sided derivatives of the function
`s ↦ g (√s)` (see `iteratedDeriv_comp_sqrt`), which is the essential analytic
input for the "even smooth functions are smooth functions of the square"
factorisation, and for the theory of radial derivatives.

## Main definitions

* `Work.RadialSpace.evenHalfDeriv`
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff

namespace Work.RadialSpace

/-- The half-derivative of `g`: `(1/2) ∫_0^1 g''(u t) dt`. For even smooth `g`
this is the smooth extension of `u ↦ deriv g u / (2 * u)`. -/
noncomputable def evenHalfDeriv (g : ℝ → ℂ) : ℝ → ℂ :=
  fun u => (1 / 2 : ℂ) * ∫ t in (0 : ℝ)..1, iteratedDeriv 2 g (u * t)

@[simp] lemma evenHalfDeriv_apply (g : ℝ → ℂ) (u : ℝ) :
    evenHalfDeriv g u = (1 / 2 : ℂ) * ∫ t in (0 : ℝ)..1, iteratedDeriv 2 g (u * t) := rfl

/-- The second derivative of an even function is even. -/
lemma even_iteratedDeriv_two {g : ℝ → ℂ} (he : Function.Even g) :
    Function.Even (iteratedDeriv 2 g) := by
  have h : (fun x : ℝ => g (-x)) = g := funext he
  have := iteratedDeriv_comp_neg 2 g
  rw [h] at this
  intro u
  simpa using this (-u)

/-- The half-derivative of an even function is even. -/
lemma even_evenHalfDeriv {g : ℝ → ℂ} (he : Function.Even g) :
    Function.Even (evenHalfDeriv g) := by
  intro u
  have hfun : (fun t : ℝ => iteratedDeriv 2 g ((-u) * t))
      = fun t : ℝ => iteratedDeriv 2 g (u * t) := by
    funext t
    rw [neg_mul, (even_iteratedDeriv_two he).eq (u * t)]
  simp only [evenHalfDeriv_apply, hfun]

/-- The derivative of a smooth function is smooth. -/
theorem contDiff_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ Smooth f) : ContDiff ℝ Smooth (deriv f) := by
  rw [contDiff_infty] at hf ⊢
  intro n
  exact (contDiff_succ_iff_deriv.mp (hf (n + 1))).2.2

/-- The half-derivative of a smooth function is smooth. -/
theorem contDiff_evenHalfDeriv {g : ℝ → ℂ} (hg : ContDiff ℝ Smooth g) :
    ContDiff ℝ Smooth (evenHalfDeriv g) := by
  have h2 : ContDiff ℝ Smooth (iteratedDeriv 2 g) := by
    have h : iteratedDeriv 2 g = deriv (deriv g) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h]
    exact contDiff_deriv (contDiff_deriv hg)
  have h := contDiff_parametric_integral (iteratedDeriv 2 g) h2
  have h4 : (fun u : ℝ => (1 / 2 : ℂ) * ∫ t in (0 : ℝ)..1, iteratedDeriv 2 g (u * t))
      = evenHalfDeriv g := rfl
  rw [← h4]
  simpa using (contDiff_const.mul h)

/-- The value of the half-derivative at zero: half of the second derivative. -/
lemma evenHalfDeriv_zero (g : ℝ → ℂ) : evenHalfDeriv g 0 = (1 / 2 : ℂ) * iteratedDeriv 2 g 0 := by
  simp only [evenHalfDeriv_apply, zero_mul]
  rw [intervalIntegral.integral_const, sub_zero]
  simp

end Work.RadialSpace
