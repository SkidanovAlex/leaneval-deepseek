import Mathlib
import Submission.Work.RPV.Defs

/-!
# `Work.RPB.B2.hasDerivAt_div_norm`

The derivative of the unit vector field `s ↦ V s / ‖V s‖` along a differentiable curve
`V : ℝ → ℂ` (away from `V = 0`), in the normal form used throughout the chord-phase
construction of B2:

`(V/‖V‖)' = I * (V/‖V‖) * (ωC V V' / ‖V‖ ^ 2)`,

where `ωC a b = Im (conj a * b)` is the symplectic form of `Work.RPV.Defs`.

The proof splits into two independent, reusable facts:

* `hasDerivAt_norm_of_complex` — the real derivative of `s ↦ ‖z s‖`, obtained from
  Mathlib's `HasDerivAt.norm_sq` and the chain rule with `Real.sqrt`;
* `div_norm_deriv_algebra` — the purely algebraic identity converting the quotient-rule
  expression for the derivative of `V / ↑(‖V‖)` into the `I * · * (ωC · / ‖·‖²)` shape.

Both are then combined through `HasDerivAt.fun_div`.
-/

open Complex

namespace Work.RPB.B2

/-- The real derivative of the norm of a complex-valued differentiable curve:
`(‖z‖)' = Re (conj (z t) * ζ) / ‖z t‖`, valid away from `z t = 0`. -/
theorem hasDerivAt_norm_of_complex {z : ℝ → ℂ} {ζ : ℂ} {t : ℝ}
    (hz : HasDerivAt z ζ t) (hne : z t ≠ 0) :
    HasDerivAt (fun s => ‖z s‖) (((starRingEnd ℂ) (z t) * ζ).re / ‖z t‖) t := by
  have hsq : HasDerivAt (fun s => ‖z s‖ ^ 2) (2 * ((starRingEnd ℂ) (z t) * ζ).re) t := by
    simpa [Complex.inner, mul_comm] using hz.norm_sq
  have hnorm_ne : ‖z t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hpos : ‖z t‖ ^ 2 ≠ 0 := by positivity
  have hcomp : HasDerivAt (fun s => Real.sqrt (‖z s‖ ^ 2))
      (1 / (2 * Real.sqrt (‖z t‖ ^ 2)) * (2 * ((starRingEnd ℂ) (z t) * ζ).re)) t :=
    (Real.hasDerivAt_sqrt hpos).comp t hsq
  have hfun : (fun s => Real.sqrt (‖z s‖ ^ 2)) = fun s => ‖z s‖ := by
    funext s; exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hcomp
  convert hcomp using 1
  rw [Real.sqrt_sq (norm_nonneg _)]
  field_simp

/-- The complex-algebra identity behind `hasDerivAt_div_norm`: the quotient-rule expression
for the derivative of `s ↦ u / ↑‖u‖` (with `v'` the derivative of the numerator along the
curve) agrees with `I * (u / ‖u‖) * (ωC u v' / ‖u‖ ^ 2)`. -/
theorem div_norm_deriv_algebra (u v' : ℂ) (hu : u ≠ 0) :
    (v' * (‖u‖ : ℂ) - u * ((((starRingEnd ℂ) u * v').re / ‖u‖ : ℝ) : ℂ)) /
        ((‖u‖ : ℂ) ^ 2)
      = Complex.I * (u / ‖u‖) * ((Work.RPV.ωC u v' / ‖u‖ ^ 2 : ℝ) : ℂ) := by
  have hnorm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnormC : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnorm_ne
  set A : ℂ := (starRingEnd ℂ) u * v' with hA
  have hω : Work.RPV.ωC u v' = A.im := by simp only [Work.RPV.ωC, ← hA]
  have hre : ((starRingEnd ℂ) u * v').re = A.re := by rw [← hA]
  have hconj : ((starRingEnd ℂ) u) * u = ((‖u‖ : ℂ) ^ 2) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hvu : v' = A * u / ((‖u‖ : ℂ) ^ 2) := by
    have hAu : A * u = v' * ((‖u‖ : ℂ) ^ 2) := by
      rw [hA, mul_assoc, mul_comm v' u, ← mul_assoc, hconj, mul_comm]
    rw [hAu]
    field_simp
  rw [hω, hre, hvu]
  simp only [Complex.ofReal_div, Complex.ofReal_pow]
  field_simp
  nth_rewrite 1 [← Complex.re_add_im A]
  ring

/-- Along a differentiable curve `V` with `V τ ≠ 0`, the derivative of the unit vector
`V / ‖V‖` is `I * (V τ / ‖V τ‖) * (ωC (V τ) v' / ‖V τ‖ ^ 2)`: the unit vector rotated by
`π/2` and scaled by the (symplectic) angular velocity `ωC (V τ) v' / ‖V τ‖ ^ 2`. -/
theorem hasDerivAt_div_norm (V : ℝ → ℂ) (v' : ℂ) (τ : ℝ) (hV : HasDerivAt V v' τ)
    (hne : V τ ≠ 0) :
    HasDerivAt (fun s => V s / ‖V s‖)
      (Complex.I * (V τ / ‖V τ‖) *
        ((Work.RPV.ωC (V τ) v' / ‖V τ‖ ^ 2 : ℝ) : ℂ)) τ := by
  have hnorm : HasDerivAt (fun s => ‖V s‖) (((starRingEnd ℂ) (V τ) * v').re / ‖V τ‖) τ :=
    hasDerivAt_norm_of_complex hV hne
  have hnormC : HasDerivAt (fun s => ((‖V s‖ : ℝ) : ℂ))
      ((((starRingEnd ℂ) (V τ) * v').re / ‖V τ‖ : ℝ) : ℂ) τ := hnorm.ofReal_comp
  have hneC : ((‖V τ‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hne
  have hdiv := hV.fun_div hnormC hneC
  rw [div_norm_deriv_algebra (V τ) v' hne] at hdiv
  exact hdiv

end Work.RPB.B2
