import Mathlib

set_option linter.unusedVariables false

/-!
# Invariance of the vertical integral of a periodic holomorphic function

If `H` is holomorphic on the half-plane `{ζ : ζ.re < L}` and `2πi`-periodic there, then the
integral of `H` over the vertical segment `θ ↦ c + θ i`, `θ ∈ [0, 2π]`, does not depend on the
real part `c`, as long as `c < L`.

This is the boundary-integral computation obtained by applying Cauchy's theorem on the rectangle
with corners `c`, `c'`, `c' + 2πi`, `c + 2πi` and using the periodicity of `H` to cancel the two
horizontal sides.
-/

namespace Work.Potential

open scoped Interval

/-- Cauchy's theorem on the rectangle with corners `c`, `d`, `d + 2πi`, `c + 2πi`, written in
terms of the two horizontal and the two vertical boundary integrals. -/
private theorem rect_relation {H : ℂ → ℂ} {c d : ℝ}
    (hdiff : DifferentiableOn ℂ H ([[c, d]] ×ℂ [[(0 : ℝ), 2 * Real.pi]])) :
    (∫ x in c..d, H (x + 0 * Complex.I)) -
        (∫ x in c..d, H (x + (2 * Real.pi) * Complex.I))
      + Complex.I • (∫ y in (0 : ℝ)..(2 * Real.pi), H (d + y * Complex.I))
      - Complex.I • (∫ y in (0 : ℝ)..(2 * Real.pi), H (c + y * Complex.I)) = 0 := by
  have hdiff' : DifferentiableOn ℂ H
      ([[((c : ℂ)).re, (((d : ℂ) + 2 * Real.pi * Complex.I)).re]] ×ℂ
       [[((c : ℂ)).im, (((d : ℂ) + 2 * Real.pi * Complex.I)).im]]) := by
    simpa using hdiff
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H (c : ℂ)
    ((d : ℂ) + 2 * Real.pi * Complex.I) hdiff'
  simpa using h

theorem periodic_vertical_integral_invariance
    {L : ℝ} {H : ℂ → ℂ}
    (hH : ∀ ζ : ℂ, ζ.re < L → AnalyticAt ℂ H ζ)
    (hper : ∀ ζ : ℂ, ζ.re < L → H (ζ + 2 * Real.pi * Complex.I) = H ζ)
    {r R : ℝ} (hr : 0 < r) (hrL : Real.log r < L) (hR : 0 < R) (hRL : Real.log R < L) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), H ((Real.log r : ℂ) + θ * Complex.I))
      = ∫ θ in (0:ℝ)..(2 * Real.pi), H ((Real.log R : ℂ) + θ * Complex.I) := by
  have hdiff : DifferentiableOn ℂ H
      ([[Real.log r, Real.log R]] ×ℂ [[(0 : ℝ), 2 * Real.pi]]) := by
    intro ζ hζ
    have hre : ζ.re ∈ [[Real.log r, Real.log R]] := (Complex.mem_reProdIm.mp hζ).1
    have hlt : ζ.re < L := by
      rcases Set.mem_uIcc.mp hre with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · linarith
      · linarith
    exact ((hH ζ hlt).differentiableAt).differentiableWithinAt
  have hrect := rect_relation hdiff
  have hAB : (∫ x in Real.log r..Real.log R, H (x + 0 * Complex.I))
      = ∫ x in Real.log r..Real.log R, H (x + (2 * Real.pi) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxL : x < L := by
      rcases Set.mem_uIcc.mp hx with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · linarith
      · linarith
    have hp : H ((x : ℂ) + 2 * Real.pi * Complex.I) = H (x : ℂ) :=
      hper (x : ℂ) (by simpa using hxL)
    simp only [zero_mul, add_zero]
    exact hp.symm
  rw [hAB, sub_self, zero_add] at hrect
  rw [← smul_sub] at hrect
  have hVR : (∫ y in (0 : ℝ)..(2 * Real.pi), H ((Real.log R : ℂ) + y * Complex.I))
      = ∫ y in (0 : ℝ)..(2 * Real.pi), H ((Real.log r : ℂ) + y * Complex.I) := by
    rcases smul_eq_zero.mp hrect with hI | h0
    · exact absurd hI Complex.I_ne_zero
    · exact sub_eq_zero.mp h0
  exact hVR.symm

end Work.Potential
