import Mathlib

namespace Work.LinnikAreas.BGTZ

open Complex

/-- **Rectangle contour-integral identity.**  For a function `H` holomorphic on the closed
rectangle `[p,q] × [-T,T]`, the difference of the two vertical integrals (multiplied by `I`)
equals the difference of the two horizontal integrals.  This is Cauchy–Goursat applied to the
boundary of the rectangle: the total boundary integral vanishes. -/
theorem rectVertIdentity (H : ℂ → ℂ) (p q T : ℝ)
    (hH : DifferentiableOn ℂ H (Set.uIcc p q ×ℂ Set.uIcc (-T) T)) :
    Complex.I * ((∫ y : ℝ in (-T)..T, H ((q : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y : ℝ in (-T)..T, H ((p : ℂ) + (y : ℂ) * Complex.I)))
      = (∫ x : ℝ in p..q, H ((x : ℂ) + (T : ℂ) * Complex.I))
        - (∫ x : ℝ in p..q, H ((x : ℂ) - (T : ℂ) * Complex.I)) := by
  -- The two opposite corners of the rectangle, as complex numbers.
  set z : ℂ := (p : ℂ) - (T : ℂ) * Complex.I
  set w : ℂ := (q : ℂ) + (T : ℂ) * Complex.I
  have hzre : z.re = p := by simp [z]
  have hzim : z.im = -T := by simp [z]
  have hwre : w.re = q := by simp [w]
  have hwim : w.im = T := by simp [w]
  -- Cauchy–Goursat for the boundary of the rectangle with corners `z` and `w`.
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H z w
    (by rw [hzre, hwre, hzim, hwim]; exact hH)
  rw [hzre, hwre, hzim, hwim] at h
  -- Rewrite the bottom edge integrand `x + (-T) * I` as `x - T * I`.
  have hA : (∫ x : ℝ in p..q, H (↑x + ↑(-T) * I)) = (∫ x : ℝ in p..q, H (↑x - ↑T * I)) := by
    congr 1 with x
    push_cast
    ring_nf
  rw [hA] at h
  rw [smul_eq_mul, smul_eq_mul] at h
  rw [add_sub_assoc] at h
  -- Extract the vertical difference from the vanishing boundary integral.
  have h2 : I * (∫ y : ℝ in (-T)..T, H (↑q + ↑y * I))
        - I * (∫ y : ℝ in (-T)..T, H (↑p + ↑y * I))
      = -(((∫ x : ℝ in p..q, H (↑x - ↑T * I)) - (∫ x : ℝ in p..q, H (↑x + ↑T * I)))) := by
    rw [eq_neg_iff_add_eq_zero]
    rw [add_comm]
    exact h
  rw [mul_sub]
  rw [h2]
  ring

end Work.LinnikAreas.BGTZ
