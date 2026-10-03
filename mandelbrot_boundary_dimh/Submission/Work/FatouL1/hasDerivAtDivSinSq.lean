import Mathlib

namespace Work.FatouL1

theorem hasDerivAtDivSinSq {w z : ℂ} (hsin : Complex.sin (Real.pi * (w - z)) ≠ 0) :
    HasDerivAt (fun z : ℂ => (Real.pi : ℂ) / (Complex.sin (Real.pi * (w - z))) ^ 2)
      ((2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * (w - z)) /
        (Complex.sin (Real.pi * (w - z))) ^ 3) z := by
  have h1 : HasDerivAt (fun y : ℂ => w - y) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub w
  have hlin : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) * (w - y)) (-(Real.pi : ℂ)) z := by
    have h := h1.const_mul (Real.pi : ℂ)
    simpa using h
  have hsq : HasDerivAt (fun y : ℂ => (Complex.sin (Real.pi * (w - y))) ^ 2)
      (2 * (Complex.sin (Real.pi * (w - z))) ^ 1 *
        (Complex.cos (Real.pi * (w - z)) * (-(Real.pi : ℂ)))) z :=
    hlin.csin.pow 2
  have hdiv := (hasDerivAt_const (x := z) (c := (Real.pi : ℂ))).div hsq (pow_ne_zero 2 hsin)
  convert hdiv using 1
  · field_simp
    ring

end Work.FatouL1
