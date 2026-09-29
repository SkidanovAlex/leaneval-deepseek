import Mathlib
import Submission.Work.Resample.sliceB1defs

namespace Work.Resample

/-- Scaling identity: multiplying `fxC p z` by `2^p` (as a complex number) recovers the
integer pair `z`, since `fxC p z = (z.1 + i z.2) / 2^p`. -/
private lemma buDscScale (p : ℕ) (z : ℤ × ℤ) :
    (((2 : ℝ) ^ p : ℝ) : ℂ) * HvdH.fxC p z = (z.1 : ℂ) + (z.2 : ℂ) * Complex.I := by
  rw [HvdH.fxC]
  have h : (((2 : ℝ) ^ p : ℝ) : ℂ) = (2 : ℂ) ^ p := by push_cast; ring
  rw [h]
  field_simp

/-- Pointwise complex-algebra decomposition of the `2^p`-scaled error of one entry of `egDsc`:
the scaled output minus the scaled diagonal term splits into the `tdiv` rounding error, the
weight-rounding term (acting on `fxC p X`) and the propagation term. -/
theorem buDscKey (p : ℕ) (W : ℤ) (X : ℤ × ℤ) (d : ℝ) (y : ℂ) :
    (((2 : ℝ) ^ p : ℝ) : ℂ) *
        (HvdH.fxC p (Int.tdiv (W * X.1) ((2 : ℤ) ^ p), Int.tdiv (W * X.2) ((2 : ℤ) ^ p))
          - (d : ℂ) * y)
      = ((((Int.tdiv (W * X.1) ((2 : ℤ) ^ p) : ℤ) : ℂ)
            + ((Int.tdiv (W * X.2) ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I)
          - (W : ℂ) * ((X.1 : ℂ) + (X.2 : ℂ) * Complex.I) / ((2 : ℂ) ^ p))
        + ((W : ℂ) - ((((2 : ℝ) ^ p) * d : ℝ) : ℂ)) * HvdH.fxC p X
        + ((((2 : ℝ) ^ p) * d : ℝ) : ℂ) * (HvdH.fxC p X - y) := by
  -- Abbreviate `q = 2^p` (as a complex number), the rounded pair `Z'` and the exact pair `Z`,
  -- and use the scaling identity to replace `q * fxC p z` by the corresponding pair.
  have hA := buDscScale p
    (Int.tdiv (W * X.1) ((2 : ℤ) ^ p), Int.tdiv (W * X.2) ((2 : ℤ) ^ p))
  have hB := buDscScale p X
  rw [← hA, ← hB]
  push_cast
  field_simp
  ring

end Work.Resample
