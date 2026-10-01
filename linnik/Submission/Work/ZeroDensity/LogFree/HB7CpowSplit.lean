import Mathlib

namespace Work.ZeroDensity.LogFree

/-- Splitting the complex power `y^{a - i c}` (for positive real `y`, `Y`) by renormalising the
amplitude `y^a = Y^a · (y/Y)^a`, so that the frozen amplitude `Y^a` factors out of the
`y^{a - i c}` term. -/
theorem HB7CpowSplit {Y y a c : ℝ} (hY : 0 < Y) (hy : 0 < y) :
    (y : ℂ) ^ ((a : ℂ) - (c : ℂ) * Complex.I)
      = ((Y ^ a : ℝ) : ℂ) * (y : ℂ) ^ ((-(c : ℂ)) * Complex.I)
        + ((Y ^ a : ℝ) : ℂ) * (((y / Y) ^ a - 1 : ℝ) : ℂ)
            * (y : ℂ) ^ ((-(c : ℂ)) * Complex.I) := by
  -- `y ≠ 0` as a complex number, so that complex powers add.
  have hyne : (y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hy
  -- The amplitude identity `Y^a * (y/Y)^a = y^a` for positive reals.
  have hrpow : ((Y ^ a : ℝ) : ℂ) * (((y / Y) ^ a : ℝ) : ℂ) = ((y ^ a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul,
      ← Real.mul_rpow (le_of_lt hY) (div_nonneg (le_of_lt hy) (le_of_lt hY))]
    congr 1
    field_simp
  -- Real powers of positive reals are complex powers of the coerced base.
  have hcpow : ((y ^ a : ℝ) : ℂ) = (y : ℂ) ^ (a : ℂ) := Complex.ofReal_cpow (le_of_lt hy) a
  -- `1 + ((y/Y)^a - 1) = (y/Y)^a`.
  have hq : (1 + (((y / Y) ^ a - 1 : ℝ) : ℂ)) = (((y / Y) ^ a : ℝ) : ℂ) := by
    push_cast
    ring
  -- The oscillation factors combine: `y^a * y^{-ic} = y^{a-ic}`.
  have key : (y : ℂ) ^ (a : ℂ) * (y : ℂ) ^ ((-(c : ℂ)) * Complex.I)
      = (y : ℂ) ^ ((a : ℂ) - (c : ℂ) * Complex.I) := by
    rw [← Complex.cpow_add _ _ hyne]
    congr 1
    ring
  rw [← key, ← hcpow, ← hrpow, ← hq]
  ring

end Work.ZeroDensity.LogFree
