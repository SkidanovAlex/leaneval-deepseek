import Mathlib
import Submission.Work.FatouL1.normSqSinComplex
import Submission.Work.FatouL1.normSqCosComplex
import Submission.Work.FatouL1.existsLeSinSqOnIcc

/-!
# Boundedness of `cot (π ·)` on a vertical strip meeting `(-1, 0)`

For real `p q` with `-1 < p` and `q < 0` the strip `{s : ℂ | p ≤ Re s ≤ q}` is contained in
`(-1, 0) × ℝ`, which contains no pole of `cot (π ·)` (the poles are the integers).  Writing
`s = x + iy` and using

  `‖sin (π s)‖² = sin (π x)² + sinh (π y)²`,  `‖cos (π s)‖² = cos (π x)² + sinh (π y)²`,

we get `‖cot (π s)‖² = (cos (π x)² + sinh (π y)²) / (sin (π x)² + sinh (π y)²)`.  The lower bound
`m > 0` for `sin (π x)²` on the (compact) interval `Icc p q` turns this into the uniform bound
`≤ 1/m`, so `C = √(1/m)` works.
-/

namespace Work.FatouL1

/-- On the vertical strip `{s | p ≤ s.re ≤ q} ⊂ (-1,0) × ℝ`, `‖Complex.cot (π s)‖` is bounded. -/
theorem existsNormCotPiLe {p q : ℝ} (hp : -1 < p) (hq : q < 0) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ∈ Set.Icc p q → ‖Complex.cot (Real.pi * s)‖ ≤ C := by
  obtain ⟨m, hm0, hm1, hm⟩ := existsLeSinSqOnIcc hp hq
  refine ⟨Real.sqrt (1 / m), ?_⟩
  intro s hs
  have hmle : m ≤ Real.sin (Real.pi * s.re) ^ 2 := hm s.re hs
  have hre : (Real.pi * s).re = Real.pi * s.re := by simp [Complex.mul_re]
  have him : (Real.pi * s).im = Real.pi * s.im := by simp [Complex.mul_im]
  have hcot : ‖Complex.cot (Real.pi * s)‖ ^ 2
      = ‖Complex.cos (Real.pi * s)‖ ^ 2 / ‖Complex.sin (Real.pi * s)‖ ^ 2 := by
    rw [Complex.cot_eq_cos_div_sin, norm_div, div_pow]
  have hb : ‖Complex.cot (Real.pi * s)‖ ^ 2 ≤ 1 / m := by
    rw [hcot, normSqCosComplex, normSqSinComplex, hre, him]
    rw [div_le_div_iff₀ (by nlinarith [hmle, hm0, sq_nonneg (Real.sinh (Real.pi * s.im))])
      (by positivity)]
    have hC : Real.cos (Real.pi * s.re) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * s.re)]
    nlinarith [hmle, hm0, hm1, hC, sq_nonneg (Real.sinh (Real.pi * s.im))]
  calc ‖Complex.cot (Real.pi * s)‖
      = Real.sqrt (‖Complex.cot (Real.pi * s)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (1 / m) := Real.sqrt_le_sqrt hb

end Work.FatouL1
