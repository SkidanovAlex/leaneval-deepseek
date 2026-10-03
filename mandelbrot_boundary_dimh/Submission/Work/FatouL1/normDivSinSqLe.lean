import Mathlib
import Submission.Work.FatouL1.existsLeSinSqOnIcc
import Submission.Work.FatouL1.normSqSinComplex

namespace Work.FatouL1

/-- On the strip `{s : ℂ | s.re ∈ [p,q]}` with `-1 < p`, `q < 0` the function
`π / sin (π s)^2` is bounded: the strip contains no pole of `sin (π ·)` (poles
occupy the integers, excluded by `-1 < p ≤ s.re ≤ q < 0`), `sin (π s)` grows
exponentially in the imaginary direction, and
`‖sin (π s)‖ ^ 2 = sin (π s.re) ^ 2 + sinh (π s.im) ^ 2 ≥ sin (π s.re) ^ 2`
is bounded below by a positive constant on the compact interval `[p,q]`. -/
theorem normDivSinSqLe {p q : ℝ} (hp : -1 < p) (hq : q < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Set.Icc p q →
      ‖(Real.pi : ℂ) / (Complex.sin (Real.pi * s)) ^ 2‖ ≤ C := by
  obtain ⟨m, hm0, hm1, hm⟩ := existsLeSinSqOnIcc hp hq
  refine ⟨Real.pi / m, div_nonneg Real.pi_pos.le hm0.le, ?_⟩
  intro s hs
  have hsin : m ≤ ‖Complex.sin (Real.pi * s)‖ ^ 2 := by
    rw [normSqSinComplex]
    have hre : (Real.pi * s).re = Real.pi * s.re := by simp
    have him : (Real.pi * s).im = Real.pi * s.im := by simp
    rw [hre, him]
    exact le_trans (hm s.re hs) (le_add_of_nonneg_right (sq_nonneg _))
  rw [norm_div, norm_pow, Complex.norm_of_nonneg Real.pi_pos.le]
  exact div_le_div_of_nonneg_left Real.pi_pos.le hm0 hsin

end Work.FatouL1
