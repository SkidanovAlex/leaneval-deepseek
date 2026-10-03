import Mathlib
import Submission.Work.FatouL1.cothRealBound
import Submission.Work.FatouL1.cothDecay
import Submission.Work.FatouL1.sinhPiZero

namespace Work.FatouL1

/-- The basic algebraic facts about `cosh`/`sinh` at `iπ` used to see that
`coth (π ·)` is `i`-periodic (i.e. `2i`-periodic in the classical convention:
`coth(π(s+i)) = coth(πs)`). -/
lemma cosh_pi_mul_I : Complex.cosh (Real.pi * Complex.I) = -1 := by
  rw [Complex.cosh, Complex.exp_pi_mul_I, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

lemma sinh_pi_mul_I : Complex.sinh (Real.pi * Complex.I) = 0 := by
  rw [Complex.sinh, Complex.exp_pi_mul_I, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem cothKernel :
    (∀ s : ℂ, Complex.cosh (Real.pi * (s + Complex.I)) / Complex.sinh (Real.pi * (s + Complex.I))
        = Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s)) ∧
    (∀ s : ℂ, Complex.cosh (Real.pi * (-s)) / Complex.sinh (Real.pi * (-s))
        = -(Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s))) ∧
    (∀ s : ℂ, (Complex.sinh (Real.pi * s) = 0 ↔ ∃ n : ℤ, s = (n : ℂ) * Complex.I)) ∧
    (∀ x : ℝ, x ≠ 0 →
      ‖Complex.cosh (Real.pi * (x : ℂ)) / Complex.sinh (Real.pi * (x : ℂ)) - 1 / (Real.pi * (x : ℂ))‖
        ≤ 1) ∧
    (∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s) - 1‖
        ≤ 4 * Real.exp (-2 * Real.pi * s.re)) ∧
    (∀ s : ℂ, s.re ≤ -(1 / 2) →
      ‖Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s) + 1‖
        ≤ 4 * Real.exp (2 * Real.pi * s.re)) := by
  refine ⟨?_, ?_, sinhPiZero, ?_, cothDecay.1, cothDecay.2⟩
  · -- periodicity `s ↦ s + i` : `cosh` and `sinh` both change sign
    intro s
    have h1 : Real.pi * (s + Complex.I) = Real.pi * s + (Real.pi * Complex.I) := by ring
    rw [h1, Complex.cosh_add, Complex.sinh_add, cosh_pi_mul_I, sinh_pi_mul_I]
    ring_nf
  · -- oddness
    intro s
    have h1 : Real.pi * (-s) = -(Real.pi * s) := by ring
    rw [h1, Complex.cosh_neg, Complex.sinh_neg, div_neg]
  · -- real axis: the sole input is the real inequality `|coth y - 1/y| ≤ 1`
    intro x hx
    have hcosh : Complex.cosh (Real.pi * (x : ℂ)) = ((Real.cosh (Real.pi * x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
    have hsinh : Complex.sinh (Real.pi * (x : ℂ)) = ((Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
    have hinv : (1 : ℂ) / (Real.pi * (x : ℂ)) = ((1 / (Real.pi * x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      rw [Complex.ofReal_div (1 : ℝ) (Real.pi * x)]
      norm_num
    have hp : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
    have hbound := cothRealBound (Real.pi * x) hp
    rw [hcosh, hsinh, hinv, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real]
    exact hbound

end Work.FatouL1
