import Mathlib
import Submission.Work.BMF.tent_fourier_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Fourier series of the second Bernoulli polynomial:
`∑_{n ∈ ℤ} e(n t)/n² = 2 π² ({t}² - {t} + 1/6)`.
This is the Fourier expansion of `bernoulliFun 2`, transported from the unit circle
to `ℝ` using `1`-periodicity. -/
theorem bernoulli_eZ_sum (t : ℝ) :
    HasSum (fun n : ℤ => (1 : ℂ) / (n : ℂ) ^ 2 * eZ ((n : ℝ) * t))
      ((2 * Real.pi ^ 2) * phiC t) := by
  have ht₀ : Int.fract t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨Int.fract_nonneg t, le_of_lt (Int.fract_lt_one t)⟩
  have h := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun (k := 2) (by norm_num) ht₀
  have hS : -(2 * ↑Real.pi * Complex.I) ^ (2:ℕ) / ↑(2:ℕ).factorial *
      ↑(bernoulliFun 2 (Int.fract t)) = (2 * Real.pi ^ 2) * phiC t := by
    rw [bernoulliFun_two, phiC_apply]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [hS] at h
  refine h.congr_fun (fun n => ?_)
  have key : (fourier n) ((Int.fract t : ℝ) : UnitAddCircle) = eZ ((n:ℝ)*t) := by
    rw [← fourier_coe_eq_eZ n t]
    rw [coe_fract_eq t]
  rw [key]

end Work.BMF
