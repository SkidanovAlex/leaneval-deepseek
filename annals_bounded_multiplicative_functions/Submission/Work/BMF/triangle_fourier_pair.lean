import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.tfp.integral_neg_side
import Submission.Work.BMF.tfp.integral_pos_side
import Submission.Work.BMF.tfp.integral_zero_freq
import Submission.Work.BMF.tfp.exp_pair_algebra
import Submission.Work.BMF.tfp.sinc_sq_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial MeasureTheory intervalIntegral

/-- **Triangle/Fejér Fourier pair.** The inverse Fourier transform of the triangle function
`x ↦ max (1-|x|) 0` is the squared sinc: for every real `u`,
`∫_{x=-1}^{1} (1-|x|) e(xu) dx = (sinc (πu))²` where `e(t) = exp(2πit)`. Moreover the Fejér kernel
is bounded below by `4/π²` on `|u| ≤ 1/2`. (Elementary: double integration by parts gives
`2∫_0^1 (1-x)cos(2πxu) dx = 2(1-cos 2πu)/(2πu)² = (sinc πu)²`, and Jordan's inequality
`sin t ≥ 2t/π` on `[0,π/2]` gives `(sinc πu)² ≥ 4/π²` for `|u| ≤ 1/2`.) -/
theorem triangle_fourier_pair :
    (∀ u : ℝ, ∫ x in (-1)..1, (((1 - |x| : ℝ) : ℂ) * eC (x * u)) =
      ((Real.sinc (Real.pi * u)) ^ 2 : ℂ)) ∧
    (∀ u : ℝ, |u| ≤ 1 / 2 → 4 / Real.pi ^ 2 ≤ (Real.sinc (Real.pi * u)) ^ 2) := by
  refine ⟨?_, fun u hu => tfp.sinc_sq_ge u hu⟩
  intro u
  rcases eq_or_ne u 0 with rfl | hu
  · have h1 : (fun x : ℝ => (((1 - |x| : ℝ) : ℂ) * eC (x * 0))) =
        fun x : ℝ => (((1 - |x| : ℝ) : ℂ) * Complex.exp (0 * (x : ℂ))) := by
      funext x; simp only [eC]; ring_nf; simp
    rw [h1, tfp.integral_zero_freq]
    simp
  · set c : ℂ := 2 * Real.pi * Complex.I * u with hcdef
    have hc : c ≠ 0 := by
      rw [hcdef]
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr hu)
    have hpt : ∀ x : ℝ, eC (x * u) = Complex.exp (c * (x : ℂ)) := by
      intro x; rw [hcdef]; simp only [eC, Complex.ofReal_mul]; ring_nf
    rw [intervalIntegral.integral_congr (fun x _ => by rw [hpt x])]
    have hcont : Continuous
        (fun x : ℝ => (((1 - |x| : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))) := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)]
    rw [tfp.integral_neg_side c hc, tfp.integral_pos_side c hc]
    rw [show 1/c - 1/c^2 + Complex.exp (-c)/c^2 + (Complex.exp c / c^2 - 1/c - 1/c^2)
        = (Complex.exp c + Complex.exp (-c) - 2)/c^2 from by field_simp; ring]
    rw [hcdef]
    exact tfp.exp_pair_algebra u hu

end Work.BMF
