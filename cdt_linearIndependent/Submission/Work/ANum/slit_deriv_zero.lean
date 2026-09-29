import Mathlib
import Submission.Work.APsi.defs
import Submission.Work.APsi.slit_facts

/-! # The derivative of the slit map at `0`

Uses the removable-singularity factorization `slit r z = z * G z` with
`G z = -8r/(slitR r z - slitP r z)` (holomorphic and non-vanishing near `0`), together with
`slitR r 0 - slitP r 0 = -2(1+r)²`.  Hence `slit r '(0) = G 0 = -8r/(-2(1+r)²) = 4r/(1+r)²`. -/

namespace Work.ANum

open Submission.CDTPlan Complex
open Work.APsi

theorem slit_deriv_zero (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (slit r) (4 * r / (1 + r) ^ 2) 0 := by
  have hGdiff : DifferentiableAt ℂ (fun z : ℂ => -8 * (r : ℂ) / (slitR r z - slitP r z)) 0 := by
    have hden : DifferentiableAt ℂ (fun z : ℂ => slitR r z - slitP r z) 0 :=
      ((differentiableOn_slitR r hr hr1).differentiableAt (Metric.ball_mem_nhds 0 one_pos)).sub
        ((differentiable_slitP r).differentiableAt)
    exact (differentiableAt_const (-8 * (r : ℂ))).div hden (slitRP_ne r hr 0)
  have hG : HasDerivAt (fun z : ℂ => -8 * (r : ℂ) / (slitR r z - slitP r z))
      (deriv (fun z : ℂ => -8 * (r : ℂ) / (slitR r z - slitP r z)) 0) 0 := hGdiff.hasDerivAt
  have h1 : HasDerivAt (fun z : ℂ => z) 1 0 := hasDerivAt_id 0
  have h2 : HasDerivAt (fun z : ℂ => z * (-8 * (r : ℂ) / (slitR r z - slitP r z)))
      (1 * (-8 * (r : ℂ) / (slitR r 0 - slitP r 0)) +
        0 * deriv (fun z : ℂ => -8 * (r : ℂ) / (slitR r z - slitP r z)) 0) 0 :=
    h1.mul hG
  have hval : (1 : ℂ) * (-8 * (r : ℂ) / (slitR r 0 - slitP r 0)) +
        0 * deriv (fun z : ℂ => -8 * (r : ℂ) / (slitR r z - slitP r z)) 0 =
      4 * (r : ℂ) / (1 + (r : ℂ)) ^ 2 := by
    rw [slitR0 r hr]
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    have h1r : (1 + (r : ℂ)) ≠ 0 := by
      have : (0:ℝ) < 1 + r := by linarith
      exact_mod_cast ne_of_gt this
    field_simp
    ring
  have h2' : HasDerivAt (fun z : ℂ => z * (-8 * (r : ℂ) / (slitR r z - slitP r z)))
      (4 * (r : ℂ) / (1 + (r : ℂ)) ^ 2) 0 := h2.congr_deriv hval
  have hfun : (fun z : ℂ => z * (-8 * (r : ℂ) / (slitR r z - slitP r z))) = slit r := by
    funext z; exact (slit_mul r hr z).symm
  rw [hfun] at h2'
  exact h2'

end Work.ANum
