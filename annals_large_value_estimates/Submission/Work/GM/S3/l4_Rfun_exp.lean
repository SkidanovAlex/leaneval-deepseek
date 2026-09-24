import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

/-- `Rfun W v = Σ_{t ∈ W} |v|^{it}` evaluated at `v = e^τ` is `Σ_{t ∈ W} e^{i t τ}`
(the base is a positive real, so `Complex.cpow` unfolds via `Complex.log`). -/
theorem l4_Rfun_exp (W : Finset ℝ) (τ : ℝ) :
    Submission.GM.Rfun W (Real.exp τ) = ∑ t ∈ W, Complex.exp (Complex.I * ((t * τ : ℝ) : ℂ)) := by
  unfold Submission.GM.Rfun
  refine Finset.sum_congr rfl ?_
  intro t ht
  rw [abs_of_pos (Real.exp_pos τ)]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero τ))]
  rw [Complex.ofReal_exp, Complex.log_exp (by simp only [Complex.ofReal_im]; linarith [Real.pi_pos]) (by simp only [Complex.ofReal_im]; linarith [Real.pi_pos])]
  congr 1
  push_cast
  ring

end Work.GM.S3
