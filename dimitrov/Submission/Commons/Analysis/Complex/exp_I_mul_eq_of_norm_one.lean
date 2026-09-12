import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Commons.Analysis.Complex

/-! Every unit-modulus complex number equals `exp (σ * I)` for some real `σ`.
A complete proof exists in `Submission/KLCloseB.lean`
(`Submission.KLMain.exists_E_eq_of_norm_one`). -/
theorem exp_I_mul_eq_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) :
    ∃ σ : ℝ, Complex.exp ((σ : ℂ) * Complex.I) = w := by
  refine ⟨(Complex.log w).im, ?_⟩
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have hlog : Complex.exp (Complex.log w) = w := Complex.exp_log hw0
  have hn : ‖Complex.exp (Complex.log w)‖ = 1 := by simpa [hlog] using hw
  have hre : (Complex.log w).re = 0 := by
    have h1 : Real.exp (Complex.log w).re = 1 := by
      rw [Complex.norm_exp] at hn
      exact hn
    exact (Real.exp_eq_one_iff _).mp h1
  have hzI : Complex.log w = ((Complex.log w).im : ℂ) * Complex.I := by
    rw [← Complex.re_add_im (Complex.log w)]
    rw [hre]
    simp
  rw [← hzI]
  exact hlog

end Commons.Analysis.Complex