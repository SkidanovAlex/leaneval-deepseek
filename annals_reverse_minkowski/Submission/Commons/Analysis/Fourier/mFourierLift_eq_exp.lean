import Mathlib.Analysis.Fourier.AddCircleMulti

open Complex
open scoped Real

namespace Commons.Analysis.Fourier

theorem mFourierLift_eq_exp (n : ℕ) (m : Fin n → ℤ) (x : Fin n → ℝ) :
    (UnitAddTorus.mFourier (-m) (fun i : Fin n => (x i : UnitAddCircle))) =
      cexp (-(2 * π * I : ℂ) * (∑ i : Fin n, x i * (m i : ℝ) : ℂ)) := by
  change (∏ i : Fin n, fourier ((-m) i) ((x i : UnitAddCircle))) =
      cexp (-(2 * π * I : ℂ) * (∑ i : Fin n, x i * (m i : ℝ) : ℂ))
  simp only [Pi.neg_apply]
  have hf : ∀ i : Fin n, fourier (-(m i)) ((x i : UnitAddCircle)) =
      cexp (-(2 * π * I : ℂ) * (x i : ℂ) * (m i : ℂ)) := by
    intro i
    rw [fourier_coe_apply (T := 1)]
    congr 1
    norm_num
    ring_nf
  calc
    (∏ i : Fin n, fourier (-(m i)) ((x i : UnitAddCircle)))
        = ∏ i : Fin n, cexp (-(2 * π * I : ℂ) * (x i : ℂ) * (m i : ℂ)) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hf i
    _ = cexp (∑ i : Fin n, (-(2 * π * I : ℂ) * (x i : ℂ) * (m i : ℂ))) := by
            rw [← Complex.exp_sum]
    _ = cexp (-(2 * π * I : ℂ) * (∑ i : Fin n, x i * (m i : ℝ) : ℂ)) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            push_cast
            ring

end Commons.Analysis.Fourier