import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Cauchy.bmCz

/-- Decompose a complex vector into its real and imaginary components along the
standard coordinate directions, viewed as real basis vectors. -/
private lemma decompose_complex_vector {n : ℕ} (v : Fin n → ℂ) :
    v = ∑ k, ((v k).re • ((Pi.single k (1 : ℂ) : Fin n → ℂ))
        + (v k).im • ((Pi.single k Complex.I : Fin n → ℂ))) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [Complex.real_smul]
  · intro k _ hk
    simp [Pi.single_eq_of_ne (Ne.symm hk)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem fderiv_eq_sum_wirtinger {n : ℕ} (u : (Fin n → ℂ) → ℂ) (z v : Fin n → ℂ) :
    fderiv ℝ u z v = ∑ k, ((v k).re * (fderiv ℝ u z (Pi.single k (1 : ℂ)))
      + (v k).im * (fderiv ℝ u z (Pi.single k Complex.I))) := by
  conv_lhs => rw [decompose_complex_vector v]
  rw [map_sum]
  simp only [map_add, map_smul, Complex.real_smul]

end Work.CR.Flat.Cauchy.bmCz
