import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul
import Submission.Commons.NumberTheory.GaussianInt.units_classification
import Submission.Commons.NumberTheory.Diophantine.prime_three_mod_four_dvd_sq_add_sq

namespace Work.FIArea3.JointCount

/-- Uniqueness of the representative of an associate class of Gaussian integers lying in the
fundamental domain `{re > 0, im ≥ 0}`: if `z` and `z'` are associated and both lie in this
region, then `z = z'`.

The units of `ℤ[i]` are `±1, ±i` (`Commons.NumberTheory.GaussianInt.units_classification`);
multiplying a Gaussian integer by each of them in turn moves it to `(-re, -im)`, `(-im, re)` and
`(im, -re)`, only the first of which (`u = 1`) can again satisfy `re > 0, im ≥ 0`. -/
theorem fundUnique {z z' : GaussianInt} (hz : 0 < z.re) (hzi : 0 ≤ z.im)
    (hz' : 0 < z'.re) (hz'i : 0 ≤ z'.im) (h : Associated z z') : z = z' := by
  obtain ⟨u, hu⟩ := h
  have hu' : (u : GaussianInt) = 1 ∨ (u : GaussianInt) = -1 ∨
      (u : GaussianInt) = (⟨0, 1⟩ : GaussianInt) ∨ (u : GaussianInt) = (⟨0, -1⟩ : GaussianInt) :=
    (Commons.NumberTheory.GaussianInt.units_classification (u : GaussianInt)).mp u.isUnit
  rcases hu' with h1 | h1 | h1 | h1
  · rw [h1] at hu; simpa using hu
  · rw [h1] at hu
    have hre : z'.re = -z.re := by rw [← hu]; simp
    omega
  · rw [h1] at hu
    have hre : z'.re = -z.im := by rw [← hu]; simp
    omega
  · rw [h1] at hu
    have him : z'.im = -z.re := by rw [← hu]; simp
    omega

end Work.FIArea3.JointCount
