import Mathlib
import Submission.Work.Drive.Final.dent_annulus_defs

/-!
# Linear forms on `ℝ × ℝ` with vanishing transverse determinant are proportional

`Work.Drive.Final.det2 L D` is the determinant of the `2 × 2` matrix of the two linear forms
`L, D : ℝ × ℝ →L[ℝ] ℝ` in the standard basis.  If `D ≠ 0` then `det2 L D = 0` forces `L` to be a
scalar multiple of `D`: a nonzero linear form on a two-dimensional space has a one-dimensional
kernel, and a form that is linearly dependent on it is proportional to it.

The proof is elementary: a nonzero functional is nonzero on one of the two basis vectors, and the
vanishing of the determinant is exactly the statement that the two coordinate pairs are linearly
dependent, at which point the multiplier is the ratio of the coordinates.
-/

namespace Work.Drive.Final

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on the two basis
vectors `(1, 0)` and `(0, 1)`. -/
private lemma clm_ext_pair {L M : (ℝ × ℝ) →L[ℝ] ℝ}
    (h1 : L (1, 0) = M (1, 0)) (h2 : L (0, 1) = M (0, 1)) : L = M := by
  apply ContinuousLinearMap.ext
  intro x
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hx]
  simp only [map_add, map_smul, h1, h2]

/-- **A vanishing transverse determinant makes the two forms proportional**: if `D ≠ 0` and
`det2 L D = 0` then `L = t • D` for some real `t`. -/
theorem exists_smul_of_det2_eq_zero {L D : (ℝ × ℝ) →L[ℝ] ℝ} (hD : D ≠ 0)
    (h : det2 L D = 0) : ∃ t : ℝ, L = t • D := by
  have hab : D ((1 : ℝ), (0 : ℝ)) ≠ 0 ∨ D ((0 : ℝ), (1 : ℝ)) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hD (clm_ext_pair (by rw [hc.1]; simp) (by rw [hc.2]; simp))
  rw [det2] at h
  rcases hab with hd | hd
  · refine ⟨L (1, 0) / D (1, 0), ?_⟩
    apply clm_ext_pair
    · rw [smul_apply, smul_eq_mul, div_mul_eq_mul_div,
        mul_div_cancel_right₀ _ hd]
    · rw [smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hd]
      linarith
  · refine ⟨L (0, 1) / D (0, 1), ?_⟩
    apply clm_ext_pair
    · rw [smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hd]
      linarith
    · rw [smul_apply, smul_eq_mul, div_mul_eq_mul_div,
        mul_div_cancel_right₀ _ hd]

end Work.Drive.Final
