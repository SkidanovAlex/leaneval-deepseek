import Mathlib

namespace Work.Pert

/-- The nearest integer to `s.re` realises the infimum of the distances from `s` to the
lattice `ℤ ⊂ ℂ`; the real part of the difference is at most `1/2` in modulus. -/
theorem iInf_dist_eq_norm_sub_round (s : ℂ) :
    ∃ m : ℤ, |(s - (m : ℂ)).re| ≤ 1 / 2 ∧
      (⨅ k : ℤ, dist s (k : ℂ)) = ‖s - (m : ℂ)‖ := by
  refine ⟨round s.re, ?_, ?_⟩
  · -- `round s.re` is within `1/2` of `s.re`
    rw [Complex.sub_re, Complex.intCast_re]
    simpa using abs_sub_round s.re
  · -- ... and no integer is closer to `s`
    have hmin : ∀ k : ℤ, dist s ((round s.re : ℤ) : ℂ) ≤ dist s (k : ℂ) := by
      intro k
      -- comparing squared moduli reduces to comparing squared distances of real parts
      have habs : |s.re - ((round s.re : ℤ) : ℝ)| ≤ |s.re - (k : ℝ)| := by
        simpa using round_le s.re k
      have hsq' : (s.re - ((round s.re : ℤ) : ℝ)) ^ 2 ≤ (s.re - (k : ℝ)) ^ 2 :=
        (sq_le_sq).mpr habs
      have hsq : ‖s - (((round s.re : ℤ)) : ℂ)‖ ^ 2 ≤ ‖s - ((k : ℤ) : ℂ)‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.intCast_re, Complex.intCast_im,
          sub_zero]
        nlinarith [hsq']
      rw [dist_eq_norm, dist_eq_norm]
      have h := (sq_le_sq).mp hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h
    have hbdd : BddBelow (Set.range (fun k : ℤ => dist s (k : ℂ))) :=
      ⟨0, by rintro _ ⟨k, rfl⟩; exact dist_nonneg⟩
    have key : (⨅ k : ℤ, dist s (k : ℂ)) = dist s ((round s.re : ℤ) : ℂ) :=
      le_antisymm (ciInf_le hbdd _) (le_ciInf hmin)
    simpa [dist_eq_norm] using key

end Work.Pert
