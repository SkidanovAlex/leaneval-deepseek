import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Real

theorem sqrt_iff_sq {t s d : ℝ} (ht : 0 ≤ t) (hd : 0 ≤ d) :
    (s ∈ Set.Icc (-t) t ∧ d ≤ Real.sqrt (t ^ 2 - s ^ 2)) ↔ s ^ 2 + d ^ 2 ≤ t ^ 2 := by
  have htabs : |t| = t := abs_of_nonneg ht
  constructor
  · rintro ⟨hs, hds⟩
    obtain ⟨hs1, hs2⟩ := hs
    have hle : |s| ≤ |t| := by
      rw [htabs]; exact abs_le.mpr ⟨hs1, hs2⟩
    have hs_sq : s ^ 2 ≤ t ^ 2 := sq_le_sq.mpr hle
    have hsub : 0 ≤ t ^ 2 - s ^ 2 := by linarith
    have hd_sq : d ^ 2 ≤ t ^ 2 - s ^ 2 := (Real.le_sqrt hd hsub).mp hds
    linarith
  · intro h
    have hs_sq : s ^ 2 ≤ t ^ 2 := by nlinarith [sq_nonneg d]
    have hsub : 0 ≤ t ^ 2 - s ^ 2 := by linarith
    have hle : |s| ≤ |t| := sq_le_sq.mp hs_sq
    refine ⟨abs_le.mp (by rwa [htabs] at hle), ?_⟩
    exact (Real.le_sqrt hd hsub).mpr (by linarith)

end Commons.Analysis.Real