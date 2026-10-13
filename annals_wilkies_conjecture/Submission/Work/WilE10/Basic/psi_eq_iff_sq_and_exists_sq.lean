import Mathlib
import Submission.Work.WilE10.Psi

namespace Work.WilE10.Basic

theorem psi_eq_iff_sq_and_exists_sq {z t : ℝ} :
    z = WilkiesDesign.E.psi t ↔ z ^ 2 * (1 + t ^ 2) = t ^ 2 ∧ ∃ v : ℝ, z * t = v ^ 2 := by
  constructor
  · intro hz
    rw [hz]
    refine ⟨?_, ?_⟩
    · rw [Work.WilE10.psi_sq]
      field_simp
    · have hnn : 0 ≤ WilkiesDesign.E.psi t * t := by
        have hpt : WilkiesDesign.E.psi t * t = t ^ 2 / Real.sqrt (1 + t ^ 2) := by
          rw [WilkiesDesign.E.psi]; field_simp
        rw [hpt]; positivity
      exact ⟨Real.sqrt (WilkiesDesign.E.psi t * t), (Real.sq_sqrt hnn).symm⟩
  · rintro ⟨h1, v, hv⟩
    exact Work.WilE10.psi_eq_of_sq h1 (by rw [hv]; exact sq_nonneg v)

end Work.WilE10.Basic
