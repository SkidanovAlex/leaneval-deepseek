import Mathlib
import Submission.Work.QuadraticFields.CertificateReal
import Submission.Work.QuadraticFields.multiQuad_isTotallyReal_of_nonneg

namespace Work.QuadraticFields

theorem gsM_isTotallyReal : NumberField.IsTotallyReal gsM := by
  have hnonneg : ∀ a ∈ gsPrimesQ, 0 ≤ a := by
    intro a ha
    rw [gsPrimesQ] at ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    have hd' : d = 5 ∨ d = 13 ∨ d = 17 ∨ d = 29 ∨ d = 37 ∨ d = 41 ∨ d = 53 := by
      rw [gsPrimes] at hd
      simpa using hd
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  exact multiQuad_isTotallyReal_of_nonneg gsPrimesQ hnonneg

end Work.QuadraticFields
