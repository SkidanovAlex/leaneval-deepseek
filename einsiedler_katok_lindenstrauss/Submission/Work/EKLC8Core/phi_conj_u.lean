import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.phi_conj_uij

namespace Work.EKLC8Core

theorem phi_conj_u (τ r : ℝ) : phi τ * u r * (phi τ)⁻¹ = u (Real.exp (-2 * τ) * r) := by
  have h := phi_conj_uij τ r (i := 0) (j := 1) h01
  have hflow : flowExp 0 - flowExp 1 = (-2 : ℝ) := by norm_num [flowExp]
  rw [hflow] at h
  simpa [u] using h

end Work.EKLC8Core
