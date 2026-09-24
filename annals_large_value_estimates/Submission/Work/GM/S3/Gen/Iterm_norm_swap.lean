import Mathlib
import Submission.Work.GM.S3.Iterm_cyclic
import Submission.Work.GM.S3.Iterm_transpose

/-!
# The norm-symmetries of `Iterm` under swapping two slots (with a sign flip)

`Work.GM.S3.Iterm_transpose` (`Iterm(m₂,m₁,m₃) = conj (Iterm(-m₁,-m₂,-m₃))`) and
`Work.GM.S3.Iterm_cyclic` (`Iterm(m₂,m₃,m₁) = Iterm(m₁,m₂,m₃)`) combine to give the two
*norm*-symmetries used by the cell decomposition of GM 7.2 (`Work.GM.S3.Gen.S3_le_cellSum`):

* `norm_Iterm_swap12`: `‖Iterm (m₁,m₂,m₃)‖ = ‖Iterm (-m₂,-m₁,-m₃)‖` — moves the magnitude of slot 1
  into slot 2;
* `norm_Iterm_swap23`: `‖Iterm (m₁,m₂,m₃)‖ = ‖Iterm (-m₁,-m₃,-m₂)‖` — moves the magnitude of slot 3
  into slot 2.

Both maps are involutions of `ℤ³` that preserve the truncation cube
`{m : 0 < |m_i| ≤ K}`, and their images lie in `Λ = {m : |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂|}`, which is why
`Σ_{m ∈ TRUNC} ‖I_m‖ ≤ 3 Σ_{m ∈ Λ ∩ TRUNC} ‖I_m‖`.
-/

namespace Work.GM.S3.Gen

open Submission.GM (Iterm)

/-- Swapping slots 1 and 2 (with a negation of all three) preserves `‖Iterm‖`. -/
theorem norm_Iterm_swap12 (N : ℕ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ) :
    ‖Iterm N W (m₁, m₂, m₃)‖ = ‖Iterm N W (-m₂, -m₁, -m₃)‖ := by
  have h := Iterm_transpose N W m₂ m₁ m₃
  rw [h, norm_star]

/-- Swapping slots 2 and 3 (with a negation of all three) preserves `‖Iterm‖`. -/
theorem norm_Iterm_swap23 (N : ℕ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ) :
    ‖Iterm N W (m₁, m₂, m₃)‖ = ‖Iterm N W (-m₁, -m₃, -m₂)‖ := by
  have h := Iterm_transpose N W m₁ m₃ m₂
  have hc := Iterm_cyclic N W m₃ m₁ m₂
  rw [← hc] at h
  rw [h, norm_star]

end Work.GM.S3.Gen
