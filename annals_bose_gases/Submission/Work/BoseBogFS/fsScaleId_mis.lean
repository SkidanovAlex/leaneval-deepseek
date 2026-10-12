import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

theorem fsScaleId_mis {n : ℕ} {ρz a ℓ : ℝ} (hρz : 0 < ρz) (ha : 0 < a) (hℓ : 0 < ℓ) :
    (((n : ℝ) + 1) / (ℓ * Real.sqrt (ρz * a))) ^ 3
        * (((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3))
            * (Work.BoseB6.meshD n) ^ 3)
      = ρz * a := by
  have hρa : 0 < ρz * a := mul_pos hρz ha
  have hs : 0 < Real.sqrt (ρz * a) := Real.sqrt_pos.mpr hρa
  have hs3 : Real.sqrt (ρz * a ^ 3) = Real.sqrt (ρz * a) * a := by
    rw [show ρz * a ^ 3 = (ρz * a) * a ^ 2 by ring, Real.sqrt_mul (le_of_lt hρa),
      Real.sqrt_sq (le_of_lt ha)]
  have hsq : Real.sqrt (ρz * a) * Real.sqrt (ρz * a) = ρz * a := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hρa)
  rw [Work.BoseB6.meshD, hs3]
  field_simp
  nlinarith [hsq]

end Work.BoseBogFS
