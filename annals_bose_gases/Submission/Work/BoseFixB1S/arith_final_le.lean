import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseFixB1P.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

theorem arith_final_le {A B C T c : ℝ}
    (hT : A - 2 * c * B + (1 + Real.pi ^ 2) * c ^ 2 * C ≤ T)
    (hAM : 2 * c * B ≤ (1 + Real.pi ^ 2)⁻¹ * A + (1 + Real.pi ^ 2) * c ^ 2 * C) :
    A ≤ (1 + (Real.pi ^ 2)⁻¹) * T := by
  have hp : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hp1 : (0 : ℝ) < 1 + Real.pi ^ 2 := by linarith
  -- From hT and hAM:  A - (1+π²)⁻¹ * A ≤ T.
  have hkey : (1 - (1 + Real.pi ^ 2)⁻¹) * A ≤ T := by nlinarith [hT, hAM]
  have hpos : (0 : ℝ) < 1 + (Real.pi ^ 2)⁻¹ := by positivity
  -- (1 - (1+π²)⁻¹) * (1 + (π²)⁻¹) = 1
  have hid : (1 - (1 + Real.pi ^ 2)⁻¹) * (1 + (Real.pi ^ 2)⁻¹) = 1 := by
    field_simp
    ring
  have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
  calc A = A * ((1 - (1 + Real.pi ^ 2)⁻¹) * (1 + (Real.pi ^ 2)⁻¹)) := by rw [hid, mul_one]
    _ = ((1 - (1 + Real.pi ^ 2)⁻¹) * A) * (1 + (Real.pi ^ 2)⁻¹) := by ring
    _ ≤ T * (1 + (Real.pi ^ 2)⁻¹) := hmul
    _ = (1 + (Real.pi ^ 2)⁻¹) * T := by ring

end Work.BoseFixB1S
