import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6 — the value of the Bogoliubov model integral at `c = 8π`

`lhyValue c = c ^ (5/2) · 64π/(15√2)` is the value of the dimensionless
Bogoliubov model integral of FS `lem:BogIntegral`, while
`lhySharp = 128/(15√π)` is the sharp Lee–Huang–Yang constant.  At the material
value `c = 8π` of the small-box density parameter the two expressions agree:

  `lhyValue (8π) = 64π⁴ · lhySharp`.

Both sides reduce to the common value `8192/15 · π³√π`; the proof is the
elementary `rpow`/`sqrt` bookkeeping recorded in the three helper lemmas below.
-/

noncomputable section

namespace Work.BoseB6

/-- `8 ^ (5/2) = 128√2`. -/
lemma eight_rpow_five_halves : (8 : ℝ) ^ (5 / 2 : ℝ) = 128 * Real.sqrt 2 := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 8), Real.rpow_two]
  rw [← Real.sqrt_eq_rpow]
  rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show Real.sqrt (4 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

/-- `π ^ (5/2) = π² √π`. -/
lemma pi_rpow_five_halves : Real.pi ^ (5 / 2 : ℝ) = Real.pi ^ 2 * Real.sqrt Real.pi := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_two,
      ← Real.sqrt_eq_rpow]

/-- `π⁴/√π = π³√π` (since `√π · √π = π`). -/
lemma pi_pow_four_div_sqrt :
    (Real.pi : ℝ) ^ 4 / Real.sqrt Real.pi = Real.pi ^ 3 * Real.sqrt Real.pi := by
  rw [div_eq_iff (by positivity : Real.sqrt Real.pi ≠ 0)]
  rw [show Real.pi ^ 3 * Real.sqrt Real.pi * Real.sqrt Real.pi
        = Real.pi ^ 3 * (Real.sqrt Real.pi * Real.sqrt Real.pi) by ring,
      show Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi by
        rw [← sq, Real.sq_sqrt Real.pi_pos.le]]
  ring

/-- The left-hand side at `c = 8π` is `8192/15 · π³√π`. -/
lemma lhyValue_eight_pi_lhs :
    lhyValue (8 * Real.pi) = 8192 / 15 * Real.pi ^ 3 * Real.sqrt Real.pi := by
  unfold lhyValue
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) Real.pi_pos.le,
      eight_rpow_five_halves, pi_rpow_five_halves]
  field_simp
  ring

/-- The right-hand side at `c = 8π` is `8192/15 · π³√π`. -/
lemma sixtyfour_pi4_lhySharp :
    (64 : ℝ) * Real.pi ^ 4 * lhySharp = 8192 / 15 * Real.pi ^ 3 * Real.sqrt Real.pi := by
  unfold lhySharp
  have h1 : (64 : ℝ) * Real.pi ^ 4 * (128 / (15 * Real.sqrt Real.pi))
      = (64 * 128 / 15) * (Real.pi ^ 4 / Real.sqrt Real.pi) := by
    rw [show (128 : ℝ) / (15 * Real.sqrt Real.pi)
          = (128 / 15) / Real.sqrt Real.pi by ring]
    ring
  rw [h1, pi_pow_four_div_sqrt]
  ring

theorem lhyValue_eight_pi : Work.BoseB6.lhyValue (8 * Real.pi) = 64 * Real.pi ^ 4 * Work.BoseB6.lhySharp := by
  rw [lhyValue_eight_pi_lhs, sixtyfour_pi4_lhySharp]

end Work.BoseB6

end
