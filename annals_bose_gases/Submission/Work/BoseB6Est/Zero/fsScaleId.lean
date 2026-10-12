import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB6Est.Zero

/-- **The FS scale identity.**  With the mesh `meshD n = 2π/(n+1)` and the lattice relation
`(n:ℝ)+1 = ℓ √(ρ_z a)`, the one-particle volume factor normalises exactly:

`(2π)⁻³ ℓ³ (ρ_z² a √(ρ_z a³)) (meshD n)³ = ρ_z a`.

Writing `s = √(ρ_z a)` (so `s² = ρ_z a`) and `meshD n = 2π/(ℓ s)`, the left side reduces to
`ρ_z² a · (s a) / s³ = ρ_z² a²/s² = ρ_z a`. -/
theorem fsScaleId {ρz a ℓ : ℝ} (hρz : 0 < ρz) (ha : 0 < a) (hℓ : 0 < ℓ) {n : ℕ}
    (hrel : (n : ℝ) + 1 = ℓ * Real.sqrt (ρz * a)) :
    ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3))
        * (Work.BoseB6.meshD n) ^ 3 = ρz * a := by
  have hρa : 0 < ρz * a := mul_pos hρz ha
  have hsz : 0 < Real.sqrt (ρz * a) := Real.sqrt_pos.mpr hρa
  -- the mesh in terms of the lattice relation
  have hmesh : Work.BoseB6.meshD n = 2 * Real.pi / (ℓ * Real.sqrt (ρz * a)) := by
    rw [Work.BoseB6.meshD, hrel]
  rw [hmesh, mul_div_assoc]
  -- `√(ρ_z a³) = √(ρ_z a) · a`
  have hs3 : Real.sqrt (ρz * a ^ 3) = Real.sqrt (ρz * a) * a := by
    rw [show ρz * a ^ 3 = (ρz * a) * a ^ 2 by ring, Real.sqrt_mul (le_of_lt hρa),
      Real.sqrt_sq (le_of_lt ha)]
  rw [hs3]
  have hsq : Real.sqrt (ρz * a) * Real.sqrt (ρz * a) = ρz * a := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hρa)
  field_simp
  nlinarith [hsq]

end Work.BoseB6Est.Zero
