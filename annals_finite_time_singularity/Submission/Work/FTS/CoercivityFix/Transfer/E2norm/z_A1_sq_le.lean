import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.C0D_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm

/-- On the open half-line the integrand `(z/(1+z)³)²` of `z_A1_sq_le` coincides with the
integrand `(1/(z(1+z)w(z)))²` of `Work.Coercivity.C0D`: indeed
`z(1+z)w(z) = z(1+z)·(1+z)²/z² = (1+z)³/z` there. -/
private theorem zA1_integrand_eq {z : ℝ} (hz : 0 < z) :
    (z / (1 + z) ^ 3) ^ 2 = (1 / (z * (1 + z) * Work.Spaces.w z)) ^ 2 := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.Spaces.w]
  congr 1
  field_simp

theorem z_A1_sq_le :
    ∫ z in Work.Spaces.Iz, (z / (1 + z) ^ 3) ^ 2 ≤ 1 / 16 := by
  -- `Iz = [0,∞)` and `(0,∞)` differ by the null point `0`
  have hmeas : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz :=
    Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))
  -- on `(0,∞)` the integral is `Work.Coercivity.C0D`
  have hcongr : ∫ z in Set.Ioi (0 : ℝ), (z / (1 + z) ^ 3) ^ 2 = Work.Coercivity.C0D := by
    rw [Work.Coercivity.C0D]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun z hz => zA1_integrand_eq (Set.mem_Ioi.mp hz))
  calc ∫ z in Work.Spaces.Iz, (z / (1 + z) ^ 3) ^ 2
      = ∫ z in Set.Ioi (0 : ℝ), (z / (1 + z) ^ 3) ^ 2 := by rw [← hmeas]
    _ = Work.Coercivity.C0D := hcongr
    _ ≤ 1 / 16 := Work.Coercivity.C0D_le

end Work.FTS.CoercivityFix.Transfer.E2norm
