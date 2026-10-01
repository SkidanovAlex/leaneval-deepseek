import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.tf72f_moment

namespace Work.OffAxis

/-- HB Lemma 7.2's weight is the quintic `g72 y = (1/30)(32 - 40 y^2 + 20 y^3 - y^5)`;
this is the polynomial identity `(2 - y)^3 (4 + 6 y + y^2) = 32 - 40 y^2 + 20 y^3 - y^5`. -/
lemma g72_eq_poly (y : ℝ) :
    Work.ZeroFreeTables.g72 y = (32/30) + (-(40/30))*y^2 + (20/30)*y^3 + (-(1/30))*y^5 := by
  simp only [Work.ZeroFreeTables.g72]
  ring

theorem G72MomentClosed (m : ℕ) :
    (∫ y in (0:ℝ)..2, y^m * Work.ZeroFreeTables.g72 y)
      = (16 * (2:ℝ)^(m+1) / 15) *
          (1/((m:ℝ)+1) - 5/((m:ℝ)+3) + 5/((m:ℝ)+4) - 1/((m:ℝ)+6)) := by
  -- `g72` is the quintic `(1/30)(32 - 40y² + 20y³ - y⁵)`, so the moment is a
  -- linear combination of four monomial integrals.
  have hcongr : (∫ y in (0:ℝ)..2, y^m * Work.ZeroFreeTables.g72 y)
      = ∫ y in (0:ℝ)..2,
          y^m * ((32/30) + (-(40/30))*y^2 + (20/30)*y^3 + (-(1/30))*y^5) := by
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [g72_eq_poly]
  rw [hcongr, Work.ZeroFreeTables.tf72f_moment_lin m 2 (32/30) (-(40/30)) (20/30) (-(1/30))]
  -- Pull out the common factor `2^(m+1)`.
  have h3 : (2:ℝ)^(m+3) = 2^(m+1) * 4 := by
    rw [show m+3 = (m+1)+2 by omega, pow_add]; norm_num
  have h4 : (2:ℝ)^(m+4) = 2^(m+1) * 8 := by
    rw [show m+4 = (m+1)+3 by omega, pow_add]; norm_num
  have h6 : (2:ℝ)^(m+6) = 2^(m+1) * 32 := by
    rw [show m+6 = (m+1)+5 by omega, pow_add]; norm_num
  rw [h3, h4, h6]
  have hm1 : ((m:ℝ)+1) ≠ 0 := by positivity
  have hm3 : ((m:ℝ)+3) ≠ 0 := by positivity
  have hm4 : ((m:ℝ)+4) ≠ 0 := by positivity
  have hm6 : ((m:ℝ)+6) ≠ 0 := by positivity
  field_simp
  ring

end Work.OffAxis
