import Mathlib.Analysis.Normed.Field.Basic
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Algebra

theorem meridianResid_algebra_dyn {p z r ρsq Z a sp κ₁ κ₂ f fτ f1 f2 g g1 g2 : ℝ}
    (hr : r ≠ 0) (hρ : ρsq = r ^ 2 + z ^ 2) :
    κ₁ * sp * a * f + a * sp * fτ + a * κ₂ * sp * Z * f1
      + (a * (2 * z * g + p * Z * z * g1 + r * g2))
          * (a * (f1 * (p * Z * (r / ρsq)) - f2 * (z / ρsq)))
      + (-(ρsq * (a * g) / r) - a * (2 * r * g + p * Z * r * g1 - z * g2))
          * (a * (f1 * (p * Z * (z / ρsq)) + f2 * (r / ρsq)))
      - (a * (2 * z * g + p * Z * z * g1 + r * g2) / r) * (a * f)
      = a * sp * (fτ + κ₁ * f + κ₂ * (Z * f1))
        + (a ^ 2 / 2) * (2 * (-3 * g - p * Z * g1) * f2
            + 2 * p * (g2 - (z / r) * g) * (Z * f1)
            - 2 * ((2 * z * g + p * z * Z * g1 + r * g2) / r) * f) := by
  subst hρ
  have h : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Work.FTS.MeridianDyn.Algebra
