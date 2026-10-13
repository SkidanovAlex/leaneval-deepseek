import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

theorem C0_eq_density (f : ℝ → ℝ → ℝ) :
    Work.Coercivity.C0 f
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          3 * Work.Spaces.K θ * Work.Spaces.Dth f z θ / (z * (1 + z)) := by
  simp only [Work.Coercivity.C0, Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens,
    Work.Coercivity.Transport, Work.Spaces.Iz, Work.Spaces.Iθ]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  congr 1 with z
  congr 1 with θ
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

end Work.FTS.CoercivityFix.Transfer.E2norm
