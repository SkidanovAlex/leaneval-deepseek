import Mathlib
import Submission.Work.MotK.TGen.ChartMaps
import Submission.Work.MotK.ChartCompC
import Submission.Work.MotK.UnitChartC

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

/-- `Fdiv a b h = GambT a b h * f̂₄` is the product of the source equation `GambT` of the
T-twisted link (whose non-vanishing is `Work.MotK.GambC_ne_zero`, proved after the rescaling
`GambC = C((a·h)⁻¹)^6 · GambTil`) and of the denominator `f̂₄` of the forward chart map (whose
non-vanishing is `Work.MotK.UnitChartCAux.fhatC_four_ne_zero`).  The corresponding objects of the
`ChartC` development (`GambC`, `fhatC`) are syntactically the same polynomials, so the
identification is `rfl`. -/
theorem FdivNeZero {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Fdiv a b h ≠ 0 := by
  have hF : Fdiv a b h = Work.MotK.GambC K a b h * Work.MotK.fhatC K a b h 4 := rfl
  rw [hF]
  exact mul_ne_zero (Work.MotK.GambC_ne_zero K a b h ha hb hh)
    (Work.MotK.UnitChartCAux.fhatC_four_ne_zero K a b h ha hb hh)

end Work.MotK.TGen
