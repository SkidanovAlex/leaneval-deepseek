import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Liouville

theorem biotSavart_congr_ae {ω ω' : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (h : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure Work.FTS.BSIdent.R3), ω y = ω' y)
    (x : Work.FTS.BSIdent.R3) :
    Work.LWP.biotSavart ω x = Work.LWP.biotSavart ω' x := by
  unfold Work.LWP.biotSavart
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

end Work.FTS.BSIdent.Liouville
