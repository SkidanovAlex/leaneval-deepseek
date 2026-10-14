import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Basic.ENNReal.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.SolutionDelivery.DatumCut.datumData_of_cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.DatumCut

open FiniteTimeSingularity MeasureTheory

/-! ## The `C^{0,α}` class of the cut-off datum

`cutDatum L ω = chi(ρ/L) • ω` is supported in the ball of radius `2L`, so although `ω` itself
need not be bounded (only its derivative is), the cut-off datum is.  Being `C^{1,α}` with
bounded derivative it is Lipschitz, and a bounded Lipschitz function is `α`-Hölder for `α ≤ 1`
(`Work.Stability.HolderOfBoundedLipschitz`). -/



end Work.SolutionDelivery.DatumCut
end
-- ===== merged: Submission.Work.SolutionDelivery.HolderInputs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

variable {α : NNReal}

namespace ConstructedSolution

variable (C : ConstructedSolution α)



end ConstructedSolution

end Work.SolutionDelivery
end
end
