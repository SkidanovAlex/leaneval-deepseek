import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.SliceHyp
import Submission.Work.FTS.EllipticEst.Honest.I4SliceBound
import Submission.Work.FTS.EllipticEst.I4SliceAlgebra
import Submission.Work.FTS.EllipticEst.Honest.I4BoundaryVanish
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDivIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeWAux

theorem i4SliceIneq : Work.FTS.EllipticEst.Honest.SliceIneq := by
  intro Φ hsm hA hB
  have hbnd : Filter.Tendsto
      (fun θ => Real.sin θ / (Real.cos θ) ^ 3
        * ((Real.cos θ) ^ 2 * deriv (fun θ' => Φ θ' / Real.cos θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    Work.FTS.EllipticEst.Honest.I4BoundaryVanish
      (fun θ => Φ θ / Real.cos θ)
      (Work.FTS.EllipticEst.Honest.contDiffOn_I4psi Φ hsm)
      (hA.mono_set Set.Ioo_subset_Icc_self)
      (Work.FTS.EllipticEst.Honest.I4SliceDivIntegrable Φ hsm hA hB)
  exact Work.FTS.EllipticEst.Honest.I4SliceBound Φ hsm hA hB
    (Work.FTS.EllipticEst.I4SliceAlgebra Φ hsm) hbnd

end Work.FTS.EllipticEst.H2W.AeWAux
