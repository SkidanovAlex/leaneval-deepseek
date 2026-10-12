import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Submission.Commons.Analysis.Integral.radial_integral_three_Ioi
import Submission.Work.BSKinetic.Decomp.ShiftDefs
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.KH

theorem chiB_iteratedFDeriv_le (K : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)),
      0 < ℓ → 0 < d → d ≤ 1 →
      ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖iteratedFDeriv ℝ K
          (fun z : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiB ℓ d u z : ℂ)) z‖
        ≤ D * ((ℓ * d)⁻¹) ^ K := by sorry

end Work.BoseFixB1.KH
