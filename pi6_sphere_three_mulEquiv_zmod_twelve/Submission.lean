import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Work.Pi6.Wiring
import Submission.Work.Pi6.mssHolds
import Submission.Work.Pi6.k2zFacts
import Submission.Work.Pi6.emMod2
import Submission.Work.Pi6.emOdd
import Submission.Work.Pi6.eFacts
import Submission.Work.Pi6.serreRangeLES
import Submission.Work.Pi6.sqFacts
import Submission.Work.Pi6.emTableZ
import Submission.Work.Pi6.towerPi
import Submission.Work.Pi6.sqCyclic
import Submission.Work.Pi6.homologyAlg
import Submission.Work.Pi6.basepointMulEquiv

namespace Submission

theorem pi6_sphere_three_mulEquiv_zmod_twelve (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Nonempty
      (HomotopyGroup.Pi 6 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) x ≃*
        Multiplicative (ZMod 12)) := by
  have hM := Work.Pi6.mssHolds
  have hZ := Work.Pi6.k2zFacts hM
  have hM2 := Work.Pi6.emMod2 hM hZ
  have hO := Work.Pi6.emOdd hM hZ
  have hE := Work.Pi6.eFacts hM hZ
  have hR := Work.Pi6.serreRangeLES
  obtain ⟨hC, hX⟩ := Work.Pi6.sqFacts hR hM2
  have hZt := Work.Pi6.emTableZ hR hM2 hO hX
  have hT := Work.Pi6.towerPi
  have hS := Work.Pi6.sqCyclic hR hE hX hC hT
  have hH := Work.Pi6.homologyAlg hR hE hZt hT
  exact Work.Pi6.pi6_of_areas Work.Pi6.basepointMulEquiv hT hE hS hH x

end Submission
