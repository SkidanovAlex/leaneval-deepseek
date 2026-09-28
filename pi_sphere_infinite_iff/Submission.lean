import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Work.Serre.serreE3b
import Submission.Work.PiS.Wiring
import Submission.Work.PiS.basepointHomog
import Submission.Work.PiS.lowDegree
import Submission.Work.PiS.circleFacts
import Submission.Work.PiS.degreeInfinite
import Submission.Work.FGThm.sphereFG
import Submission.Work.FGThm.serreFGTheorem
import Submission.Work.EMFG.emHomologyFG
import Submission.Work.SSS.serreFGThreeForTwo
import Submission.Work.Rat.sphereTorsion
import Submission.Work.Rat.hopfInfinite

namespace Submission

theorem pi_sphere_infinite_iff (k n : ℕ) (hn : 1 ≤ n)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Infinite (HomotopyGroup.Pi k (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) ↔
      k = n ∨ (Even n ∧ k + 1 = 2 * n) :=
  have sss := Work.SSS.serreFGThreeForTwo
  have sf := Work.FGThm.sphereFG (Work.FGThm.serreFGTheorem sss (Work.EMFG.emHomologyFG sss))
  have st := Work.Rat.sphereTorsion Work.Serre.serreE3b sf
  Work.PiS.pi_sphere_of_areas Work.PiS.basepointHomog Work.PiS.lowDegree Work.PiS.circleFacts
    Work.PiS.degreeInfinite (Work.Rat.hopfInfinite Work.Serre.serreE3b sf st) sf st k n hn x

end Submission
