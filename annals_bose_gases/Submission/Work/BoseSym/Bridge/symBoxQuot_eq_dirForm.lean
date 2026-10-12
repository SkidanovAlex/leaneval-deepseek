import ChallengeDeps
import Submission.Work.BoseSym.BoxTest
import Submission.Work.BoseSym.Bridge.gSq_graphPoint_box
import Submission.Work.BoseSym.Bridge.l2Sq_graphPoint_box
import Submission.Work.BoseSym.Bridge.potSq_graphPoint_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Bridge
open MeasureTheory
open BoseGases
open Submission.BoseGases

theorem symBoxQuot_eq_dirForm {N : ℕ} {L : ℝ} {W : Conf N → ℝ} (Ψ : SymState N L) :
    (intBox N L (fun x => ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ (Ψ : Conf N → ℝ) x (eDir N i k)) ^ 2)
      + intBox N L (fun x => W x * ((Ψ : Conf N → ℝ) x) ^ 2))
      / intBox N L (fun x => ((Ψ : Conf N → ℝ) x) ^ 2)
    = dirForm W (graphPoint N L (symBoxToTest N L Ψ)) / l2Sq (graphPoint N L (symBoxToTest N L Ψ)) := by
  rw [dirForm, gSq_graphPoint_box, potSq_graphPoint_box, l2Sq_graphPoint_box]
  simp only [symBoxToTest_coe]

end Work.BoseSym.Bridge
