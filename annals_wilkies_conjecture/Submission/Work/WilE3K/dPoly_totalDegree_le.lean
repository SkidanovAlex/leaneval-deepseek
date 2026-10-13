import Mathlib
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE9.EaD.eaD_totalDegree_le
import Submission.Work.WilE2.Degree

namespace Work.WilE3K

/-- The symbolic derivative `E.dPoly c` of the lifted system is the EA derivative `eaD E.toChain c`
along the ambient EA chain `E.toChain` (`ETData.dPoly_eq_eaD`), and the EA derivative never raises
the total degree (`Work.WilE9.EaD.eaD_totalDegree_le`). -/
theorem dPoly_totalDegree_le {N rt n re : ℕ} (E : Work.WilE3K.ETData N rt n re)
    (c : Fin (N + 1)) (P : WilkiesDesign.E.EAPoly (N + 1) re) :
    (E.dPoly c P).totalDegree ≤ P.totalDegree := by
  rw [E.dPoly_eq_eaD c P]
  exact Work.WilE9.EaD.eaD_totalDegree_le E.toChain c P

end Work.WilE3K
