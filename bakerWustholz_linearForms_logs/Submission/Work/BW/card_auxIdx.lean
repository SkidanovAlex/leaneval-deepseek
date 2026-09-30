import Mathlib
import Submission.Work.BW.auxpolydefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem card_auxIdx (r h D0 : ℕ) (Dj : Fin r → ℕ) :
    Fintype.card (AuxIdx r h D0 Dj) = h * (D0 + 1) * ∏ j, (Dj j + 1) := by
  simp only [AuxIdx, Fintype.card_prod, Fintype.card_fin, Fintype.card_pi]
  ring

end Work.BW
