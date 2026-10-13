import Mathlib
import Submission.Work.WilE2.KhoSphereDefs

namespace Work.WilE2

/-- Each component `w ↦ (S.liftChain).ev (liftP (F i)) w` of the lifted system map is the
evaluation of an EA polynomial along the (fixed) lifted chain `S.liftChain`; being
(Fréchet) differentiable everywhere (`ev_hasFDerivAt`), it is continuous. -/
theorem continuous_liftSystem {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    Continuous (liftSystem S F) := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_iff_continuousAt.mpr
    (fun x => (ev_hasFDerivAt S.liftChain (liftP (F i)) x).continuousAt)

end Work.WilE2
