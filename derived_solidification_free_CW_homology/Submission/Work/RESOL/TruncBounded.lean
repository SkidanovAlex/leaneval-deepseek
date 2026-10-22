import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.ResEps
import Submission.Work.RESOL.hasAtomicTerms_R
import Submission.Work.RESOL.isBoundedAbove_R
import Submission.Work.RESOL.solidCofibrant_trunc
import Submission.Work.RESOL.isIso_sigmaDesc_of_zero_complement
import Submission.Work.RESOL.exists_windowTower

open CategoryTheory Limits LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL


/-! ## Boundedness of the brutal truncation -/

/-- The brutal truncation of a bounded-above complex is bounded above. -/
theorem isBoundedAbove_trunc (m : ℤ) {B : Cpx} (hB : IsBoundedAbove B) :
    IsBoundedAbove (trunc m B) := by
  obtain ⟨b, hb⟩ := hB
  refine ⟨max m b, fun n hn => ?_⟩
  by_cases hm : m ≤ n
  · rw [trunc_X_of_le B m hm]
    exact hb n (by omega)
  · rw [trunc_X_of_not_le B m hm]
    exact isZero_zero LightCondAb

/-- The brutal truncation of a complex is bounded below. -/
theorem isBoundedBelow_trunc (m : ℤ) (B : Cpx) : IsBoundedBelow (trunc m B) := by
  refine ⟨m, fun n hn => ?_⟩
  exact isZero_trunc_X B m (by omega)

end Work.RESOL

end
