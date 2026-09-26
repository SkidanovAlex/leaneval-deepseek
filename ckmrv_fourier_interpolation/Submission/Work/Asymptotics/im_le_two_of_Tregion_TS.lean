import Mathlib
import Submission.Work.Asymptotics.TSasm.layerSemi_Tregion

/-!
# `Im u ≤ 2` on the cusp-`0` half tile `Tregion`

`Work.Asymptotics.im_le_two_of_Tregion` is proved in `Submission/Work/Asymptotics/TSasm/
cuspOneBandLadderSmall_TS.lean`, which cannot be imported together with the `TSasm` layer chain
(it declares a second copy of `Work.Asymptotics.layer_agreement_shift`).  The five-line proof is
repeated here on an importable module so that the geometry lemmas of the `TSasm` branch can use it.

The statement is elementary: `Tregion` contains the inequality `‖u‖² ≤ 2 Im u`, i.e.
`Re(u)² + (Im u - 1)² ≤ 1`, whence `Im u ≤ 2`.
-/

namespace Work.Asymptotics

open UpperHalfPlane

/-- `Im u ≤ 2` for `u ∈ Tregion`. -/
lemma im_le_two_of_Tregion_TS {u : ℍ} (hu : u ∈ Work.Asymptotics.Tregion) : u.im ≤ 2 := by
  have h := (ts_Tregion_ineqs hu).2
  have hsq : ‖(u : ℂ)‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := ts_normSq_coe u
  have him : 0 < u.im := u.im_pos
  nlinarith [h, hsq, sq_nonneg u.re, sq_nonneg u.im, sq_nonneg (u.im - 1)]

end Work.Asymptotics
