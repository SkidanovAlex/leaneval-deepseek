import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Chord
import Submission.Work.Implosion.Ecalle.ecalCoord_cutPt_im

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Chord

open Complex

/-- The height coordinate `chordHeight lam t = log((1+t)/(1−t))/(2λ)` of the cut point
`t·(iλ)` is minus the imaginary part of its Écalle coordinate.  This is immediate from
`Ecalle.ecalCoord_cutPt_im`, which computes that imaginary part as
`−log((1+t)/(1−t))/(2λ)`; passing to the negative gives the height. -/
theorem chordHeight_eq_ecalleHeight (lam : ℝ) (hlam : 0 < lam) (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    chordHeight lam t
      = -(ecalCoord ((lam : ℂ) * I) (cutPt ((lam : ℂ) * I) t)).im := by
  rw [Work.Implosion.Ecalle.ecalCoord_cutPt_im lam hlam t ht]
  simp only [chordHeight]
  ring

end Work.Implosion.Chord
