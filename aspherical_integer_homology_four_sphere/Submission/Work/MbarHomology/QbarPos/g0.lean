import Mathlib
import Submission.Work.MbarHomology.Mbar.Flags
import Submission.Work.MbarHomology.Qbar.Act

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option autoImplicit false

/-!
# The `pos`-equivariance of the sign-change action on the faces of `Q̄` (one group at a time)

The identity `qPos (faceActT e f) i = signVecT e i * qPos f i` (the `pos` component of
`Work.MbarHomology.Qbar.qAct_spec`) is a finite computation over `16 × 865` faces.  A single
`decide` for all of it exhausts memory, so each value of `e : Fin 16` is checked separately and the
file is split into as many modules as the memory budget allows.  Every public theorem below is
derived, at proof level, from one kernel computation over `List.finRange 865`.
-/

namespace Work.MbarHomology.QbarPos

private theorem chk_0 :
    (List.finRange 865).all (fun f => decide (
      qPos (faceActT 0 f) 0 = signVecT 0 0 * qPos f 0 ∧
      qPos (faceActT 0 f) 1 = signVecT 0 1 * qPos f 1 ∧
      qPos (faceActT 0 f) 2 = signVecT 0 2 * qPos f 2 ∧
      qPos (faceActT 0 f) 3 = signVecT 0 3 * qPos f 3)) = true := by decide

theorem qPos_faceActT_0 (f : Fin 865) (i : Fin 4) :
    qPos (faceActT 0 f) i = signVecT 0 i * qPos f i := by
  have h := of_decide_eq_true ((List.all_eq_true.mp chk_0) f (List.mem_finRange f))
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

private theorem chk_1 :
    (List.finRange 865).all (fun f => decide (
      qPos (faceActT 1 f) 0 = signVecT 1 0 * qPos f 0 ∧
      qPos (faceActT 1 f) 1 = signVecT 1 1 * qPos f 1 ∧
      qPos (faceActT 1 f) 2 = signVecT 1 2 * qPos f 2 ∧
      qPos (faceActT 1 f) 3 = signVecT 1 3 * qPos f 3)) = true := by decide

theorem qPos_faceActT_1 (f : Fin 865) (i : Fin 4) :
    qPos (faceActT 1 f) i = signVecT 1 i * qPos f i := by
  have h := of_decide_eq_true ((List.all_eq_true.mp chk_1) f (List.mem_finRange f))
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2


end Work.MbarHomology.QbarPos
