/-
# The sign-change action on the faces, constraints and orientations of `Q̄`

**Work package W1** of `Submission/Work/NOTES_LEAD_eA.md`.

The group of sign changes (the Klein diagonal `diag(±1,±1,±1,±1)`) acts on `Q̄`, hence on its faces
and on its `48` constraints.  The tables are generated (`Data/QbarAct.lean`) and here given their
meanings:

* `faceActT e f` — the image of the face `f` under the sign change encoded by `e : Fin 16`;
* `consActT e i` — the induced permutation of the `48` constraints of `QbarPD`;
* `oST e f` — the orientation sign of the sign change on the face `f`, normalised (see the
  generator) so that the incidence numbers satisfy
  `inc (faceActT e f) (faceActT e f') = oST e f * oST e f' * inc f f'`;
* `signVecT e` — the sign vector `±1` of the sign change.

Everything is verified in Python by `Submission/Work/MbarHomology/scripts/gen_qbar_act.py` before
the tables are emitted; the Lean counterparts of those checks are `qAct_spec`
(`Submission/Work/MbarHomology/Qbar/qAct_spec.lean`).

These identities are what make the barycentric subdivision of `Q̄` simplicial with respect to the
side pairings (work package W4: the barycentre map is equivariant, hence `face` is well defined on
the orbits of flags) and what makes the subdivision chain of a cell equivariant (work package W7).
-/
import Mathlib
import Submission.Work.MbarHomology.Qbar.CW
import Submission.Work.MbarHomology.Data.QbarAct

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology

open scoped BigOperators

noncomputable section

/-- The sign vector of the sign change encoded by `e : Fin 16` (`0 ↦ +1`, `1 ↦ −1`). -/
def signVecT (e : Fin 16) : Fin 4 → ℤ := fun i => if (e.val / 2 ^ i.val) % 2 = 0 then 1 else -1

/-- The sign change `g` on the faces of `Q̄`. -/
def faceAct (g : Fin 4 → ZMod 2) (f : Fin 865) : Fin 865 := faceActT (Work.FoldInst.enc g) f

/-- The sign change `g` on the `48` constraints of `QbarPD`. -/
def consAct (g : Fin 4 → ZMod 2) (i : Fin 48) : Fin 48 := consActT (Work.FoldInst.enc g) i

/-- The orientation sign of the sign change `g` on the face `f`. -/
def oS (g : Fin 4 → ZMod 2) (f : Fin 865) : ℤ := oST (Work.FoldInst.enc g) f

end

end Work.MbarHomology
