import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT

open Matrix

noncomputable section

/-- **The unconditional form of `K0.map` on the class of a matrix, under a clash-free name.**

`Work.KT.K0.map_cls` is currently declared *twice* with different statements:
`Submission/Work/KT/Fund/Basic.lean:168` has the idempotent form `K0.map φ (cls p) = cls (p.map φ)`
(for `p.IsIdem`), while `Submission/Work/KT/Psi/Basic.lean:52` has this unconditional form
`K0.map φ (cls p) = mapCls φ p` (which `Fund/Basic.lean` also proves, under the name
`K0.map_cls'`).  Hence no module can import both `Fund/Basic` and `Psi/Basic`: Lean rejects the
second import with `environment already contains 'Work.KT.K0.map_cls'`.  This is why the headers of
`ballK_dim2`, `ballK_step`, `ball_K`, `sphere_K` and `ext_generator` avoid one of the two chains
(see `Submission/Work/KT/NOTES_susp_bijective_status.md`, §3, item 1).

This module imports only `Defs` and gives the unconditional form under a fresh name, so that the
declaration `K0.map_cls` can be deleted from `Psi/Basic.lean` and the uses in the `Psi/` chain
renamed to this name — which resolves the clash and unblocks the ψ-chain, `ballK_step`, `ball_K`
and hence `hopf_K`. -/
theorem map_cls_uncond {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (p : Mat R) :
    K0.map φ (cls p) = mapCls φ p := by
  -- `K0.map φ` is `QuotientAddGroup.lift (K0Rel R) (FreeAbelianGroup.lift (mapCls φ))`, and
  -- `cls p` is the image of the generator `FreeAbelianGroup.of p`, so the computation is
  -- `lift_mk` followed by `lift_apply_of`.
  unfold K0.map cls
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

end

end Work.KT
