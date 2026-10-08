import Mathlib
import Submission.Work.A7REC.Defs

/-!
# `V ≤ C_G(z)`

Area `A7REC` (recognition of `A₇`), file `Basic/V_le_C.lean`.

Let `G` be a finite group satisfying the `A₇` hypotheses (`A7RecCtx G`).  Here `z` is the central
involution of a Sylow `2`-subgroup `S`, and

`V = O₂(C_G(z)) = pCoreIn 2 (U ⊔ S)`

is the `2`-core of the centralizer `C_G(z) = U ⊔ S` (the `pCoreIn` is the image in `G` of the
`2`-core of the subgroup `U ⊔ S`).  Since the `p`-core of a group is by definition a subgroup of
that group, `V` lands in `U ⊔ S = C_G(z)`; nothing else is used.  In particular `V` is
centralized by `z`, which is the content of this file.
-/

namespace Work.A7REC.Basic

/-- **`V` lies in `U ⊔ S = C_G(z)`.**  `V = pCoreIn 2 (U ⊔ S)` is the image in `G` of a subgroup
of `U ⊔ S` under the inclusion `U ⊔ S ↪ G`, hence is contained in `U ⊔ S`. -/
theorem V_le_join (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    ctx.V ≤ ctx.U ⊔ (ctx.S : Subgroup G) := by
  rw [ctx.hVdef]
  exact Subgroup.map_subtype_le _

/-- **`V ≤ C_G(z)`.**  Immediate from `V ≤ U ⊔ S` and `C_G(z) = U ⊔ S`. -/
theorem V_le_C (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    ctx.V ≤ Subgroup.centralizer ({ctx.z} : Set G) := by
  rw [ctx.hCz]
  exact V_le_join G ctx

end Work.A7REC.Basic
