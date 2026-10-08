import Mathlib
import Submission.Work.A7REC.Defs

/-!
# `O₂(C_G(z)) ≤ S`

Area `A7REC` (recognition of `A₇`), file `Basic/V_le_S.lean`.

Let `G` be a finite group satisfying the `A₇` hypotheses (`A7RecCtx G`), `z` the central
involution of the Sylow `2`-subgroup `S`, and `V = O₂(C_G(z)) = pCoreIn 2 (U ⊔ S)` the `2`-core
of the centralizer `H = C_G(z) = U ⊔ S`.  We show `V ≤ S`.

This is the general fact that the `p`-core of a finite group is contained in every Sylow
`p`-subgroup.  Concretely: `S` is a Sylow `2`-subgroup of `H` (it lies in `H` and
`|S| = 8` equals the `2`-part of `|H| = 24`), `O₂(H)` is a normal `2`-subgroup of `H`, and a
normal `p`-subgroup is contained in every Sylow `p`-subgroup
(`IsPGroup.le_sylow_of_normal`).  Transporting back along the inclusion `H ↪ G` gives the claim.

For `G = A₇` and `z = (1 2)(3 4)` this is the familiar statement `O₂(S₄) = V₄ ≤ D₈ = S`.
-/

namespace Work.A7REC.Basic

open Subgroup

/-- **The `p`-core of a group is a `p`-group.**  `O_p(K) = pCore p K` is the normal core of the
supremum `sSup {N ≤ K | N.Normal ∧ IsPGroup p N}` of all normal `p`-subgroups of `K`.  A
supremum of normal `p`-subgroups is a `p`-group (`Sylow.sSup_of_normal`), and a subgroup of a
`p`-group is a `p`-group, so the normal core of that supremum is a `p`-group. -/
theorem isPGroup_pCore (p : ℕ) (K : Type*) [Group K] :
    IsPGroup p (Work.A7REC.pCore p K) := by
  unfold Work.A7REC.pCore
  exact (Sylow.sSup_of_normal _ (fun N hN => hN.2) (fun N hN => hN.1)).to_le
    (Subgroup.normalCore_le _)

/-- **`O₂(C_G(z)) ≤ S`.**  Let `H = C_G(z) = U ⊔ S`.  Then

* `S ≤ H`, so `S` is a Sylow `2`-subgroup of `H` (Mathlib's `Sylow.subtype` restricted to `H`);
* `O₂(H)` is a normal `2`-subgroup of `H` (`isPGroup_pCore` and `pCore_normal`), hence
  `O₂(H) ≤ S` by `IsPGroup.le_sylow_of_normal`;
* `V` is the image of `O₂(H)` under the inclusion `H ↪ G`, so `V ≤ S`. -/
theorem V_le_S (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    ctx.V ≤ (ctx.S : Subgroup G) := by
  set H : Subgroup G := ctx.U ⊔ (ctx.S : Subgroup G) with hH
  have hS_le : (ctx.S : Subgroup G) ≤ H := le_sup_right
  -- `V` is the image in `G` of `O₂(H)` along the inclusion `H ↪ G`.
  have hV : ctx.V = (Work.A7REC.pCore 2 H).map H.subtype := by
    rw [ctx.hVdef, Work.A7REC.pCoreIn, hH]
  -- `O₂(H) ≤ S`, viewed inside `H`, by `IsPGroup.le_sylow_of_normal`.
  have hp : Work.A7REC.pCore 2 H ≤ ((ctx.S.subtype hS_le : Sylow 2 H) : Subgroup H) :=
    IsPGroup.le_sylow_of_normal (isPGroup_pCore 2 H) (ctx.S.subtype hS_le)
  -- the inclusion `H ↪ G` sends `S` (as a subgroup of `H`) back to `S ≤ G`.
  have hmap : (((ctx.S.subtype hS_le : Sylow 2 H)) : Subgroup H).map H.subtype
      = (ctx.S : Subgroup G) := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hS_le]
  calc ctx.V = (Work.A7REC.pCore 2 H).map H.subtype := hV
    _ ≤ (((ctx.S.subtype hS_le : Sylow 2 H)) : Subgroup H).map H.subtype :=
        Subgroup.map_mono hp
    _ = (ctx.S : Subgroup G) := hmap

end Work.A7REC.Basic
