/-
Area `A7REC` (recognition of `A₇`): **the interface file**.

Import this module to get, in one line, everything the area currently proves:

* the contract statement `Work.A7REC.A7RecProp` and the hypothesis bundle `Work.A7REC.A7RecCtx`;
* the residual statements `A7IndexSevenProp`, `A7Subgroup360Prop` and the reductions
  `a7RecProp_of_indexSeven`, `a7RecProp_of_subgroup360`;
* the index-`7` recognition `Work.A7REC.mulEquiv_A7_of_index_seven`;
* the local structure of a group satisfying the hypotheses, collected in `A7LocalFacts`.

`NOTES_A7REC_design.md` describes the area; `NOTES_Suzuki_transcription.md` transcribes Suzuki
1959 §5/§6/§8; `NOTES_A7Y6Values_correction.md` explains the correction of the C1e leaf.

**The deliverable of the area** (the degree-`6` character route of Suzuki §8) is *not* in this
file; import

```lean
import Submission.Work.A7REC.Char.Char6   -- C1 + C2+C3; the one-class input comes from area FUS
```

which provides `Work.A7REC.a7Char6 (hone) : A7Char6Prop` and
`Work.A7REC.a7Rec2Prop_of_leaves (hone) : A7Rec2Prop`, both of whose axiom closures are
`[propext, Classical.choice, Quot.sound]`; `Work.A7REC.a7RecProp_of_A7Rec2Prop` then gives the
contract statement `A7RecProp` once the induction premise `SmallerDGroups` is available.

The one-class input `hone` itself is supplied by area `FUS` through
`Submission/Work/A7REC/OneInvClass.lean`:

```lean
import Submission.Work.A7REC.OneInvClass
-- Work.A7REC.oneInvClass_of_fusion : Work.GW2.InvolutionFusionProp → hone
-- Work.A7REC.a7Rec2Prop_of_fusion : Work.GW2.InvolutionFusionProp → A7Rec2Prop
```

so a caller holding `Work.FUS.involutionFusionProp` gets `A7Rec2Prop` in one application.
-/
import Mathlib
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.IndexSeven
import Submission.Work.A7REC.Reduction
import Submission.Work.A7REC.Basic.card_S
import Submission.Work.A7REC.Basic.U_inf_S
import Submission.Work.A7REC.Basic.card_centralizer_z
import Submission.Work.A7REC.Basic.V_le_C
import Submission.Work.A7REC.Basic.V_le_S
import Submission.Work.A7REC.Basic.four_subgroups_of_S
import Submission.Work.A7REC.Basic.local
import Submission.Work.A7REC.Join.card_sup_of_le_normalizer_of_disjoint

namespace Work.A7REC

open Subgroup

/-- **The local structure of a group satisfying the `A₇` hypotheses**, as one statement.

All of these are proved in this area from `A7RecCtx G` alone, without character theory:

* `|S| = 8`, `U ⊓ S = ⊥`;
* `|C_G(z)| = 24`, `|C_G(U)| = 36` (so `N_G(U)/C_G(U) ≅ C₂`), `|N_G(U)| = 72`;
* the indices `105`, `70`, `35` — the numbers of conjugates of `z`, of `U` and of `V`;
* `V = O₂(C_G(z))` is a four-group normal in `C_G(z)`, contained in `S`, and `z ∈ V`. -/
def A7LocalFacts : Prop :=
  ∀ (G : Type*) [Group G] [Finite G] (ctx : A7RecCtx G),
    Nat.card ((ctx.S : Subgroup G)) = 8 ∧
    ctx.U ⊓ (ctx.S : Subgroup G) = ⊥ ∧
    Nat.card (Subgroup.centralizer ({ctx.z} : Set G)) = 24 ∧
    Nat.card (Subgroup.centralizer (ctx.U : Set G)) = 36 ∧
    Nat.card (Subgroup.normalizer (ctx.U : Set G)) = 72 ∧
    (Subgroup.centralizer ({ctx.z} : Set G)).index = 105 ∧
    (Subgroup.centralizer (ctx.U : Set G)).index = 70 ∧
    (Subgroup.normalizer (ctx.U : Set G)).index = 35 ∧
    ctx.V ≤ (ctx.S : Subgroup G) ∧
    (ctx.V.subgroupOf (Subgroup.centralizer ({ctx.z} : Set G))).Normal ∧
    Nat.card ctx.V = 4 ∧
    ctx.z ∈ ctx.V ∧
    ⁅ctx.U, ctx.V⁆ = ⊥

/-- `A7LocalFacts` holds. -/
theorem a7LocalFacts : A7LocalFacts := by
  intro G _ _ ctx
  exact ⟨Basic.card_S G ctx, Basic.U_inf_S G ctx, Basic.card_centralizer_z G ctx,
    Basic.card_centralizer_U G ctx, ctx.hNUcard, Basic.index_centralizer_z G ctx,
    Basic.index_centralizer_U G ctx, Basic.index_NU G ctx, Basic.V_le_S G ctx,
    Basic.V_normal_C G ctx, ctx.hV4.1, Basic.z_mem_V G ctx, Basic.commute_U_V G ctx⟩

end Work.A7REC
