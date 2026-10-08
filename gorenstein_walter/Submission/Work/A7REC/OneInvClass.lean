/-
Area `A7REC`: **the bridge from area `FUS` to the one-class input `hone`**.

Every C-leaf of this area (and `a7Rec2Prop_of_leaves`) takes as input

```
hone : ∀ (G) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
         A7RecHyps G S z U V → OneInvClass G
```

i.e. "in a group satisfying the `A₇` hypotheses, all involutions are conjugate".  This is exactly
the first conjunct of area `FUS`'s `InvolutionFusionProp` (Gorenstein 7.7.3 / Bender 1.6), applied
with the Sylow `2`-subgroup of order `8`: the extra hypothesis `∀ N ⊴ G, N.index ≠ 2` is available
because `G` is simple of order `2520` (a normal subgroup of index `2` is `⊥` or `⊤`, whose indices
are `2520` and `1`).

`Work.A7REC.oneInvClass_of_fusion` is that bridge, and `Work.A7REC.a7Rec2Prop_of_fusion` is the
area's deliverable with `hone` supplied by `Work.FUS.involutionFusionProp`.
-/
import Mathlib
import Submission.Work.A7REC.Excl
import Submission.Work.A7REC.Char.Char6
import Submission.Work.FUS.Deliverable

namespace Work.A7REC

/-- **The one-class input from area `FUS`.**  If all involutions of a group with a dihedral Sylow
`2`-subgroup and no normal subgroup of index `2` are conjugate (`InvolutionFusionProp`), then the
same holds in every group satisfying the `A₇` hypotheses. -/
theorem oneInvClass_of_fusion (h : Work.GW2.InvolutionFusionProp) :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
      A7RecHyps G S z U V → OneInvClass G := by
  intro G _ _ S z U V hyps
  haveI : IsSimpleGroup G := hyps.1
  have hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN h2
    rcases hN.eq_bot_or_eq_top with hbot | htop
    · rw [hbot, Subgroup.index_bot] at h2
      rw [hyps.2.1] at h2
      norm_num at h2
    · rw [htop, Subgroup.index_top] at h2
      norm_num at h2
  exact (h G S 4 (by norm_num) hyps.2.2.1 hno).1

/-- **The deliverable of the area, with `hone` supplied by area `FUS`.** -/
theorem a7Rec2Prop_of_fusion (h : Work.GW2.InvolutionFusionProp) : A7Rec2Prop :=
  a7Rec2Prop_of_leaves (oneInvClass_of_fusion h)

end Work.A7REC
