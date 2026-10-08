/-
# `Work.ThreePoints.Main` — assembly of the area's deliverables

* `ChIIFourProp` from `ThmCProp` and the areas' `Prop`s (`chIIFourProp_of_thmC`);
* the second deliverable, `ChIIFourP3SubnormalProp` (`chIIFourP3Subnormal`);
* both together with Theorem C, `ThmCProp ∧ ChIIFourProp ∧ ChIIFourP3SubnormalProp`
  (`threePoints`).

Each `ChIIFourProp` clause is one of

* Prop. 1(b): `stronglyEmbedded_subgroupOf_inf_conj`;
* Prop. 2(a), 2(c): `centD_eq_centralizer_of_involution`;
* Prop. 3 (a),(b) and (c),(d) in the case `X ≠ ⊥`: `sec4_prop3_ab_ne_bot`, `sec4_prop3_cd_ne_bot`;
* Prop. 4: `sec4_prop4_full`.

Audits: `AxiomCheck.lean` / `AxiomCheckExtra.lean` (`#print axioms`, all
`[propext, Classical.choice, Quot.sound]`) and `check_closure.py` (the transitive import closure of
this module mentions neither `hole` nor `hole`).
-/
import Submission.Work.ThreePoints.thmC
import Submission.Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj
import Submission.Work.ThreePoints.centD_eq_centralizer_of_involution
import Submission.Work.ThreePoints.sec4_prop3_ab_ne_bot
import Submission.Work.ThreePoints.sec4_prop3_cd_ne_bot
import Submission.Work.ThreePoints.sec4_prop4_full
import Submission.Work.ThreePoints.chIIFourP3Subnormal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

/-- **`ChIIFourProp` from `ThmCProp` and the areas' `Prop`s** (Peterfalvi I Ch. II §4). -/
theorem chIIFourProp_of_thmC (hFT : FeitThompsonProp) (hC : ThmCProp) (hA : ThmAProp)
    (hZJ : GlaubermanZJProp) (hBrSz : BrauerSuzukiProp) (hMod : ModelFactsProp) :
    ChIIFourProp := by
  intro G _ _ hS H hH t ht htH
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X F hX3 hFX hFN g hg
    exact stronglyEmbedded_subgroupOf_inf_conj hFT hC hA hS hH hX3 hFX hFN hg
  · exact (centD_eq_centralizer_of_involution hFT hC hA hS hH ht htH).1
  · exact (centD_eq_centralizer_of_involution hFT hC hA hS hH ht htH).2
  · intro X hX0 hX hNX
    exact ⟨(sec4_prop3_ab_ne_bot hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX).1,
      (sec4_prop3_ab_ne_bot hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX).2,
      (sec4_prop3_cd_ne_bot hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX).1,
      (sec4_prop3_cd_ne_bot hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX).2⟩
  · exact sec4_prop4_full hFT hC hA hZJ hBrSz hMod hS hH ht htH

/-- The two Ch. II §4 deliverables, from `ThmCProp`. -/
theorem chIIFour_and_p3Subnormal_of_thmC (hFT : FeitThompsonProp) (hC : ThmCProp)
    (hA : ThmAProp) (hZJ : GlaubermanZJProp) (hBrSz : BrauerSuzukiProp)
    (hMod : ModelFactsProp) : ChIIFourProp ∧ ChIIFourP3SubnormalProp :=
  ⟨chIIFourProp_of_thmC hFT hC hA hZJ hBrSz hMod,
    chIIFourP3Subnormal hFT hC hA hZJ hBrSz hMod⟩

/-- **The area's full deliverable**: Theorem C and the two forms of Ch. II §4, from
`FeitThompsonProp` and the areas `ThmAProp`, `GlaubermanZJProp`, `BrauerSuzukiProp`,
`ModelFactsProp`. -/
theorem threePoints (hFT : FeitThompsonProp) (hA : ThmAProp) (hZJ : GlaubermanZJProp)
    (hBrSz : BrauerSuzukiProp) (hMod : ModelFactsProp) :
    ThmCProp ∧ ChIIFourProp ∧ ChIIFourP3SubnormalProp := by
  have hC : ThmCProp := thmC hFT hA hZJ hBrSz hMod
  exact ⟨hC, chIIFourProp_of_thmC hFT hC hA hZJ hBrSz hMod,
    chIIFourP3Subnormal hFT hC hA hZJ hBrSz hMod⟩

end Work.ThreePoints
