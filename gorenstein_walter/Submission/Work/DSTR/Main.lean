/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area DSTR, `Work.DSTR`)

# AREA DSTR — the assembled deliverable

`Work.DSTR.DSTRDeliverable` collects the seven `Prop`s the area delivers (the six design
deliverables plus `LayerOneInvClassProp`), and `Work.DSTR.dstr` produces them from a single
explicit input bundle `Work.DSTR.DSTRInputs` (the `Prop`s of the other areas and the auxiliary
`Prop`s of this area).

A caller who has the `LocalToolkit` of the design can instead use the individual producers
(`Work.DSTR.d16`, `.layer`, `.l19`, `.d110i`, `.d110ii`, `.fstar`, `.layerOneInvClass`).
-/
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.dihOrCycHered
import Submission.Work.DSTR.oddCoreQuot
import Submission.Work.DSTR.twoRank
import Submission.Work.DSTR.quasisimpleSylow
import Submission.Work.DSTR.layerUnique
import Submission.Work.DSTR.quasisimpleCenterOdd
import Submission.Work.DSTR.layerShape
import Submission.Work.DSTR.fittingSelfCentralizing
import Submission.Work.DSTR.dihedralSubgroup
import Submission.Work.DSTR.dihedralQuotient
import Submission.Work.DSTR.dihedralAbelianRank
import Submission.Work.DSTR.l2OddSylowCyclic
import Submission.Work.DSTR.d110iModel
import Submission.Work.DSTR.d110iOdd
import Submission.Work.DSTR.d110iiModel
import Submission.Work.DSTR.innerLift
import Submission.Work.DSTR.layerOneInvClass
import Submission.Work.DSTR.d16
import Submission.Work.DSTR.layer
import Submission.Work.DSTR.l19
import Submission.Work.DSTR.d110i
import Submission.Work.DSTR.d110ii
import Submission.Work.DSTR.fstar
import Submission.Work.L2F.Defs

namespace Work.DSTR

/-- The inputs of area DSTR, exactly as consumed by its leaves: the `Prop`s of the other areas
(`FT`, `FUS`, `COPR`, `L2F`, `A7F`, `AUTL2`, `AUTA7`) together with the auxiliary `Prop`s of this
area.  (The design's `LocalToolkit` supplies all of them except `Work.L2F.L2CentInvariantProp`,
which is the `L2F` extension of `Core2.lean` §G.) -/
structure DSTRInputs : Prop where
  ft : Work.GW2.FeitThompsonProp
  fus : Work.GW2.InvolutionFusionProp
  c11i : Work.GW2.Coprime11iProp
  c11iv : Work.GW2.Coprime11ivProp
  c13 : Work.GW2.Coprime13Prop
  c15 : Work.GW2.Coprime15Prop
  a7 : Work.GW2.A7ModelProp
  l2cent : Work.GW2.L2InvolutionCentralizerProp
  l2ti : Work.GW2.L2TIProp
  l2inv : Work.L2F.L2CentInvariantProp
  autL2 : Work.GW2.AutL2Prop
  autA7 : Work.GW2.AutA7Prop
  dsub : Work.GW2.DihedralSubgroupProp
  dquo : Work.GW2.DihedralQuotientProp
  dDR : Work.GW2.DihedralAbelianRankProp
  l2odd : Work.GW2.L2OddSylowCyclicProp
  e1 : Work.GW2.FittingSelfCentralizingProp

/-- The seven `Prop`s delivered by area DSTR. -/
structure DSTRDeliverable : Prop where
  d16 : Work.GW2.D16Prop
  layer : Work.GW2.LayerProp
  l19 : Work.GW2.L19Prop
  d110i : Work.GW2.D110iProp
  d110ii : Work.GW2.D110iiProp
  fstar : Work.GW2.FStarProp
  layerOneInvClass : Work.GW2.LayerOneInvClassProp

/-- **Area DSTR, assembled**: the six design deliverables plus `LayerOneInvClassProp`, from the
input bundle. -/
theorem dstr (I : DSTRInputs) : DSTRDeliverable := by
  have h1 : Work.GW2.DihOrCycHeredProp := dihOrCycHered I.dsub I.dquo
  have h2 : Work.GW2.OddCoreQuotProp := oddCoreQuot
  have h3 : Work.GW2.TwoRankProp := twoRank I.dDR
  have h4 : Work.GW2.QuasisimpleSylowProp := quasisimpleSylow
  have h6 : Work.GW2.QuasisimpleCenterOddProp :=
    quasisimpleCenterOdd I.ft I.dsub I.fus h4
  have h5 : Work.GW2.LayerUniqueProp := layerUnique h4 h6 I.dDR
  have h7 : Work.GW2.LayerShapeProp := layerShape h2 h5 h6 I.autL2 I.autA7
  have h16 : Work.GW2.D16Prop := d16 h2 h3 h4 h5 h6 h7 I.fus I.e1
  have h9a : Work.GW2.D110iModelProp := d110iModel I.a7 I.dsub h1 h2 I.autL2 I.l2inv
  have h9b : Work.GW2.D110iOddProp := d110iOdd I.c11i I.c11iv I.c13 I.c15
  have h10a : Work.GW2.D110iiModelProp :=
    d110iiModel I.autL2 I.l2cent I.l2ti I.dsub h1
  exact
    { d16 := h16
      layer := layer h2 h5 h6 h7 I.autL2 I.autA7
      l19 := l19 I.l2odd
      d110i := d110i h1 h2 h9a h9b
      d110ii := d110ii h10a h7 h5 h1 I.autA7 h4 h6
      fstar := fstar h16 h5 I.e1
      layerOneInvClass := layerOneInvClass h1 h4 I.fus }

end Work.DSTR
