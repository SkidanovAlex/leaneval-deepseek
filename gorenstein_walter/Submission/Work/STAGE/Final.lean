/-
# gw_stage: the Gorenstein–Walter theorem in ONE environment

Built from the auditor's composition `Submission/Work/_audit/PLANMAP_gw_1008b.lean`, with every
`Staged` field replaced by a direct citation of the delivering area's theorem.  All areas now
share the canonical vocabulary `Submission.Work.ASM.Defs` (+ `BSW.Defs`, `DSTR.Defs`).

CORE4's case 2 enters through its delivered `Work.GW2.case2False_deliverable` (`CORE4/Eight28.lean`,
route L28' with `Work.CORE4.L2pLocal` and `Work.CORE4.CopyLocal27` proved).  No `sorry`.
-/
import Submission.Work.ASM.ChallengeStatement
import Submission.Work.ASM.FT
import Submission.Work.RED.Canonical
import Submission.Work.FUS.Deliverable
import Submission.Work.COPR.Deliverable
import Submission.Work.BMAX.Lemma23
import Submission.Work.CORE2A.Assembly
import Submission.Work.CORE2A.lemma22
import Submission.Work.CORE2A.c14_aut
import Submission.Work.CORE3.Assembly
import Submission.Work.DSTR.Main
import Submission.Work.A7REC.OneInvClass
import Submission.Work.BSW.Final
import Submission.Work.L2F.Main
import Submission.Work.L2F.Props.PGL2CommutatorTorus
import Submission.Work.L2F.Props.L2CentInvariant
import Submission.Work.L2F.Props.L2OuterInvolution
import Submission.Work.L2F.Props.L2CentOddCyclic
import Submission.Work.L2F.Props.L2TorusNormalizer
import Submission.Work.L2F.Props.L2PrimeSubgroupCount
import Submission.Work.L2F.Props.L2NormalizesTwoSylowFree
import Submission.Work.A7F.Model
import Submission.Work.AUTL2.Main.bridge
import Submission.Work.AUTA7.Main
import Submission.Work.GLUE.ZjA
import Submission.Work.PSTAB.PStable
import Submission.Work.ZJB2.Final
import Submission.Work.ZASS2.Main
import Submission.Work.CORE2B.Proved
import Submission.Work.BG.Assembly
import Submission.Work.BG.Final
import Submission.Work.CORE4.Eight28
import Submission.Work.CORE4.A7S4Bridge

open scoped MatrixGroups

namespace Work.STAGE
open Work.GW2

/-- The `LayerOneInvClassProp` bridge: DSTR's statement (`C3OneInvClassIn`, `orderOf x = 2`)
implies CORE4's (`OneInvClassIn`, `involutionSet`).  (`AuditGW.layerBridge`.) -/
theorem layerBridge (h : LayerOneInvClassProp) : LayerOneInvClassPropC4 := by
  intro X _ _ hft hd E hn hq x hx y hy
  exact h X hft hd E hn hq x hx.1 y hy.1 hx.2 hy.2

theorem dihOrCycHered : DihOrCycHeredProp :=
  Work.DSTR.dihOrCycHered Work.DSTR.dihedralSubgroup Work.DSTR.dihedralQuotient

/-- DSTR's deliverable. -/
theorem dstrDel : Work.DSTR.DSTRDeliverable :=
  Work.DSTR.dstr
    { ft := feitThompsonProp, fus := Work.FUS.involutionFusionProp,
      c11i := coprime11i, c11iv := coprime11iv, c13 := coprime13, c15 := coprime15,
      a7 := Work.A7F.a7ModelProp, l2cent := Work.L2F.l2InvolutionCentralizer,
      l2ti := Work.L2F.l2TI, l2inv := Work.L2F.Props.L2CentInvariant,
      autL2 := Work.AUTL2.autL2Prop, autA7 := Work.GW2.autA7Prop,
      dsub := Work.DSTR.dihedralSubgroup, dquo := Work.DSTR.dihedralQuotient,
      dDR := Work.DSTR.dihedralAbelianRank, l2odd := Work.DSTR.l2OddSylowCyclic,
      e1 := Work.DSTR.fittingSelfCentralizing }

/-- The `LocalToolkit`. -/
theorem toolkit : LocalToolkit :=
  let D := dstrDel
  { ft := feitThompsonProp, fus := Work.FUS.involutionFusionProp,
    split := Work.FUS.centralizerSplitProp,
    c11i := coprime11i, c11ii := coprime11ii, c11iii := coprime11iii, c11iv := coprime11iv,
    c13 := coprime13, c15 := coprime15,
    d16 := D.d16, lay := D.layer, l19 := D.l19, d110i := D.d110i, d110ii := D.d110ii,
    fstar := D.fstar,
    l2syl := Work.L2F.l2SylowDihedral, l2cent := Work.L2F.l2InvolutionCentralizer,
    l2four := Work.L2F.l2FourGroup, l2ti := Work.L2F.l2TI,
    a7 := Work.A7F.a7ModelProp, autL2 := Work.AUTL2.autL2Prop, autA7 := Work.GW2.autA7Prop }

theorem bsw2 : BSW2Prop := bsw2_unconditional Work.ZASS2.zassOdd2

/-- `Thm26bAutProp` via CORE2A `c14_aut`. -/
theorem thm26bAut : Thm26bAutProp :=
  let h4 := Work.DSTR.quasisimpleSylow
  let h6 := Work.DSTR.quasisimpleCenterOdd feitThompsonProp Work.DSTR.dihedralSubgroup
    Work.FUS.involutionFusionProp h4
  let h5 := Work.DSTR.layerUnique h4 h6 Work.DSTR.dihedralAbelianRank
  Work.CORE2A.c14_aut toolkit
    (Work.CORE2A.lemma21 toolkit Work.BG.bgThmB bsw2)
    (Work.DSTR.layerShape Work.DSTR.oddCoreQuot h5 h6 Work.AUTL2.autL2Prop Work.GW2.autA7Prop)
    (Work.DSTR.twoRank Work.DSTR.dihedralAbelianRank)
    (Work.DSTR.layerOneInvClass dihOrCycHered h4 Work.FUS.involutionFusionProp)
    Work.AUTL2.autL2Prop Work.GW2.autA7Prop

/-- CORE4: case 2 is impossible — CORE4's deliverable `case2False_deliverable` (route L28'). -/
theorem case2 (T : LocalToolkit) (h26 : Thm26Prop) (h27 : Lemma27Prop) (h28 : Lemma28Prop)
    (hA : BGThmAProp) (hL : LayerOneInvClassProp) : Case2FalseProp :=
  Work.GW2.case2False_deliverable
    { toolkit := T, l2centOdd := Work.L2F.Props.L2CentOddCyclic,
      l2primeCount := Work.L2F.Props.L2PrimeSubgroupCount,
      l2torusNorm := Work.L2F.Props.L2TorusNormalizer,
      l2normTwo := Work.L2F.Props.L2NormalizesTwoSylowFree,
      thm26 := h26, lem27 := h27, lem28 := h28, bgA := hA,
      layerOneInvClass := layerBridge hL, a7s4 := Work.GW2.A7S4Prop_holds,
      l2outer := Work.L2F.Props.L2OuterInvolution }

/-- **The Gorenstein–Walter theorem** (challenge statement), in one environment. -/
theorem gorenstein_walter (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k)) := by
  let T := toolkit
  have h22 : Lemma22Prop := Work.CORE2A.lemma22 T Work.BG.bgThmC bsw2
  have h23 : Lemma23Prop := lemma23 T
  have h26 : Thm26Prop :=
    Work.CORE2A.thm26 T Work.BG.bgThmB bsw2 h22 h23 (Work.GW2.zjA Work.GW2.pStable)
      (Work.ZJB2.zjbProp' Work.GW2.pStable dihOrCycHered) thm26bAut
      Work.L2F.Props.PGL2CommutatorTorus
  have h27 : Lemma27Prop := Work.CORE2B.lemma27 T h22 h23 h26
  have h28 : Lemma28Prop := Work.CORE2B.lemma28 T h22 h26 h27
  have h29 : Lemma29Prop := Work.CORE2B.lemma29 T
  have h210 : Thm210Prop := Work.CORE2B.thm210 T h26 h27 h28
  have h1 : Case1FalseProp :=
    Work.CORE3.case1False_of_leaves' T h22 h26 h29 Work.BG.bgThmC
      (Work.A7REC.a7Rec2Prop_of_fusion Work.FUS.involutionFusionProp)
  have h2 : Case2FalseProp := case2 T h26 h27 h28 Work.BG.bgThmA dstrDel.layerOneInvClass
  exact gorenstein_walter_of_props feitThompsonProp (nonSimpleStep_of_RED T) h210 h1 h2
    G hnonab P hdih

end Work.STAGE
