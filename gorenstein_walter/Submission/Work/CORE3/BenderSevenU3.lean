import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.FourGroupOrderThreeFixed
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.J4.CardDvdSixOfDisjoint
import Submission.Work.CORE3.J4.J4DTriv
import Submission.Work.CORE3.J4.J4U3
import Submission.Work.CORE3.J4.J4U3ConjK
import Submission.Work.CORE3.J4U3V18Aux.PcoreConjCentralizer
import Submission.Work.CORE3.Case1bCount
import Submission.Work.CORE3.D23.Core23A
import Submission.Work.CORE3.D23.Props

namespace Work.CORE3

/-! Bender 1981, §3, p. 224, step (7), first conclusion `|U| = 3`, in the corrected form of
design pass 23 §A: the hypothesis is Bender's `N_Ĥ(X)` even, i.e. "some involution `s ∈ Ĥ`
inverts `X`" (the `N_G(X)` form of the earlier stubs is automatic, since `y ∈ N_G(X)`, and
carries no information).  The proof is design pass 23's assembly
`Work.CORE3.D23.J4U3V18s`, whose three leaves are `D23.InvolActionUniform`,
`D23.FittingFaithfulFour` and `D23.CardUOfFittingThree`, wrapped as the Props in
`Submission/Work/CORE3/D23/Props.lean`. -/

theorem BenderSevenU3 (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (X : Subgroup G) (hXle : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card ↥X))
    (hinv : Work.GW2.Inverts y X)
    (hCeven : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    {s : G} (hsH : s ∈ B.Hhat) (hs2 : orderOf s = 2) (hsX : Work.GW2.Inverts s X) :
    Nat.card B.U = 3 :=
  Work.CORE3.D23.J4U3V18s Work.CORE3.D23.involActionUniformProp
    Work.CORE3.D23.fittingFaithfulFourProp Work.CORE3.D23.cardUOfFittingThreeProp
    G I h B h1 D hy2 hyH X hXle hXne hXodd hinv hCeven hsH hs2 hsX

end Work.CORE3
