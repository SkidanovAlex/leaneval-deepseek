import Submission.Work.ZJB.Step1.Assembly
import Submission.Work.ZJB2.Step1.zsLeZJProp
import Submission.Work.ZJB2.Step1.cardSylowInProp
import Submission.Work.ZJB2.Step1.sylowOfNormalizerProp
import Submission.Work.ZJB2.Step1.normJLeNormZJProp
import Submission.Work.ZJB2.Step1.cpStarInOfCpInProp
import Submission.Work.ZJB2.Step1.existsMaxBadProp
import Submission.Work.ZJB2.Step1.existsAProp
import Submission.Work.ZJB2.Step1.existsT1Prop
import Submission.Work.ZJB2.Step1.dMemProp
import Submission.Work.ZJB2.Step1.existsMaxHProp
import Submission.Work.ZJB2.Step1.stepNProp
import Submission.Work.ZJB2.Step1.zjtMemProp
import Submission.Work.ZJB2.Step1.finalProp

/-!
# ZJB2, step (I) of Glauberman's Theorem 5.1: the assembly

`Work.ZJB.step1_of_leaves` (`Submission/Work/ZJB/Step1/Assembly.lean`, proved in the lead's
design pass 11) reduces Theorem 5.1's step (I) to thirteen `…Prop` leaves.  This file feeds it
the corresponding proved theorems of `Submission/Work/ZJB2/Step1/`.

The auxiliary leaves F1 (`thompsonJEqOfLeProp`), I.1 (`dltProp`) and I.2 (`claimAProp`) are not
arguments of the assembly: they are used *inside* the proofs of I.3 (`existsAProp`), I.4
(`existsT1Prop`) and I.8 (`finalProp`).
-/

namespace Work.ZJB2.Step1

/-- **Theorem 5.1, step (I)** (Glauberman 1968, pp. 1117–1119, hypothesis (a)):
`Z(S)^g ⊆ S ⟹ Z(S)^g ⊆ Z(J(S))`. -/
theorem step1Prop {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.Step1Prop p G :=
  Work.ZJB.step1_of_leaves (zsLeZJProp (G := G)) (cardSylowInProp (G := G) (p := p))
    (sylowOfNormalizerProp (G := G) (p := p)) (normJLeNormZJProp (G := G))
    (cpStarInOfCpInProp (G := G) (p := p)) (existsMaxBadProp (G := G) (p := p))
    (existsAProp (G := G) (p := p)) (existsT1Prop (G := G) (p := p))
    (dMemProp (G := G) (p := p)) (existsMaxHProp (G := G) (p := p))
    (stepNProp (G := G) (p := p)) (zjtMemProp (G := G) (p := p))
    (finalProp (G := G) (p := p))

end Work.ZJB2.Step1
