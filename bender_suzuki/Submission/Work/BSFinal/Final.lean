import Submission.Blueprint.Assembly
import Submission.Work.BrauerSuzuki.Main
import Submission.Work.GlaubermanZJ.Main
import Submission.Work.ThompsonFrobenius.thompsonFrobenius
import Submission.Work.Higman.Main
import Submission.Work.Hering.Hering
import Submission.Work.FeitSibley.Main
import Submission.Work.RankOneUniqueness.rankOneUniqueness
import Submission.Work.Models.models
import Submission.Work.DoubleTransitivity.Sec7.ThmA
import Submission.Work.Reductions.Main
import Submission.Work.ThreePoints.Main
import Submission.Work.ThreePoints.BenderPrelim
import Submission.Work.NormalComplement.Main
import Submission.Work.ZassenhausTwoGroup.Main
import Submission.Work.ZassenhausPSL2.ZassenhausPSL2OfQCore
import Submission.Work.ZassenhausSuzuki.AssemblySelf
import Submission.Work.ThmF.ChV12.fpfOddPartProp
import Submission.Work.DoubleTransitivity.Export.coprimeDQProp
import Submission.Work.ThmG2.Assembly
import Submission.Work.PSU3.psu3
import Submission.Work.Endgame.Main
import Submission.Work.BSIntegrate.Defs
import Submission.Work.BSIntegrate.thmG3
import Submission.Work.BSIntegrate.degreeProp_prime
import Submission.Work.BSIntegrate.vanishesOffProp
import Submission.Work.BSIntegrate.existsLinearV2Prop
import Submission.Work.ThmF17.OddForm
import Submission.Work.BSLit.ArithmeticNineTwoSeven
import Submission.Work.BSLit.Wielandt.WielandtFixedPoint
import Submission.Work.BSLit.BenderFacts2.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSFinal.Final` — Bender–Suzuki from `FeitThompsonProp` alone

Every area input is produced by its delivered producer:

* Théorème F: `Work.ThmF17.thmF17_appXI_odd_closed` (App. XI produced by AppXIShadow /
  AppXIDickson / AppXIField / Step7Comm; Hall–Wielandt in the corrected odd form, discharged by
  `Work.BSHallW.hallWielandtOdd` through `Work.BSHallW.thmF17'`), with
  `Work.BSLit.WielandtFixedPoint hFT` and `Work.BSLit.ArithmeticNineTwoSeven`;
* Théorème G: `Work.BSIntegrate.thmG3` with its D1 inputs from `BSIntegrate`;
* the Bender-model input: `Work.BSLit.BenderModelFacts2Prop`;
* everything else as in `Work.BSIntegrate.bender_suzuki_of_area_props` (copied below under the
  namespace `Work.BSFinal`, so that this module does not import the old `ThmF16` chain).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.BSFinal

theorem thmAProp_of_ft (hFT : FeitThompsonProp) : ThmAProp :=
  Work.DoubleTransitivity.Sec7.ThmA hFT (Work.GlaubermanZJ.GlaubermanZJ hFT)
    Work.BrauerSuzuki.brauerSuzuki

theorem thompsonFrobenius_of_ft (hFT : FeitThompsonProp) : ThompsonFrobeniusProp :=
  Work.ThompsonFrobenius.thompsonFrobenius hFT (Work.GlaubermanZJ.GlaubermanZJ hFT)

theorem thmCProp_of_ft (hFT : FeitThompsonProp) : ThmCProp := 
  (Work.ThreePoints.threePoints hFT (thmAProp_of_ft hFT) (Work.GlaubermanZJ.GlaubermanZJ hFT)
    Work.BrauerSuzuki.brauerSuzuki Work.Models.models_prop).1

theorem chIIFourProp_of_ft (hFT : FeitThompsonProp) : ChIIFourProp := 
  (Work.ThreePoints.threePoints hFT (thmAProp_of_ft hFT) (Work.GlaubermanZJ.GlaubermanZJ hFT)
    Work.BrauerSuzuki.brauerSuzuki Work.Models.models_prop).2.1

theorem chIIFourP3SubnormalProp_of_ft (hFT : FeitThompsonProp) : ChIIFourP3SubnormalProp :=
  
  (Work.ThreePoints.threePoints hFT (thmAProp_of_ft hFT) (Work.GlaubermanZJ.GlaubermanZJ hFT)
    Work.BrauerSuzuki.brauerSuzuki Work.Models.models_prop).2.2

theorem fpfOddPartProp_of_ft (hFT : FeitThompsonProp) : Work.ThmG.FpfOddPartProp :=
  Work.ThmF.ChV12.fpfOddPartProp hFT (chIIFourProp_of_ft hFT) (thompsonFrobenius_of_ft hFT)

theorem coprimeDQProp_of_ft (hFT : FeitThompsonProp) : Work.ThmG.CoprimeDQProp :=
  Work.DoubleTransitivity.coprimeDQProp (thompsonFrobenius_of_ft hFT) (chIIFourProp_of_ft hFT)
    Work.ThreePoints.kNeOneProp (fpfOddPartProp_of_ft hFT)

theorem thmDProp_of_ft (hFT : FeitThompsonProp) : ThmDProp :=
  Work.NormalComplement.normalComplement hFT (thmAProp_of_ft hFT) (thmCProp_of_ft hFT)
    (chIIFourProp_of_ft hFT) (Work.Hering.Hering hFT Work.Higman.higmanClass)
    (thompsonFrobenius_of_ft hFT) Work.BrauerSuzuki.brauerSuzuki Work.Models.models_prop
    (chIIFourP3SubnormalProp_of_ft hFT) Work.BSLit.BenderModelFacts2Prop

theorem zassenhausTwoGroupProp_of_ft (hFT : FeitThompsonProp) : ZassenhausTwoGroupProp :=
  Work.ZassenhausTwoGroup.ZassenhausTwoGroup_of_areas hFT (thompsonFrobenius_of_ft hFT)
    (Work.FeitSibley.feitSibley hFT)

/-- Théorème F from `FeitThompsonProp` alone (App. XI produced, Hall–Wielandt odd form). -/
theorem thmFProp_of_ft (hFT : FeitThompsonProp) : ThmFProp :=
  Work.ThmF17.thmF17_appXI_odd_closed hFT (chIIFourProp_of_ft hFT) (thompsonFrobenius_of_ft hFT)
    (Work.BSLit.WielandtFixedPoint hFT) Work.BSLit.ArithmeticNineTwoSeven Work.Higman.higmanProp
    Work.BrauerSuzuki.brauerSuzuki

/-- Théorème G from `FeitThompsonProp` alone. -/
theorem thmGProp_of_ft (hFT : FeitThompsonProp) : ThmGProp :=
  Work.BSIntegrate.thmG3 hFT (Work.FeitSibley.feitSibley hFT) (chIIFourProp_of_ft hFT)
    (thompsonFrobenius_of_ft hFT) Work.ThreePoints.kNeOneProp (coprimeDQProp_of_ft hFT)
    (fpfOddPartProp_of_ft hFT)
    (Work.BSIntegrate.existsLinearV2Prop hFT (chIIFourProp_of_ft hFT) (fpfOddPartProp_of_ft hFT))
    Work.ThmG2.indTwoV2Prop
    (Work.BSIntegrate.degreeProp_prime (chIIFourProp_of_ft hFT) (thompsonFrobenius_of_ft hFT)
      (fpfOddPartProp_of_ft hFT) (coprimeDQProp_of_ft hFT))
    (Work.BSIntegrate.vanishesOffProp (chIIFourProp_of_ft hFT) (thompsonFrobenius_of_ft hFT)
      (fpfOddPartProp_of_ft hFT) (coprimeDQProp_of_ft hFT))

end Work.BSFinal

/-- **The Bender–Suzuki theorem, with Feit–Thompson as the only hypothesis.** -/
theorem bender_suzuki_final.{u} (hFT : FeitThompsonProp)
    {X : Type u} [Group X] [Finite X] [IsSimpleGroup X]
    (M : Subgroup X) (h : IsStronglyEmbedded M) : IsSimpleBenderGroup X :=
  open Work.BSFinal in
  bender_suzuki_of_areas hFT Work.BrauerSuzuki.brauerSuzuki (Work.GlaubermanZJ.GlaubermanZJ hFT)
    (thompsonFrobenius_of_ft hFT) Work.Higman.higmanProp
    (Work.Hering.Hering hFT Work.Higman.higmanClass) (Work.FeitSibley.feitSibley hFT)
    Work.RankOneUniqueness.rankOneUniqueness Work.Models.models_prop (thmAProp_of_ft hFT)
    (Work.Reductions.reductions hFT (thmAProp_of_ft hFT)) (thmCProp_of_ft hFT)
    (chIIFourProp_of_ft hFT) (thmDProp_of_ft hFT) (zassenhausTwoGroupProp_of_ft hFT)
    Work.ZassenhausPSL2.zassenhausPSL2 (Work.ZassenhausSuzuki.zassenhausSuzuki_final hFT)
    (thmFProp_of_ft hFT) (thmGProp_of_ft hFT)
    (Work.PSU3.psu3 hFT (chIIFourProp_of_ft hFT) Work.Higman.higmanProp)
    (Work.Endgame.endgame hFT) M h

/-- The challenge statement, verbatim (`Type*`), from `FeitThompsonProp`. -/
theorem bender_suzuki_final' (hFT : FeitThompsonProp) {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] (M : Subgroup X) (h : IsStronglyEmbedded M) : IsSimpleBenderGroup X :=
  bender_suzuki_final hFT M h
