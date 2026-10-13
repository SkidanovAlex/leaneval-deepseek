import Mathlib
import Submission.Work.WilC5.ValProp
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC5.Reduct
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.S4ExpF.logclosure_exp
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC5.StepSeqDecomp
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.LRcReduct
import Submission.Work.WilC5.StepKeyOfValProp

namespace Work.WilC5.ExistsStepSeqAux

/-
This is vdDMM (3.4)+(3.7): if the definable closure of `B ∪ {z}` contains an element `w` whose
value is new over the `dcl`-closed substructure `B`, then some translate `z - a` (`a ∈ B`) already
has a new value.  With the valuation property `ValProp` as an explicit hypothesis this is exactly
`Work.WilC5.StepKeyOfValProp` (the assembly from vdDMM 3.4 and Corollary 3.7), stated here in the
form the `ExistsStepSeq` layer consumes.
-/
theorem TranslateNew
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels) (hVI : WilkiesDesign.CG.ValIneq)
    (hVP : Work.WilC5.ValProp)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    {z : K}
    (hnew : ∃ w : K, w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ {z}) ∧
        ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) w) :
    ∃ a ∈ (B : Set K), ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) (z - a) :=
  Work.WilC5.StepKeyOfValProp hrexp hadd hmul hone hleneg hMCr hOM hVI hVP B hBdcl hnew

end Work.WilC5.ExistsStepSeqAux
