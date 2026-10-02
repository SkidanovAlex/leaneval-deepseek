import Submission.Work.LineBundles.Main
import Submission.Work.Gen.whitneySumFormulaOneOne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Whitney sum formula in ranks `(1,1)` from this chapter's degree-`1` theorem

`Work.Gen.whitneySumFormulaOneOne` reduces `Work.LerayHirsch.WhitneySumFormula 1 1` — the input that
the LERAYHIRSCH subproject carries — to two inputs: the **degree `1`** case
`c₁(L ⊕ M) = c₁(L) + c₁(M)` (proved in this chapter, `Work.LineBundles.whitneySum_c1`,
unconditionally) and the **degree `2`** case `c₂(L ⊕ M) = c₁(L) ⌣ c₁(M)` (the top-class
multiplicativity, the WHITNEY subproject's `Work.Whitney.TopClassMul`).

This file records that consequence.  (It is kept in its own module because it imports
`Submission.Work.Gen.whitneySumFormulaOneOne`, whose import closure is the GEN/LERAYHIRSCH one.)
-/

namespace Work.LineBundles

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The Whitney sum formula in ranks `(1,1)`** from the degree-`2` (top-class) multiplicativity. -/
theorem whitneySumFormula_one_one_of_topClassMul
    (hCrux : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (L : LineCore B ι₁) (M : LineCore B ι₂),
      Work.Thom.chernClass (1 + 1) 2 (Work.Whitney.whitneySum L M)
        = Work.Whitney.chernProductSum L M 2) :
    Work.LerayHirsch.WhitneySumFormula 1 1 :=
  Work.Gen.whitneySumFormulaOneOne hCrux fun L M => by
    rw [whitneySum_c1 L M, chernProductSum_one_eq_add L M]

end

end Work.LineBundles
