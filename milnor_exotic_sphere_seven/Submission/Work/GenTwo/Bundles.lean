import Mathlib
import Submission.Work.GenTwo.Split
import Submission.Work.GenTwo.Model
import Submission.Work.GenTwo.CbigDiag
import Submission.Work.Gen.EulerBundles
import Submission.Work.GenTwo.TangentCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The two bundles of the complexified Euler sequence of `ℂP²`, and the block gauge

`Work.Gen.E2.Src` is the source `(TℂP² ⊗ ℂ) ⊕ ε²` of the Euler sequence (the Whitney sum of the
complexified tangent bundle `Work.Gen.stdTangentC 2` with the trivial rank-`2` bundle) and
`Work.Gen.E2.Tgt` is the target `(ℂ ⊗ O(1))³`.  This module defines the fibrewise linear maps of
the gauge

`blockFibre p u : ℂ⁴ × ℂ² → ℂ³ × ℂ³`  (the `T^{1,0}` and `T^{0,1}` blocks),
`MCLM p b = CbigCLM ∘ blockFibre p (chartFun p b) ∘ sumFibreC⁻¹ : ℂ⁶ → ℂ⁶`,
`gaugeCLM p t b = Tgt.coordChange t (diagIdx p) b ∘ MCLM p b`,

with their inverses `blockInv`, `MInvCLM`, `gaugeInvCLM`.
-/

namespace Work.Gen.E2

open Work.Projective

noncomputable section

/-! ## The source bundle -/

/-- The source bundle of the Euler sequence: `(TℂP² ⊗ ℂ) ⊕ ε²`. -/
abbrev Src : VectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin (2 * 2 + 2))) (Fin 3 × Fin 1) :=
  Work.Whitney.whitneySum (stdTangentC 2)
    (trivialVectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 1))

theorem stdTangentC_baseSet_two (p : Fin 3) : (stdTangentC 2).baseSet p = chartSet p :=
  stdTangentRealN_baseSet 2 p

theorem Src_baseSet (p : Fin 3) (β : Fin 1) : Src.baseSet (p, β) = chartSet p := by
  show (Work.Whitney.whitneySum (stdTangentC 2)
    (trivialVectorBundleCore ℂ (CP 2) (EuclideanSpace ℂ (Fin 2)) (Fin 1))).baseSet (p, β)
      = chartSet p
  rw [Work.Whitney.whitneySum_baseSet, stdTangentC_baseSet_two]
  exact Set.inter_univ _

/-! ## The block gauge -/

/-- **The block gauge** `ℂ⁴ × ℂ² → ℂ³ × ℂ³`: the `T^{1,0}` block on the holomorphic coordinates
and the `ε²`-coordinate, and the `T^{0,1}` block on the antiholomorphic coordinates. -/
def blockFibre (p : Fin 3) (u : Fin 2 → ℂ) :
    (EuclideanSpace ℂ (Fin (2 * 2)) × EuclideanSpace ℂ (Fin 2)) →L[ℂ]
      (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) :=
  ((wlpC 3).symm.toContinuousLinearMap.comp
      ((GblockCLM p u).comp
        ((holPart.comp (ContinuousLinearMap.fst ℂ _ _)).prod
          (Work.Gen.c0CLM.comp (ContinuousLinearMap.snd ℂ _ _))))).prod
    ((wlpC 3).symm.toContinuousLinearMap.comp
      ((HblockCLM p u).comp
        ((antiPart.comp (ContinuousLinearMap.fst ℂ _ _)).prod
          (Work.Gen.c1CLM.comp (ContinuousLinearMap.snd ℂ _ _)))))

/-- The `A`-component of the inverse block gauge. -/
def blkA (p : Fin 3) (u : Fin 2 → ℂ) :
    (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ] (Fin 2 → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) ℂ).comp
    ((GblockInv p u).comp ((wlpC 3).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ _ _)))

/-- The `B`-component of the inverse block gauge. -/
def blkB (p : Fin 3) (u : Fin 2 → ℂ) :
    (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ] (Fin 2 → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) ℂ).comp
    ((HblockInv p u).comp ((wlpC 3).toContinuousLinearMap.comp
      (ContinuousLinearMap.snd ℂ _ _)))

/-- The `C`-component of the inverse block gauge. -/
def blkC (p : Fin 3) (u : Fin 2 → ℂ) :
    (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ℂ).comp
    ((GblockInv p u).comp ((wlpC 3).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ _ _)))

/-- The `D`-component of the inverse block gauge. -/
def blkD (p : Fin 3) (u : Fin 2 → ℂ) :
    (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ℂ).comp
    ((HblockInv p u).comp ((wlpC 3).toContinuousLinearMap.comp
      (ContinuousLinearMap.snd ℂ _ _)))

/-- **The inverse block gauge**. -/
def blockInv (p : Fin 3) (u : Fin 2 → ℂ) :
    (EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)) →L[ℂ]
      (EuclideanSpace ℂ (Fin (2 * 2)) × EuclideanSpace ℂ (Fin 2)) :=
  (XiEquiv.toContinuousLinearMap.comp ((blkA p u).prod (blkB p u))).prod
    (Work.Gen.pair2CLM.comp ((blkC p u).prod (blkD p u)))

/-! ## The gauge of the bundle map -/

/-- `CbigCLM ∘ blockFibre p (chartFun p b) ∘ sumFibreC⁻¹`: the block gauge in the standard fibre
`ℂ⁶` of the source bundle. -/
def MCLM (p : Fin 3) (b : CP 2) :
    EuclideanSpace ℂ (Fin (2 * 2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * 2 + 2)) :=
  CbigCLM.comp ((blockFibre p (chartFun p b)).comp
    (Work.Whitney.sumFibreC (2 * 2) 2).symm.toContinuousLinearMap)

/-- `sumFibreC ∘ blockInv p (chartFun p b) ∘ CbigInv`: its inverse. -/
def MInvCLM (p : Fin 3) (b : CP 2) :
    EuclideanSpace ℂ (Fin (2 * 2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * 2 + 2)) :=
  (Work.Whitney.sumFibreC (2 * 2) 2).toContinuousLinearMap.comp
    ((blockInv p (chartFun p b)).comp CbigInv)

/-- The gauge of the bundle map, in the source chart `p` and the target chart `t`. -/
def gaugeCLM (p : Fin 3) (t : TgtIdx) (b : CP 2) :
    EuclideanSpace ℂ (Fin (2 * 2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * 2 + 2)) :=
  (Tgt.coordChange (diagIdx p) t b).comp (MCLM p b)

/-- The gauge of the inverse bundle map. -/
def gaugeInvCLM (p : Fin 3) (t : TgtIdx) (b : CP 2) :
    EuclideanSpace ℂ (Fin (2 * 2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * 2 + 2)) :=
  (MInvCLM p b).comp (Tgt.coordChange t (diagIdx p) b)

end

end Work.Gen.E2
