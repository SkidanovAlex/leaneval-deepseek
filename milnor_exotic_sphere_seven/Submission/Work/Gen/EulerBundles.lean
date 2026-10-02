import Mathlib
import Submission.Work.Gen.Euler
import Submission.Work.Gen.EulerDefs
import Submission.Work.Gen.EulerModel
import Submission.Work.Gen.EulerSplit
import Submission.Work.Gen.EulerGaugeCLMDefs
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The two bundles of the Euler sequence, and the gauge between them

`Work.Gen.Src` is the source bundle `TℂP⁴ ⊗ ℂ ⊕ ε²` of the Euler sequence (as `Work.Whitney.whitneySum` of the
complexified tangent bundle `Work.Gen.stdTangentC 4` with the trivial rank-`2` bundle), and
`Work.Gen.Tgt` is the target `Work.Gen.eulerTarget = (ℂ ⊗ O(1))⁵`.  This module defines the
fibrewise linear maps of the gauge

`blockFibre p u : ℂ⁸ × ℂ² → ℂ⁵ × ℂ⁵`  (the `T^{1,0}` and `T^{0,1}` blocks),
`MCLM p b = CbigCLM ∘ blockFibre p (chartFun p b) ∘ sumFibreC⁻¹ : ℂ¹⁰ → ℂ¹⁰`,
`gaugeCLM p t b = Tgt.coordChange t (diagIdx p) b ∘ MCLM p b`,

with their inverses `blockInv`, `MInvCLM`, `gaugeInvCLM`, in the form consumed by
`Work.Thom.nonempty_bundleIso_of_gauge`.
-/

namespace Work.Gen

open Work.Projective

noncomputable section

/-- The source bundle of the Euler sequence: `(TℂP⁴ ⊗ ℂ) ⊕ ε²`. -/
abbrev Src : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 10)) (Fin 5 × Fin 1) :=
  Work.Whitney.whitneySum (stdTangentC 4)
    (trivialVectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 2)) (Fin 1))

/-- The target bundle of the Euler sequence: `(ℂ ⊗ O(1))⁵`. -/
abbrev Tgt : VectorBundleCore ℂ (CP 4) (EuclideanSpace ℂ (Fin 10))
    (lineIdx × lineIdx × lineIdx × lineIdx × lineIdx) := eulerTarget

/-- The index type of the target bundle. -/
abbrev TgtIdx : Type := lineIdx × lineIdx × lineIdx × lineIdx × lineIdx

/-! ## The two `ε²`-coordinates -/

/-- The first coordinate of `ℂ²`. -/
def c0CLM : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (0 : Fin 2)).comp (wlpC 2).toContinuousLinearMap

/-- The second coordinate of `ℂ²`. -/
def c1CLM : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (1 : Fin 2)).comp (wlpC 2).toContinuousLinearMap

/-- The recombination `ℂ × ℂ → ℂ²`. -/
def pair2CLM : ℂ × ℂ →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (wlpC 2).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 2 =>
      if i = 0 then ContinuousLinearMap.fst ℂ ℂ ℂ else ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem c0CLM_pair2 (a b : ℂ) : c0CLM (pair2CLM (a, b)) = a := by
  simp [c0CLM, pair2CLM]

theorem c1CLM_pair2 (a b : ℂ) : c1CLM (pair2CLM (a, b)) = b := by
  simp [c1CLM, pair2CLM]

theorem pair2CLM_c0_c1 (c : EuclideanSpace ℂ (Fin 2)) : pair2CLM (c0CLM c, c1CLM c) = c := by
  apply (wlpC 2).injective
  ext i
  fin_cases i <;> simp [c0CLM, c1CLM, pair2CLM]

/-! ## The block gauge -/

/-- **The block gauge** `ℂ⁸ × ℂ² → ℂ⁵ × ℂ⁵`: the `T^{1,0}` block on the holomorphic coordinates
and the `ε²`-coordinate, and the `T^{0,1}` block on the antiholomorphic coordinates. -/
def blockFibre (p : Fin 5) (u : Fin 4 → ℂ) :
    (EuclideanSpace ℂ (Fin 8) × EuclideanSpace ℂ (Fin 2)) →L[ℂ]
      (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) :=
  ((wlpC 5).symm.toContinuousLinearMap.comp
      ((GblockCLM p u).comp
        ((holPart.comp (ContinuousLinearMap.fst ℂ _ _)).prod
          (c0CLM.comp (ContinuousLinearMap.snd ℂ _ _))))).prod
    ((wlpC 5).symm.toContinuousLinearMap.comp
      ((HblockCLM p u).comp
        ((antiPart.comp (ContinuousLinearMap.fst ℂ _ _)).prod
          (c1CLM.comp (ContinuousLinearMap.snd ℂ _ _)))))

/-- The `A`-component of the inverse block gauge. -/
def blkA (p : Fin 5) (u : Fin 4 → ℂ) :
    (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) →L[ℂ] (Fin 4 → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin 4 → ℂ) ℂ).comp
    ((GblockInv p u).comp ((wlpC 5).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ _ _)))

/-- The `B`-component of the inverse block gauge. -/
def blkB (p : Fin 5) (u : Fin 4 → ℂ) :
    (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) →L[ℂ] (Fin 4 → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin 4 → ℂ) ℂ).comp
    ((HblockInv p u).comp ((wlpC 5).toContinuousLinearMap.comp
      (ContinuousLinearMap.snd ℂ _ _)))

/-- The `C`-component of the inverse block gauge. -/
def blkC (p : Fin 5) (u : Fin 4 → ℂ) :
    (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ (Fin 4 → ℂ) ℂ).comp
    ((GblockInv p u).comp ((wlpC 5).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ _ _)))

/-- The `D`-component of the inverse block gauge. -/
def blkD (p : Fin 5) (u : Fin 4 → ℂ) :
    (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ (Fin 4 → ℂ) ℂ).comp
    ((HblockInv p u).comp ((wlpC 5).toContinuousLinearMap.comp
      (ContinuousLinearMap.snd ℂ _ _)))

/-- **The inverse block gauge**. -/
def blockInv (p : Fin 5) (u : Fin 4 → ℂ) :
    (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) →L[ℂ]
      (EuclideanSpace ℂ (Fin 8) × EuclideanSpace ℂ (Fin 2)) :=
  (XiEquiv.toContinuousLinearMap.comp ((blkA p u).prod (blkB p u))).prod
    (pair2CLM.comp ((blkC p u).prod (blkD p u)))

/-! ## The gauge of the bundle map -/

/-- `CbigCLM ∘ blockFibre p (chartFun p b) ∘ sumFibreC⁻¹`: the block gauge in the standard fibre
`ℂ¹⁰` of the source bundle. -/
def MCLM (p : Fin 5) (b : CP 4) : EuclideanSpace ℂ (Fin 10) →L[ℂ] EuclideanSpace ℂ (Fin 10) :=
  CbigCLM.comp ((blockFibre p (chartFun p b)).comp (Work.Whitney.sumFibreC 8 2).symm.toContinuousLinearMap)

/-- `sumFibreC ∘ blockInv p (chartFun p b) ∘ CbigInv`: its inverse. -/
def MInvCLM (p : Fin 5) (b : CP 4) : EuclideanSpace ℂ (Fin 10) →L[ℂ] EuclideanSpace ℂ (Fin 10) :=
  (Work.Whitney.sumFibreC 8 2).toContinuousLinearMap.comp ((blockInv p (chartFun p b)).comp CbigInv)

/-- The gauge of the bundle map, in the source chart `p` and the target chart `t`. -/
def gaugeCLM (p : Fin 5) (t : TgtIdx) (b : CP 4) :
    EuclideanSpace ℂ (Fin 10) →L[ℂ] EuclideanSpace ℂ (Fin 10) :=
  (Tgt.coordChange (diagIdx p) t b).comp (MCLM p b)

/-- The gauge of the inverse bundle map. -/
def gaugeInvCLM (p : Fin 5) (t : TgtIdx) (b : CP 4) :
    EuclideanSpace ℂ (Fin 10) →L[ℂ] EuclideanSpace ℂ (Fin 10) :=
  (MInvCLM p b).comp (Tgt.coordChange t (diagIdx p) b)

end

end Work.Gen
