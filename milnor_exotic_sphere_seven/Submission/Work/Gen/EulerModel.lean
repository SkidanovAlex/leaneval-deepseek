import Mathlib
import Submission.Work.Gen.EulerDefs
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.BundleIso_comap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The diagonal index and the copy-order shuffle of the Euler target

`Work.Gen.diagIdx i = ((i,i),…,(i,i))` is the diagonal index over the chart `i`, and
`Work.Gen.Cbig` is the constant shuffle putting the standard fibre `ℂ¹⁰` of `eulerTarget` into the
copy order of the five summands of `lineC 4`.
-/

namespace Work.Gen

open Work.Projective Work.Whitney

noncomputable section

/-- The diagonal index of the `(Fin 5 × Fin 5)^5` cover of `eulerTarget` over the chart `i`. -/
def diagIdx (i : Fin 5) : (Fin 5 × Fin 5) × (Fin 5 × Fin 5) × (Fin 5 × Fin 5) ×
    (Fin 5 × Fin 5) × (Fin 5 × Fin 5) :=
  ((i, i), (i, i), (i, i), (i, i), (i, i))

@[simp] theorem eulerTarget_baseSet_diagIdx (i : Fin 5) :
    eulerTarget.baseSet (diagIdx i) = chartSet i := by
  show (Work.Whitney.whitneySum (lineC 4) (Work.Whitney.whitneySum (lineC 4)
    (Work.Whitney.whitneySum (lineC 4) (Work.Whitney.whitneySum (lineC 4) (lineC 4))))).baseSet
    ((i, i), (i, i), (i, i), (i, i), (i, i)) = chartSet i
  simp only [Work.Whitney.whitneySum_baseSet, lineC_baseSet, Set.inter_self]

/-- The nested type `ℂ² × (ℂ² × (ℂ² × (ℂ² × ℂ²)))`. -/
abbrev Nested5 : Type :=
  EuclideanSpace ℂ (Fin 2) ×
    (EuclideanSpace ℂ (Fin 2) ×
      (EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2))))

/-- `EuclideanSpace ℂ (Fin k) ≃L (Fin k → ℂ)`. -/
noncomputable def wlpC (k : ℕ) : EuclideanSpace ℂ (Fin k) ≃L[ℂ] (Fin k → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).toContinuousLinearEquiv

/-- The `k`-th coordinate functional of `ℂ⁵`. -/
noncomputable def coord5 (k : Fin 5) : EuclideanSpace ℂ (Fin 5) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj k).comp (wlpC 5 : EuclideanSpace ℂ (Fin 5) →L[ℂ] (Fin 5 → ℂ))

/-- `ℂ ≃L ℂ¹`. -/
noncomputable def toC1 : ℂ ≃L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  ((LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans
    (WithLp.linearEquiv 2 ℂ (Fin 1 → ℂ)).symm).toContinuousLinearEquiv

/-- The `k`-th pair of two vectors of `ℂ⁵`, as a vector of `ℂ²`. -/
noncomputable def pairK (k : Fin 5) :
    (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (sumFibreC 1 1).toContinuousLinearMap.comp
    (((toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)).comp
        ((coord5 k).comp (ContinuousLinearMap.fst ℂ _ _))).prod
      ((toC1 : ℂ →L[ℂ] EuclideanSpace ℂ (Fin 1)).comp
        ((coord5 k).comp (ContinuousLinearMap.snd ℂ _ _))))

/-- The `k`-th component of `Nested5`. -/
noncomputable def nestK (k : Fin 5) : Nested5 →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  match k with
  | 0 => ContinuousLinearMap.fst ℂ _ _
  | 1 => (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  | 2 => (ContinuousLinearMap.fst ℂ _ _).comp ((ContinuousLinearMap.snd ℂ _ _).comp
          (ContinuousLinearMap.snd ℂ _ _))
  | 3 => (ContinuousLinearMap.fst ℂ _ _).comp (((ContinuousLinearMap.snd ℂ _ _).comp
          (ContinuousLinearMap.snd ℂ _ _)).comp (ContinuousLinearMap.snd ℂ _ _))
  | 4 => (ContinuousLinearMap.snd ℂ _ _).comp (((ContinuousLinearMap.snd ℂ _ _).comp
          (ContinuousLinearMap.snd ℂ _ _)).comp (ContinuousLinearMap.snd ℂ _ _))

/-- The `k`-th "first" coordinate of a nested vector, as an element of `ℂ¹`. -/
noncomputable def zipK (k : Fin 5) : Nested5 →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  ((ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin 1)) (EuclideanSpace ℂ (Fin 1))).comp
    ((sumFibreC 1 1).symm.toContinuousLinearMap.comp (nestK k)))

/-- The `k`-th "second" coordinate of a nested vector, as an element of `ℂ¹`. -/
noncomputable def zipK' (k : Fin 5) : Nested5 →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  ((ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin 1)) (EuclideanSpace ℂ (Fin 1))).comp
    ((sumFibreC 1 1).symm.toContinuousLinearMap.comp (nestK k)))

/-- The "pairing" `ℂ⁵ × ℂ⁵ → Nested5`. -/
noncomputable def pairing :
    (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) →L[ℂ] Nested5 :=
  (pairK 0).prod ((pairK 1).prod ((pairK 2).prod ((pairK 3).prod (pairK 4))))

/-- The nested `sumFibreC` shuffle `Nested5 ≃L ℂ¹⁰`. -/
noncomputable def sumShuffle : Nested5 ≃L[ℂ] EuclideanSpace ℂ (Fin 10) :=
  let e2 := ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 2))
  let Y3 : (EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2))) ≃L[ℂ]
      EuclideanSpace ℂ (Fin 6) :=
    (ContinuousLinearEquiv.prodCongr e2 (sumFibreC 2 2)).trans (sumFibreC 2 4)
  let Y4 : (EuclideanSpace ℂ (Fin 2) ×
        (EuclideanSpace ℂ (Fin 2) × (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)))) ≃L[ℂ]
      EuclideanSpace ℂ (Fin 8) :=
    (ContinuousLinearEquiv.prodCongr e2 Y3).trans (sumFibreC 2 6)
  (ContinuousLinearEquiv.prodCongr e2 Y4).trans (sumFibreC 2 8)

/-- The "unpairing": read a nested vector of `ℂ²`s back into a pair of nested vectors of `ℂ¹`s and
then into `ℂ⁵ × ℂ⁵`. -/
noncomputable def pairingInvL : Nested5 →L[ℂ] (Fin 5 → ℂ) :=
  ContinuousLinearMap.pi (fun k : Fin 5 =>
    (toC1.symm : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ).comp (zipK k))

noncomputable def pairingInvR : Nested5 →L[ℂ] (Fin 5 → ℂ) :=
  ContinuousLinearMap.pi (fun k : Fin 5 =>
    (toC1.symm : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ).comp (zipK' k))

/-- The inverse of `pairing`. -/
noncomputable def pairingInv : Nested5 →L[ℂ] (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) :=
  ((wlpC 5).symm.toContinuousLinearMap.comp pairingInvL).prod
    ((wlpC 5).symm.toContinuousLinearMap.comp pairingInvR)

/-- The copy-order shuffle of `eulerTarget`, as a continuous linear map. -/
noncomputable def CbigCLM :
    (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) →L[ℂ] EuclideanSpace ℂ (Fin 10) :=
  sumShuffle.toContinuousLinearMap.comp pairing

/-- Its inverse. -/
noncomputable def CbigInv :
    EuclideanSpace ℂ (Fin 10) →L[ℂ] (EuclideanSpace ℂ (Fin 5) × EuclideanSpace ℂ (Fin 5)) :=
  pairingInv.comp sumShuffle.symm.toContinuousLinearMap

end

end Work.Gen

namespace Work.Gen

open Work.Projective Work.Whitney

noncomputable section



end

end Work.Gen
