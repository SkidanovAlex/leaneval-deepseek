import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.sumEps
import Submission.Work.Thom.realSumStable

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The two standard-fibre presentations of `Z ⊕ ε¹` agree

`Work.Thom.sumEps ι₀ Z` (ADDENDUM 23) and `Work.Whitney.whitneySum Z ε¹` are two presentations of
the same bundle — the Whitney sum of `Z` with the trivial complex line — in the *same* standard
fibre `EuclideanSpace ℂ (Fin (m+1))` over the same cover `ι × ι₀`.  They differ only in the choice
of the continuous linear equivalence that identifies `ℂ^m × ℂ¹` with `ℂ^{m+1}`: `Work.Thom.prodFinEquiv m`
(a `Classical.choice`) for `sumEps`, and the *explicit* `Work.Whitney.sumFibreC m 1`
(`EuclideanSpace.finAddEquivProd` of Mathlib) for `whitneySum`.

This module proves that they are isomorphic, whose transition functions are conjugate by the
constant gauge `Work.Whitney.sumFibreC m 1 ∘ (Work.Thom.prodFinEquiv m)⁻¹`; the continuity
argument is `Work.Thom.continuousOn_chartExpr_gauge` / `Work.Thom.continuous_totalSpaceMap_clm`
(exactly as for `Work.Thom.nonempty_bundleIso_sumEpsC`).

Consequence (the reason for this module): every stability statement on the `sumEps` side transfers
to the `whitneySum` side, so that the Whitney sum subproject can use
`Work.Thom.chernClass_sumEps` and `Work.Thom.pontryagin1_sumEpsR` directly.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {ι₀ : Type} [Inhabited ι₀]

/-- The constant gauge `ℂ^{m+1} → ℂ^{m+1}` identifying the two presentations of `Z ⊕ ε¹`. -/
noncomputable def sumEps_gauge (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)) :=
  (sumFibreC m 1 : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin (m + 1))).comp
    ((prodFinEquiv m).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))

/-- Its inverse. -/
noncomputable def sumEps_gaugeInv (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)) :=
  (prodFinEquiv m : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin (m + 1))).comp
    ((sumFibreC m 1).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))

theorem sumEps_gauge_comp (m : ℕ) : (sumEps_gauge m).comp (sumEps_gaugeInv m) = 1 := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.comp_apply, sumEps_gauge, sumEps_gaugeInv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem sumEps_gaugeInv_comp (m : ℕ) : (sumEps_gaugeInv m).comp (sumEps_gauge m) = 1 := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.comp_apply, sumEps_gauge, sumEps_gaugeInv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The base sets of the two presentations coincide. -/
theorem sumEps_baseSet_eq_whitneySum_baseSet {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (sumEps ι₀ Z).baseSet
      = (whitneySum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)).baseSet := by
  funext p
  rw [sumEps_baseSet, whitneySum_baseSet, bundleSum_baseSet]

/-- The index maps of the two presentations coincide. -/
theorem sumEps_indexAt_eq_whitneySum_indexAt {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (sumEps ι₀ Z).indexAt
      = (whitneySum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)).indexAt := by
  funext x
  rw [sumEps_indexAt, whitneySum_indexAt, bundleSum_indexAt]

/-- **The transition functions of the two presentations are conjugate by the constant gauge.** -/
theorem sumEps_gauge_conj {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i j : ι × ι₀) (b : B) :
    ((whitneySum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)).coordChange
        i j b).comp (sumEps_gauge m)
      = (sumEps_gauge m).comp ((sumEps ι₀ Z).coordChange i j b) := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, whitneySum_coordChange, sumEps_coordChange,
    bundleSum_trivial_coordChange, sumEps_gauge, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- **The two presentations of `Z ⊕ ε¹` are isomorphic.** -/
theorem nonempty_bundleIso_sumEps_whitneySum {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Nonempty (BundleIso (sumEps ι₀ Z)
      (whitneySum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀))) := by
  have hchart := continuousOn_chartExpr_gauge (sumEps ι₀ Z)
    (whitneySum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀))
    (sumEps_gauge m) (sumEps_gaugeInv m) (sumEps_gauge_comp m) (sumEps_gaugeInv_comp m)
    (sumEps_baseSet_eq_whitneySum_baseSet (ι₀ := ι₀) Z)
    (sumEps_indexAt_eq_whitneySum_indexAt (ι₀ := ι₀) Z)
    (sumEps_gauge_conj (ι₀ := ι₀) Z)
  refine ⟨{ hom := fun _ => (sumEps_gauge m).toLinearMap
            inv := fun _ => (sumEps_gaugeInv m).toLinearMap
            left_inv := fun _ x => ?_
            right_inv := fun _ y => ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · show (sumEps_gaugeInv m) ((sumEps_gauge m) x) = x
    simp only [sumEps_gauge, sumEps_gaugeInv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  · show (sumEps_gauge m) ((sumEps_gaugeInv m) y) = y
    simp only [sumEps_gauge, sumEps_gaugeInv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  · exact continuous_totalSpaceMap_clm (sumEps ι₀ Z)
      (whitneySum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀))
      (ContinuousMap.id B) (fun _ => sumEps_gauge m) (fun i₁ i₂ => hchart.1 i₁ i₂)
  · exact continuous_totalSpaceMap_clm
      (whitneySum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀))
      (sumEps ι₀ Z) (ContinuousMap.id B) (fun _ => sumEps_gaugeInv m)
      (fun i₁ i₂ => hchart.2 i₁ i₂)

end

end Work.Whitney
