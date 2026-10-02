import Mathlib
import Submission.Work.Thom.tautQuotientComap
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

/-!
# Splitting off a nowhere-zero section: the definitions and the linear algebra

This module contains the definitions and the *linear algebra* of the proof that a complex
gluing-data bundle `V` of rank `m+1` with a continuous nowhere-zero section `σ` over a paracompact
Hausdorff base is isomorphic to `σ^*(Q_V) ⊕ ε¹` (`Q_V` the tautological quotient of `V` over the
complement of the zero section).  The continuity arguments and the assembly of the `BundleIso`
live in `Submission/Work/Whitney/nonempty_bundleIso_of_nowhereZeroSection_of_paracompact.lean`.
-/

open Work.TangentClasses Work.Thom

namespace Work.Whitney
namespace NZ

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- The vector of the section `σ` at `b`, as an element of the model fibre. -/
noncomputable def secVec (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V)))) (b : B) :
    EuclideanSpace ℂ (Fin (m+1)) :=
  (show EuclideanSpace ℂ (Fin (m+1)) from
    ((σ b : ↥(zeroComplement (realification V))) : (realification V).TotalSpace).2)

/-- The non-vanishing coordinate of the tautological section, at `σ b`. -/
noncomputable def secIdx (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V)))) (b : B) : Fin (m+1) :=
  tqCoord V (σ b)

/-- The pullback of the tautological quotient along `σ`. -/
noncomputable def Q (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V)))) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) (ι × Fin (m+1)) :=
  bundleComap (tautQuotient V) σ

/-- The right-hand side of the splitting: `σ^*(Q_V) ⊕ ε¹`, in the standard fibre. -/
noncomputable def W {ι₀ : Type} [Inhabited ι₀]
    (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V)))) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ((ι × Fin (m+1)) × ι₀) :=
  whitneySum (Q V σ) (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)

/-- The hypothesis that `σ` is a section of the projection. -/
abbrev IsSection {V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    (σ : C(B, ↥(zeroComplement (realification V)))) : Prop :=
  ∀ b, ((σ b : ↥(zeroComplement (realification V))) : (realification V).TotalSpace).1 = b

section Basic

variable {V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
variable {σ : C(B, ↥(zeroComplement (realification V)))}

/-- The chart coordinate of the section point, read in any chart. -/
theorem localTriv_secVec (hσ : IsSection σ) (i : ι) (b : B) :
    (V.localTriv i ((σ b : ↥(zeroComplement (realification V))) :
      (realification V).TotalSpace)).2
      = V.coordChange (V.indexAt b) i b (secVec V σ b) := by
  have key : ∀ (q : (realification V).TotalSpace),
      (V.localTriv i q).2 = V.coordChange (V.indexAt q.1) i q.1 q.2 := by
    intro q
    rw [VectorBundleCore.localTriv_apply]
  rw [key, hσ b]
  rfl

/-- In the preferred chart, the section point reads as `secVec`. -/
theorem zCoord_secVec (hσ : IsSection σ) (b : B) :
    zCoord (Z := V) (V.indexAt b) (σ b) = secVec V σ b := by
  rw [zCoord, localTriv_secVec hσ, V.coordChange_self _ _ (V.mem_baseSet_at b)]

/-- The chosen coordinate of the section vector is non-zero. -/
theorem secVec_secIdx_ne_zero (hσ : IsSection σ) (b : B) :
    secVec V σ b (secIdx V σ b) ≠ 0 := by
  have h := tqCoord_spec V (σ b)
  rw [show ((σ b : ↥(zeroComplement (realification V))) :
      (realification V).TotalSpace).proj = b from hσ b] at h
  have hz : zCoord (Z := V) (V.indexAt b) (σ b) = secVec V σ b := by
    rw [zCoord]
    have key : ∀ (q : (realification V).TotalSpace),
        (V.localTriv (V.indexAt b) q).2
          = V.coordChange (V.indexAt q.1) (V.indexAt b) q.1 q.2 := by
      intro q; rw [VectorBundleCore.localTriv_apply]
    rw [key, hσ b, V.coordChange_self _ _ (V.mem_baseSet_at b)]; rfl
  rw [zCoord] at hz
  simp only [secIdx]
  simp only [← hz]
  exact h

/-- The index of the pullback of the tautological quotient at `b`. -/
theorem Q_indexAt (hσ : IsSection σ) (b : B) :
    (Q V σ).indexAt b = (V.indexAt b, secIdx V σ b) := by
  rw [Q, bundleComap_indexAt, tautQuotient_indexAt_eq, hσ b]
  rfl

/-- The transition function of the pullback of the tautological quotient, explicitly. -/
theorem Q_coordChange_apply (hσ : IsSection σ) (a : ι × Fin (m+1)) (b : B)
    (z : EuclideanSpace ℂ (Fin m)) :
    (Q V σ).coordChange a ((Q V σ).indexAt b) b z
      = quoFun (secIdx V σ b) (secVec V σ b)
          (V.coordChange a.1 (V.indexAt b) b (fillFun a.2 z)) := by
  rw [Q, bundleComap_coordChange, bundleComap_indexAt, tautQuotient_indexAt_eq]
  rw [show ((σ b : ↥(zeroComplement (realification V))) :
      (realification V).TotalSpace).proj = b from hσ b]
  rw [tautQuotient_coordChange]
  rw [show ((σ b : ↥(zeroComplement (realification V))) :
      (realification V).TotalSpace).proj = b from hσ b]
  rw [localTriv_secVec hσ (V.indexAt b) b, V.coordChange_self _ _ (V.mem_baseSet_at b)]
  rfl

end Basic

/-! ## The splitting of the standard fibre -/

/-- The first component of the splitting `ℂ^{m+1} ≅ ℂ^m × ℂ¹`. -/
noncomputable def fstC (m : ℕ) : EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1))).comp
    ((sumFibreC m 1).symm : EuclideanSpace ℂ (Fin (m+1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))

/-- The second component of the splitting `ℂ^{m+1} ≅ ℂ^m × ℂ¹`. -/
noncomputable def sndC (m : ℕ) : EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  (ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1))).comp
    ((sumFibreC m 1).symm : EuclideanSpace ℂ (Fin (m+1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))

/-- The scalar second component of the splitting `ℂ^{m+1} ≅ ℂ^m × ℂ¹`. -/
noncomputable def scalarC (m : ℕ) : EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ :=
  (evalCLM (0 : Fin 1)).comp (sndC m)

theorem fstC_sumFibreC (m : ℕ) (z : EuclideanSpace ℂ (Fin m)) (t : EuclideanSpace ℂ (Fin 1)) :
    fstC m (sumFibreC m 1 (z, t)) = z := by
  simp only [fstC, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [ContinuousLinearEquiv.symm_apply_apply]; rfl

theorem sndC_sumFibreC (m : ℕ) (z : EuclideanSpace ℂ (Fin m)) (t : EuclideanSpace ℂ (Fin 1)) :
    sndC m (sumFibreC m 1 (z, t)) = t := by
  simp only [sndC, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [ContinuousLinearEquiv.symm_apply_apply]; rfl

theorem scalarC_sumFibreC (m : ℕ) (z : EuclideanSpace ℂ (Fin m)) (t : EuclideanSpace ℂ (Fin 1)) :
    scalarC m (sumFibreC m 1 (z, t)) = evalCLM (0 : Fin 1) t := by
  rw [scalarC, ContinuousLinearMap.comp_apply, sndC_sumFibreC]

theorem sumFibreC_fstC_sndC (m : ℕ) (u : EuclideanSpace ℂ (Fin (m+1))) :
    sumFibreC m 1 (fstC m u, sndC m u) = u := by
  have h : (fstC m u, sndC m u) = (sumFibreC m 1).symm u := rfl
  rw [h]
  exact ContinuousLinearEquiv.apply_symm_apply _ u

theorem scalarC_smul_basisVec (m : ℕ) (u : EuclideanSpace ℂ (Fin (m+1))) :
    (scalarC m u) • basisVec (0 : Fin 1) = sndC m u := by
  ext i
  rw [show i = (0 : Fin 1) from Subsingleton.elim i 0]
  simp [basisVec_apply, scalarC, evalCLM_apply, smul_eq_mul]

/-! ## The fibrewise maps of the splitting -/

/-- The quotient projection at `b`, in the preferred chart of the tautological quotient. -/
noncomputable def qCLM (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V)))) (b : B) :
    EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  quoCLM (secIdx V σ b) (secVec V σ b)

/-- The forward fibrewise map `V_b → (σ^*(Q_V) ⊕ ε¹)_b`, given a splitting functional `ℓ`. -/
noncomputable def homCLM (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V))))
    (ℓ : B → (EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ)) (b : B) :
    EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] EuclideanSpace ℂ (Fin (m+1)) :=
  ((sumFibreC m 1 : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin (m+1)))).comp
    ((qCLM V σ b).prod ((ℓ b).smulRight (basisVec (0 : Fin 1))))

/-- The backward fibrewise map, given a splitting functional `ℓ`. -/
noncomputable def invCLM (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V))))
    (ℓ : B → (EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ)) (b : B) :
    EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] EuclideanSpace ℂ (Fin (m+1)) :=
  (fillCLM (secIdx V σ b)).comp (fstC m)
    - (((ℓ b).comp (fillCLM (secIdx V σ b))).comp (fstC m)).smulRight (secVec V σ b)
    + ((scalarC m).smulRight (secVec V σ b))

section Maps

variable {V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
variable {σ : C(B, ↥(zeroComplement (realification V)))}
variable (ℓ : B → (EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ))

theorem homCLM_apply (b : B) (w : EuclideanSpace ℂ (Fin (m+1))) :
    homCLM V σ ℓ b w = sumFibreC m 1 (quoFun (secIdx V σ b) (secVec V σ b) w,
      (ℓ b w) • basisVec (0 : Fin 1)) := by
  simp only [homCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    qCLM, quoCLM_apply, ContinuousLinearMap.smulRight_apply]
  rfl

theorem fstC_homCLM (b : B) (w : EuclideanSpace ℂ (Fin (m+1))) :
    fstC m (homCLM V σ ℓ b w) = quoFun (secIdx V σ b) (secVec V σ b) w := by
  rw [homCLM_apply, fstC_sumFibreC]

theorem scalarC_homCLM (b : B) (w : EuclideanSpace ℂ (Fin (m+1))) :
    scalarC m (homCLM V σ ℓ b w) = ℓ b w := by
  rw [homCLM_apply, scalarC_sumFibreC]
  simp [evalCLM_apply, basisVec_apply]

theorem invCLM_apply (b : B) (u : EuclideanSpace ℂ (Fin (m+1))) :
    invCLM V σ ℓ b u = fillFun (secIdx V σ b) (fstC m u)
      - (ℓ b (fillFun (secIdx V σ b) (fstC m u))) • secVec V σ b
      + (scalarC m u) • secVec V σ b := by
  simp only [invCLM, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, fillCLM_apply]

theorem quoFun_invCLM (hσ : IsSection σ) (b : B) (u : EuclideanSpace ℂ (Fin (m+1))) :
    quoFun (secIdx V σ b) (secVec V σ b) (invCLM V σ ℓ b u) = fstC m u := by
  change quoCLM (secIdx V σ b) (secVec V σ b) (invCLM V σ ℓ b u) = fstC m u
  rw [invCLM_apply, map_add, map_sub, map_smul, map_smul]
  simp only [quoCLM_apply, quoFun_fillFun _ _ _ (secVec_secIdx_ne_zero hσ b),
    quoFun_self _ _ (secVec_secIdx_ne_zero hσ b), smul_zero, sub_zero, add_zero]

theorem ell_invCLM (hℓ : ∀ b, ℓ b (secVec V σ b) = 1) (b : B)
    (u : EuclideanSpace ℂ (Fin (m+1))) :
    ℓ b (invCLM V σ ℓ b u) = scalarC m u := by
  rw [invCLM_apply, map_add, map_sub, map_smul, map_smul, hℓ b]
  simp

theorem invCLM_homCLM_apply (hσ : IsSection σ) (hℓ : ∀ b, ℓ b (secVec V σ b) = 1)
    (b : B) (w : EuclideanSpace ℂ (Fin (m+1))) :
    invCLM V σ ℓ b (homCLM V σ ℓ b w) = w := by
  rw [invCLM_apply, fstC_homCLM, scalarC_homCLM]
  have hv : secVec V σ b (secIdx V σ b) ≠ 0 := secVec_secIdx_ne_zero hσ b
  rw [fillFun_quoFun (secIdx V σ b) (secVec V σ b) w hv]
  rw [map_sub, map_smul, hℓ b]
  module

theorem homCLM_invCLM_apply (hσ : IsSection σ) (hℓ : ∀ b, ℓ b (secVec V σ b) = 1)
    (b : B) (u : EuclideanSpace ℂ (Fin (m+1))) :
    homCLM V σ ℓ b (invCLM V σ ℓ b u) = u := by
  rw [homCLM_apply, quoFun_invCLM ℓ hσ b u, ell_invCLM ℓ hℓ b u,
    scalarC_smul_basisVec, sumFibreC_fstC_sndC]

theorem invCLM_comp_homCLM (hσ : IsSection σ) (hℓ : ∀ b, ℓ b (secVec V σ b) = 1) (b : B) :
    (invCLM V σ ℓ b).comp (homCLM V σ ℓ b)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (m+1))) := by
  refine ContinuousLinearMap.ext fun w => ?_
  simpa using invCLM_homCLM_apply ℓ hσ hℓ b w

theorem homCLM_comp_invCLM (hσ : IsSection σ) (hℓ : ∀ b, ℓ b (secVec V σ b) = 1) (b : B) :
    (homCLM V σ ℓ b).comp (invCLM V σ ℓ b)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (m+1))) := by
  refine ContinuousLinearMap.ext fun u => ?_
  simpa using homCLM_invCLM_apply ℓ hσ hℓ b u

end Maps

end NZ
end Work.Whitney
