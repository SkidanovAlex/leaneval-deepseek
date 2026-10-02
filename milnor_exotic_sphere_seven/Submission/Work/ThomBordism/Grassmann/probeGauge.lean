import Mathlib
import Submission.Work.ThomBordism.Grassmann.probePlane
import Submission.Work.ThomBordism.Grassmann.zStdSetup
import Submission.Work.Gen.EulerToolkit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses Work.Projective

noncomputable section

variable {k m : ℕ}

/-! ## The chart evaluation as a continuous linear map -/

theorem coordEval_smul (S : ChartIdx k m) (f : Stiefel k m) (r : ℝ) (a : Amb k) :
    coordEval S f (r • a) = r • coordEval S f a := by
  simp only [coordEval, WithLp.ofLp_smul, Pi.smul_apply]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => (smul_smul r (a.ofLp i) (coordVec S f i)).symm)

theorem evalChart_linear (S : ChartIdx k m) (x : ↥(baseSet S)) :
    ∃ L : Amb k →L[ℝ] Amb (k + m), ∀ v, L v = evalChart S (x, v) := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = (x : OG k m) := Quotient.exists_rep _
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ x.2)
  refine ⟨LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    { toFun := fun v => coordEval S f v
      map_add' := fun a b => coordEval_add S f a b
      map_smul' := fun r a => coordEval_smul S f r a }, ?_⟩
  intro v
  show coordEval S f v = evalChart S (x, v)
  exact (evalChart_spec S x f hfc hf.symm v).symm

noncomputable def evalChartCLM (S : ChartIdx k m) (x : ↥(baseSet S)) : Amb k →L[ℝ] Amb (k + m) :=
  Classical.choose (evalChart_linear S x)

theorem evalChartCLM_apply (S : ChartIdx k m) (x : ↥(baseSet S)) (v : Amb k) :
    evalChartCLM S x v = evalChart S (x, v) :=
  Classical.choose_spec (evalChart_linear S x) v

/-- The vector of the plane with oriented chart coordinates `v`, as a linear map. -/
noncomputable def ambCLM (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m) (P : OG k m)
    (hP : P ∈ baseSet S) : Amb k →L[ℝ] Amb (k + m) :=
  (evalChartCLM S ⟨P, hP⟩).comp (matLin (orientMat S P))

theorem ambCLM_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m) (P : OG k m)
    (hP : P ∈ baseSet S) (v : Amb k) :
    ambCLM k m hk hm S P hP v = evalChartO S ⟨P, hP⟩ v := by
  rw [ambCLM, ContinuousLinearMap.comp_apply, evalChartCLM_apply]
  rfl

/-! ## Continuity of the normalised spanning vector -/

theorem continuousOn_uVec (i : Fin 3) :
    ContinuousOn (fun x : CP 2 => Work.Gen.uVec i x) (Work.Projective.chartSet i) := by
  refine continuousOn_pi.mpr (fun j => ?_)
  by_cases hj : j = i
  · rw [hj]
    have h1 : (fun x : CP 2 => Work.Gen.uVec i x i) = fun _ => (1 : ℂ) := by
      funext x; exact Work.Gen.uVec_apply_self i x
    rw [h1]; exact continuousOn_const
  · have h1 : (fun x : CP 2 => Work.Gen.uVec i x j)
        = fun x => Work.Projective.chartFun i x (Work.Projective.removeAbove i j hj) := by
      funext x
      rw [Work.Gen.uVec_apply, Work.Gen.homCoord_of_ne hj]
    rw [h1]
    exact (continuous_apply _).comp_continuousOn (Work.Projective.continuousOn_chartFun i)

/-! ## The target-side bookkeeping -/

theorem real_smul_eq_ofReal_smul {M : Type*} [AddCommMonoid M] [Module ℝ M] [Module ℂ M]
    [IsScalarTower ℝ ℂ M] (r : ℝ) (z : M) : r • z = ((r : ℂ)) • z := by
  simpa using (IsScalarTower.smul_assoc r (1 : ℂ) z).symm

/-- The identification `ℂ ≅ ℂ¹` as a real continuous linear map. -/
noncomputable def mkFCLM : ℂ →L[ℝ] EuclideanSpace ℂ (Fin 1) :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (EuclideanSpace.single (𝕜 := ℂ) (0 : Fin 1) 1)

theorem mkFCLM_apply (a : ℂ) : mkFCLM a = Work.Gen.mkF a := by
  rw [mkFCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
  apply (EuclideanSpace.equiv (Fin 1) ℂ).injective
  ext j
  fin_cases j
  simp [Work.Gen.mkF]

/-- The coordinate of `ℂ¹` as a real continuous linear map. -/
noncomputable def scFCLM : EuclideanSpace ℂ (Fin 1) →L[ℝ] ℂ :=
  (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).restrictScalars ℝ

theorem scFCLM_apply (c : EuclideanSpace ℂ (Fin 1)) : scFCLM c = Work.Gen.scF c := by
  rw [scFCLM]
  show EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) c = Work.Gen.scF c
  simp [Work.Gen.scF, EuclideanSpace.proj]

/-- The `E3`-component of an ambient vector. -/
noncomputable def probeProjE3 (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) : Amb (k + m) →L[ℝ] E3 :=
  (cxE.symm : Amb 6 →L[ℝ] E3).comp (probeCy k m hk hm)

/-- The coefficient functional `ξ ↦ ⟪u_i, ξ⟫`. -/
noncomputable def probeCoeffCLM (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2) :
    Amb (k + m) →L[ℝ] ℂ :=
  ((innerSL ℂ (cxOf (Work.Gen.uVec i x))).restrictScalars ℝ).comp (probeProjE3 k m hk hm)

theorem probeCoeffCLM_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (w : Amb (k + m)) :
    probeCoeffCLM k m hk hm i x w
      = inner ℂ (cxOf (Work.Gen.uVec i x)) (cxE.symm (probeCy k m hk hm w)) := by
  show (innerSL ℂ (cxOf (Work.Gen.uVec i x))) ((cxE.symm : Amb 6 →L[ℝ] E3)
    (probeCy k m hk hm w)) = _
  rfl

/-- The `ℝ²`-coordinate of the dual line coordinate `⟨ξ, u_i⟩ = conj ⟪u_i, ξ⟫`. -/
noncomputable def probeCpart (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2) :
    Amb (k + m) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
      (mkFCLM.comp (Complex.conjCLE : ℂ →L[ℝ] ℂ))).comp (probeCoeffCLM k m hk hm i x)

theorem probeCpart_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (w : Amb (k + m)) :
    probeCpart k m hk hm i x w
      = equivC1R2 (Work.Gen.mkF (starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec i x))
          (cxE.symm (probeCy k m hk hm w))))) := by
  show equivC1R2 (mkFCLM (Complex.conjCLE (probeCoeffCLM k m hk hm i x w))) = _
  rw [mkFCLM_apply, Complex.conjCLE_apply, starRingEnd_apply, probeCoeffCLM_apply]
  rfl

/-- The `ℂ`-coordinate read off an element of `ℝ²`. -/
noncomputable def probeBCLM : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ :=
  scFCLM.comp (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))

theorem probeBCLM_apply (a : EuclideanSpace ℝ (Fin 2)) :
    probeBCLM a = Work.Gen.scF (equivC1R2.symm a) := by
  show scFCLM ((equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ]
    EuclideanSpace ℂ (Fin 1)) a) = _
  rw [scFCLM_apply]
  rfl

/-- The line element `ξ ∈ E3` reconstructed from the `ℝ²`-coordinate. -/
noncomputable def probeXiCLM (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] E3 :=
  (((ContinuousLinearMap.mul ℝ ℂ
      ((inner ℂ (cxOf (Work.Gen.uVec i x)) (cxOf (Work.Gen.uVec i x)))⁻¹)).comp
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (probeBCLM))).smulRight
    (cxOf (Work.Gen.uVec i x)))

theorem probeXiCLM_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (a : EuclideanSpace ℝ (Fin 2)) :
    probeXiCLM k m hk hm i x a
      = (((inner ℂ (cxOf (Work.Gen.uVec i x)) (cxOf (Work.Gen.uVec i x)))⁻¹)
          * starRingEnd ℂ (Work.Gen.scF (equivC1R2.symm a))) • cxOf (Work.Gen.uVec i x) := by
  show (ContinuousLinearMap.mul ℝ ℂ
      ((inner ℂ (cxOf (Work.Gen.uVec i x)) (cxOf (Work.Gen.uVec i x)))⁻¹)
        (Complex.conjCLE (probeBCLM a))) • cxOf (Work.Gen.uVec i x) = _
  rw [Complex.conjCLE_apply, probeBCLM_apply, starRingEnd_apply]
  rfl

/-- The vector of the probe plane reconstructed from the target coordinates. -/
noncomputable def probeReconCLM (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2) :
    EuclideanSpace ℝ (Fin (2 + (k - 2))) →L[ℝ] Amb (k + m) :=
  (((probeEmb k m hk hm).comp ((cxE : E3 →L[ℝ] Amb 6).comp (probeXiCLM k m hk hm i x))).coprod
      (probeTailComb k m hk)).comp
    ((Work.Whitney.sumFibreR 2 (k - 2)).symm : EuclideanSpace ℝ (Fin (2 + (k - 2))) →L[ℝ]
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin (k - 2))))

theorem probeReconCLM_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (y : EuclideanSpace ℝ (Fin (2 + (k - 2)))) :
    probeReconCLM k m hk hm i x y
      = probeEmb k m hk hm (cxE (probeXiCLM k m hk hm i x
          ((Work.Whitney.sumFibreR 2 (k - 2)).symm y).1))
        + probeTailComb k m hk ((Work.Whitney.sumFibreR 2 (k - 2)).symm y).2 := by
  show ((probeEmb k m hk hm).comp ((cxE : E3 →L[ℝ] Amb 6).comp
      (probeXiCLM k m hk hm i x))).coprod (probeTailComb k m hk)
      ((Work.Whitney.sumFibreR 2 (k - 2)).symm y) = _
  rw [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- The `S`-coordinates of an ambient vector of the plane, as a linear map. -/
noncomputable def toECoordAtCLM (S : ChartIdx k m) (P : OG k m) : Amb (k + m) →L[ℝ] Amb k :=
  (matLin (orientMat S P)).comp
    ((LinearMap.toContinuousLinearMap
        ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm : (Fin k → ℝ) →ₗ[ℝ] Amb k)).comp
      ((LinearMap.toContinuousLinearMap (coordProj S)).comp
        (LinearMap.toContinuousLinearMap
          ((WithLp.linearEquiv 2 ℝ (Fin (k + m) → ℝ)) :
            Amb (k + m) →ₗ[ℝ] (Fin (k + m) → ℝ)))))

theorem toECoordAtCLM_apply (S : ChartIdx k m) (P : OG k m) (w : Amb (k + m)) :
    toECoordAtCLM S P w = toECoordAt S P w := by
  rw [toECoordAtCLM]
  show (matLin (orientMat S P)) (((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm)
    ((coordProj S) ((WithLp.linearEquiv 2 ℝ (Fin (k + m) → ℝ)) w))) = _
  rfl

/-! ## The gauge and its inverse -/

/-- The gauge on the chart, for a point of the chart. -/
noncomputable def probePhiRaw (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2) (hx : probeSigma k m hk hm x ∈ baseSet S) :
    Amb k →L[ℝ] EuclideanSpace ℝ (Fin (2 + (k - 2))) :=
  ((Work.Whitney.sumFibreR 2 (k - 2) :
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin (k - 2))) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 + (k - 2)))).comp
    (((probeCpart k m hk hm t.1 x).prod (probeUx k m hk)).comp
      (ambCLM k m hk hm S (probeSigma k m hk hm x) hx)))

theorem probePhiRaw_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2) (hx : probeSigma k m hk hm x ∈ baseSet S) (v : Amb k) :
    probePhiRaw k m hk hm S t x hx v
      = Work.Whitney.sumFibreR 2 (k - 2)
          (probeCpart k m hk hm t.1 x (evalChartO S ⟨probeSigma k m hk hm x, hx⟩ v),
            probeUx k m hk (evalChartO S ⟨probeSigma k m hk hm x, hx⟩ v)) := by
  rw [probePhiRaw, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ambCLM_apply]
  rfl

/-- **The gauge of the probe**. -/
noncomputable def probePhi (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2) :
    Amb k →L[ℝ] EuclideanSpace ℝ (Fin (2 + (k - 2))) := by
  classical
  exact dite (probeSigma k m hk hm x ∈ baseSet S) (fun hx => probePhiRaw k m hk hm S t x hx)
    (fun _ => 0)

theorem probePhi_apply_of_mem (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2) (hx : probeSigma k m hk hm x ∈ baseSet S) (v : Amb k) :
    probePhi k m hk hm S t x v
      = Work.Whitney.sumFibreR 2 (k - 2)
          (probeCpart k m hk hm t.1 x (evalChartO S ⟨probeSigma k m hk hm x, hx⟩ v),
            probeUx k m hk (evalChartO S ⟨probeSigma k m hk hm x, hx⟩ v)) := by
  rw [probePhi, dif_pos hx, probePhiRaw_apply]

/-- The inverse gauge on the chart, for a point of the chart. -/
noncomputable def probePhiInvRaw (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2) (hx : probeSigma k m hk hm x ∈ baseSet S) :
    EuclideanSpace ℝ (Fin (2 + (k - 2))) →L[ℝ] Amb k :=
  (toECoordAtCLM S (probeSigma k m hk hm x)).comp (probeReconCLM k m hk hm t.1 x)

theorem probePhiInvRaw_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2) (hx : probeSigma k m hk hm x ∈ baseSet S)
    (y : EuclideanSpace ℝ (Fin (2 + (k - 2)))) :
    probePhiInvRaw k m hk hm S t x hx y
      = toECoordAt S (probeSigma k m hk hm x) (probeReconCLM k m hk hm t.1 x y) := by
  rw [probePhiInvRaw, ContinuousLinearMap.comp_apply, toECoordAtCLM_apply]

/-- **The inverse gauge of the probe**. -/
noncomputable def probePhiInv (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2) :
    EuclideanSpace ℝ (Fin (2 + (k - 2))) →L[ℝ] Amb k := by
  classical
  exact dite (probeSigma k m hk hm x ∈ baseSet S)
    (fun hx => probePhiInvRaw k m hk hm S t x hx) (fun _ => 0)

theorem probePhiInv_apply_of_mem (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2) (hx : probeSigma k m hk hm x ∈ baseSet S)
    (y : EuclideanSpace ℝ (Fin (2 + (k - 2)))) :
    probePhiInv k m hk hm S t x y
      = toECoordAt S (probeSigma k m hk hm x) (probeReconCLM k m hk hm t.1 x y) := by
  rw [probePhiInv, dif_pos hx, probePhiInvRaw_apply]


/-! ## The bundles and their base sets -/

/-- The tautological bundle pulled back along the probe. -/
noncomputable abbrev Zb (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) :
    Work.TangentClasses.RealBundle (CP 2) (Amb k) (ChartIdx k m) :=
  Work.Thom.bundleComap (tautologicalBundle k m) (probeSigma k m hk hm)

/-- The target bundle `zStd ⊕ ε^{k-2}`. -/
noncomputable abbrev Zt (k m : ℕ) :
    Work.TangentClasses.RealBundle (CP 2) (EuclideanSpace ℝ (Fin (2 + (k - 2))))
      (Fin 3 × Fin 1) :=
  Work.Whitney.whitneySumR zStd
    (Work.TangentClasses.RealBundle.trivial (CP 2) (EuclideanSpace ℝ (Fin (k - 2))) (Fin 1))

theorem Zb_baseSet (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m) :
    (Zb k m hk hm).baseSet S = {x | probeSigma k m hk hm x ∈ baseSet S} := rfl

theorem Zt_baseSet (k m : ℕ) (t : Fin 3 × Fin 1) :
    (Zt k m).baseSet t = Work.Projective.chartSet t.1 := by
  rw [Zt, Work.Whitney.whitneySumR_baseSet, Work.TangentClasses.RealBundle.trivial_baseSet,
    Set.inter_univ, zStd, RealBundle.mapFibre_baseSet, Work.Thom.realification_baseSet,
    Work.Gen.tautDual_baseSet]

theorem memPlane_evalChartO (S : ChartIdx k m) (P : OG k m) (hP : P ∈ baseSet S) (v : Amb k) :
    memPlane P (evalChartO S ⟨P, hP⟩ v) := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = P := Quotient.exists_rep _
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ hP)
  refine ⟨f, hf, ?_⟩
  rw [evalChartO, evalChart_spec S ⟨P, hP⟩ f hfc hf.symm]
  refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
  exact coordVec_mem_span S f i



theorem cxOf_eq_norm_smul_cxUnit {v : Fin 3 → ℂ} (hv : v ≠ 0) :
    cxOf v = ((‖cxOf v‖ : ℝ)) • cxUnit v := by
  rw [cxUnit, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (cxOf_ne_zero hv)), one_smul]

/-- **A complex multiple of the line vector of the probe point, plus a complement vector, lies in
the span of the probe frame.** -/
theorem probeEmb_cxOf_add_mem_span (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (c : ℂ) (τ : EuclideanSpace ℝ (Fin (k - 2))) :
    probeEmb k m hk hm (cxE (c • cxOf (Work.Gen.uVec i x))) + probeTailComb k m hk τ
      ∈ Submodule.span ℝ (Set.range (probeFrameRep k m hk hm (Work.Gen.uVec i x))) := by
  have hv : Work.Gen.uVec i x ≠ 0 := Work.Gen.uVec_ne_zero i x
  have hmem0 : probePairVec k m hk hm (Work.Gen.uVec i x) 0
      ∈ Submodule.span ℝ (Set.range (probeFrameRep k m hk hm (Work.Gen.uVec i x))) :=
    Submodule.subset_span ⟨probeSplit k hk (Sum.inl 0),
      by simp only [probeFrameRep_inl, probePairVec_zero]⟩
  have hmem1 : probePairVec k m hk hm (Work.Gen.uVec i x) 1
      ∈ Submodule.span ℝ (Set.range (probeFrameRep k m hk hm (Work.Gen.uVec i x))) :=
    Submodule.subset_span ⟨probeSplit k hk (Sum.inl 1),
      by simp only [probeFrameRep_inl, probePairVec_one]⟩
  have htail : probeTailComb k m hk τ
      ∈ Submodule.span ℝ (Set.range (probeFrameRep k m hk hm (Work.Gen.uVec i x))) := by
    rw [probeTailComb_apply]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨probeSplit k hk (Sum.inr l),
        by simp only [probeFrameRep_inr]⟩))
  have hscale : c • cxOf (Work.Gen.uVec i x)
      = (c * ((‖cxOf (Work.Gen.uVec i x)‖ : ℝ) : ℂ)) • cxUnit (Work.Gen.uVec i x) := by
    conv_lhs => rw [cxOf_eq_norm_smul_cxUnit hv]
    rw [real_smul_eq_ofReal_smul, smul_smul]
  rw [hscale, cxE_complex_smul, probeEmb_add_smul, ← probePairVec_zero, ← probePairVec_neg_one]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ hmem0)
      (Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem1))) htail

/-- The reconstructed plane vector lies in the plane of the probe point. -/
theorem memPlane_probeRecon (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (hx : x ∈ Work.Projective.chartSet i) (y : EuclideanSpace ℝ (Fin (2 + (k - 2)))) :
    memPlane (probeSigma k m hk hm x) (probeReconCLM k m hk hm i x y) := by
  refine ⟨probeStiefelRep k m hk hm (Work.Gen.uVec i x) (Work.Gen.uVec_ne_zero i x), ?_, ?_⟩
  · exact (probeSigma_apply_uVec k m hk hm i x hx).symm
  · rw [probeReconCLM_apply, probeXiCLM_apply]
    exact probeEmb_cxOf_add_mem_span k m hk hm i x _ _


/-! ## The six cocycle conditions and the two inverse conditions -/

theorem probePhi_hsrc (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (S' : ChartIdx k m) (x : CP 2)
    (h1 : x ∈ (Zb k m hk hm).baseSet S) (h2 : x ∈ (Zb k m hk hm).baseSet S')
    (h3 : x ∈ (Zt k m).baseSet t) :
    (probePhi k m hk hm S t x).comp ((Zb k m hk hm).coordChange S' S x)
      = probePhi k m hk hm S' t x := by
  rw [Zb_baseSet] at h1 h2
  have hxS : probeSigma k m hk hm x ∈ baseSet S := h1
  have hxS' : probeSigma k m hk hm x ∈ baseSet S' := h2
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.comp_apply, probePhi_apply_of_mem k m hk hm S t x hxS,
    probePhi_apply_of_mem k m hk hm S' t x hxS']
  have hglue := evalChartO_glue S' S (probeSigma k m hk hm x) ⟨hxS', hxS⟩ v
  rw [hglue]
  rfl

theorem probePhi_htgt (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t t' : Fin 3 × Fin 1) (x : CP 2)
    (h1 : x ∈ (Zb k m hk hm).baseSet S) (h2 : x ∈ (Zt k m).baseSet t)
    (h3 : x ∈ (Zt k m).baseSet t') :
    ((Zt k m).coordChange t t' x).comp (probePhi k m hk hm S t x)
      = probePhi k m hk hm S t' x := by
  have hxS : probeSigma k m hk hm x ∈ baseSet S := h1
  have hch : x ∈ Work.Projective.chartSet t.1 := by
    rw [Zt_baseSet k m t] at h2; exact h2
  have hch' : x ∈ Work.Projective.chartSet t'.1 := by
    rw [Zt_baseSet k m t'] at h3; exact h3
  -- the two normalisations of the line differ by the transition scalar
  have hkey : ∀ ξ : E3,
      starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec t'.1 x)) ξ)
        = Work.Gen.homCoord 2 t'.1 t.1 x
          * starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec t.1 x)) ξ) := by
    intro ξ
    have hrel : Work.Gen.uVec t'.1 x
        = Work.Gen.homCoord 2 t'.1 t.1 x • Work.Gen.uVec t.1 x := by
      rw [Work.Gen.uVec_indep t.1 t'.1 ⟨hch, hch'⟩, Work.Gen.homCoord_inv hch hch']
    have hcx : cxOf (Work.Gen.uVec t'.1 x)
        = Work.Gen.homCoord 2 t'.1 t.1 x • cxOf (Work.Gen.uVec t.1 x) := by
      rw [hrel, cxOf_smul]
    rw [hcx, inner_smul_left]
    simp only [starRingEnd_apply, star_mul, star_star]
    ring
  -- the `zStd` transition, on values
  have hzstd : ∀ a : EuclideanSpace ℝ (Fin 2),
      zStd.coordChange t.1 t'.1 x a
        = equivC1R2 ((Work.Gen.homCoord 2 t'.1 t.1 x)
            • (equivC1R2.symm a : EuclideanSpace ℂ (Fin 1))) := by
    intro a
    rw [zStd, RealBundle.mapFibre_coordChange]
    show equivC1R2 ((Work.Thom.realification (Work.Gen.tautDual 2)).coordChange t.1 t'.1 x
      (equivC1R2.symm a)) = _
    rw [show (Work.Thom.realification (Work.Gen.tautDual 2)).coordChange t.1 t'.1 x
        (equivC1R2.symm a)
        = (Work.Gen.tautDual 2).coordChange t.1 t'.1 x (equivC1R2.symm a) from
      congrFun (Work.Thom.realification_coordChange (Work.Gen.tautDual 2) t.1 t'.1 x) _]
    rw [Work.Gen.tautDual_coordChange]
    rfl
  -- the target transition, on values
  have hZt : ∀ p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin (k - 2)),
      (Zt k m).coordChange t t' x (Work.Whitney.sumFibreR 2 (k - 2) p)
        = Work.Whitney.sumFibreR 2 (k - 2)
            (zStd.coordChange t.1 t'.1 x p.1, p.2) := by
    intro p
    rw [Zt, Work.Whitney.whitneySumR_coordChange,
      Work.TangentClasses.RealBundle.trivial_coordChange]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.comp_apply, probePhi_apply_of_mem k m hk hm S t x hxS v,
    probePhi_apply_of_mem k m hk hm S t' x hxS v, hZt]
  congr 1
  rw [hzstd, probeCpart_apply, ContinuousLinearEquiv.symm_apply_apply, probeCpart_apply]
  refine Prod.ext ?_ rfl
  rw [← Work.Gen.mkF_mul]
  exact congrArg (fun z => equivC1R2 (Work.Gen.mkF z)) (hkey _).symm

/-! ## The transition of the dual line coordinate

The value of any transition function, in the coordinates of the fibre. -/

/-- The value of the `zStd`-transition: the coordinate in the chart `i` is multiplied by the
homogeneous ratio `homCoord 2 i' i`. -/
theorem zStd_coordChange_apply (i i' : Fin 3) (x : CP 2) (a : EuclideanSpace ℝ (Fin 2)) :
    zStd.coordChange i' i x a
      = equivC1R2 ((Work.Gen.homCoord 2 i i' x) •
          (equivC1R2.symm a : EuclideanSpace ℂ (Fin 1))) := by
  rw [zStd, RealBundle.mapFibre_coordChange]
  show equivC1R2 ((Work.Thom.realification (Work.Gen.tautDual 2)).coordChange i' i x
    (equivC1R2.symm a)) = _
  rw [show (Work.Thom.realification (Work.Gen.tautDual 2)).coordChange i' i x
      (equivC1R2.symm a)
      = (Work.Gen.tautDual 2).coordChange i' i x (equivC1R2.symm a) from
    congrFun (Work.Thom.realification_coordChange (Work.Gen.tautDual 2) i' i x) _]
  rw [Work.Gen.tautDual_coordChange]
  rfl

/-- The value of the target transition `Zt.coordChange t t'`, in coordinates: the first component
transforms by the `zStd`-transition, the second (the trivial summand) is unchanged. -/
theorem Zt_coordChange_apply (k m : ℕ) (t t' : Fin 3 × Fin 1) (x : CP 2)
    (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin (k - 2))) :
    (Zt k m).coordChange t t' x (Work.Whitney.sumFibreR 2 (k - 2) p)
      = Work.Whitney.sumFibreR 2 (k - 2)
          (zStd.coordChange t.1 t'.1 x p.1, p.2) := by
  rw [Zt, Work.Whitney.whitneySumR_coordChange,
    Work.TangentClasses.RealBundle.trivial_coordChange]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- **The line element reconstructed from a line coordinate**, for an arbitrary spanning vector
`u` of the line: the multiple of `u` whose `u`-coordinate is
`scF (equivC1R2.symm a)`. -/
noncomputable def probeXiOf (u : E3) (a : EuclideanSpace ℝ (Fin 2)) : E3 :=
  ((inner ℂ u u)⁻¹ * starRingEnd ℂ (Work.Gen.scF (equivC1R2.symm a))) • u

theorem probeXiCLM_eq_probeXiOf (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (a : EuclideanSpace ℝ (Fin 2)) :
    probeXiCLM k m hk hm i x a = probeXiOf (cxOf (Work.Gen.uVec i x)) a := by
  rw [probeXiCLM_apply, probeXiOf]

/-- **Rescaling the spanning vector.**  Rescaling the spanning vector `u` by `c ≠ 0` and the line
coordinate by the same `c` leaves the reconstructed element unchanged. -/
theorem probeXiOf_scale (u : E3) (hu : u ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (a a' : EuclideanSpace ℝ (Fin 2))
    (hb : Work.Gen.scF (equivC1R2.symm a') = c * Work.Gen.scF (equivC1R2.symm a)) :
    probeXiOf (c • u) a' = probeXiOf u a := by
  have hA : inner ℂ u u ≠ 0 := inner_self_ne_zero.mpr hu
  have hX : star c ≠ 0 := star_ne_zero.mpr hc
  rw [probeXiOf, probeXiOf, hb]
  simp only [starRingEnd_apply, inner_smul_left, inner_smul_right, star_mul, star_star]
  have hscalar : ((c * (star c * inner ℂ u u))⁻¹
      * (star (Work.Gen.scF (equivC1R2.symm a)) * star c)) * c
      = (inner ℂ u u)⁻¹ * star (Work.Gen.scF (equivC1R2.symm a)) := by
    field_simp
  rw [smul_smul, hscalar]

/-- **The dual line coordinate is compatible with the transition functions**: reconstructing the
line element from the coordinate in the chart `i'` (as transferred to the chart `i` by the
transition function) gives the same vector as reconstructing it directly in the chart `i'`. -/
theorem probeXiCLM_coordChange (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i i' : Fin 3) (x : CP 2)
    (hi : x ∈ Work.Projective.chartSet i) (hi' : x ∈ Work.Projective.chartSet i')
    (a : EuclideanSpace ℝ (Fin 2)) :
    probeXiCLM k m hk hm i x (zStd.coordChange i' i x a)
      = probeXiCLM k m hk hm i' x a := by
  have hv : Work.Gen.uVec i' x ≠ 0 := Work.Gen.uVec_ne_zero i' x
  have hne : Work.Gen.homCoord 2 i i' x ≠ 0 := Work.Gen.homCoord_ne_zero_of_mem hi hi'
  have hvec : Work.Gen.uVec i x = Work.Gen.homCoord 2 i i' x • Work.Gen.uVec i' x := by
    rw [Work.Gen.uVec_indep i' i ⟨hi', hi⟩, Work.Gen.homCoord_inv hi' hi]
  have hb : Work.Gen.scF (equivC1R2.symm (zStd.coordChange i' i x a))
      = Work.Gen.homCoord 2 i i' x * Work.Gen.scF (equivC1R2.symm a) := by
    rw [zStd_coordChange_apply, ContinuousLinearEquiv.symm_apply_apply, Work.Gen.scF_smul]
  rw [probeXiCLM_eq_probeXiOf, hvec, cxOf_smul]
  exact probeXiOf_scale _ (cxOf_ne_zero hv) _ hne _ _ hb

/-- **Injectivity of the chart coordinate on the plane**: two plane vectors with the same `S`-reading
are equal. -/
theorem toECoordAt_inj_of_mem (k m : ℕ) (S : ChartIdx k m) (P : OG k m) (hPS : P ∈ baseSet S)
    {w w' : Amb (k + m)} (hw : memPlane P w) (hw' : memPlane P w')
    (h : toECoordAt S P w = toECoordAt S P w') : w = w' := by
  rw [← evalChartO_toECoordAt S P hPS w hw, h, evalChartO_toECoordAt S P hPS w' hw']

/-- **The chart-to-chart transition function on the plane coordinate**: the transition function of
the tautological bundle takes the `S`-coordinate of a vector of the plane to its `S'`-coordinate. -/
theorem coordChange_toECoordAt' (k m : ℕ) (S S' : ChartIdx k m) (P : OG k m)
    (hPS : P ∈ baseSet S) (hPS' : P ∈ baseSet S') (w : Amb (k + m)) (hw : memPlane P w) :
    (tautologicalBundle k m).coordChange S S' P (toECoordAt S P w) = toECoordAt S' P w := by
  refine peEvalChartO_injective S' ⟨P, hPS'⟩ ?_
  show evalChartO S' ⟨P, hPS'⟩ (coordChangeO S S' P (toECoordAt S P w))
    = evalChartO S' ⟨P, hPS'⟩ (toECoordAt S' P w)
  rw [← evalChartO_glue S S' P ⟨hPS, hPS'⟩ (toECoordAt S P w),
    evalChartO_toECoordAt S P hPS w hw, evalChartO_toECoordAt S' P hPS' w hw]

theorem probePhi_htgtinv (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t t' : Fin 3 × Fin 1) (x : CP 2)
    (h1 : x ∈ (Zb k m hk hm).baseSet S) (h2 : x ∈ (Zt k m).baseSet t)
    (h3 : x ∈ (Zt k m).baseSet t') :
    (probePhiInv k m hk hm S t x).comp ((Zt k m).coordChange t' t x)
      = probePhiInv k m hk hm S t' x := by
  have hxS : probeSigma k m hk hm x ∈ baseSet S := h1
  have hxt : x ∈ Work.Projective.chartSet t.1 := by
    rw [Zt_baseSet k m t] at h2; exact h2
  have hxt' : x ∈ Work.Projective.chartSet t'.1 := by
    rw [Zt_baseSet k m t'] at h3; exact h3
  refine ContinuousLinearMap.ext (fun y => ?_)
  rw [ContinuousLinearMap.comp_apply, probePhiInv_apply_of_mem k m hk hm S t x hxS,
    probePhiInv_apply_of_mem k m hk hm S t' x hxS]
  -- replace the source argument by its coordinates in the chart `t`
  have hZt : (Zt k m).coordChange t' t x y
      = Work.Whitney.sumFibreR 2 (k - 2)
          (zStd.coordChange t'.1 t.1 x
            ((Work.Whitney.sumFibreR 2 (k - 2)).symm y).1,
           ((Work.Whitney.sumFibreR 2 (k - 2)).symm y).2) := by
    have h := Zt_coordChange_apply k m t' t x ((Work.Whitney.sumFibreR 2 (k - 2)).symm y)
    rwa [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [hZt, probeReconCLM_apply, ContinuousLinearEquiv.symm_apply_apply, probeReconCLM_apply]
  dsimp only
  rw [probeXiCLM_coordChange k m hk hm t.1 t'.1 x hxt hxt']

theorem probePhi_hsrcinv (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (S' : ChartIdx k m) (x : CP 2)
    (h1 : x ∈ (Zb k m hk hm).baseSet S) (h2 : x ∈ (Zb k m hk hm).baseSet S')
    (h3 : x ∈ (Zt k m).baseSet t) :
    ((Zb k m hk hm).coordChange S S' x).comp (probePhiInv k m hk hm S t x)
      = probePhiInv k m hk hm S' t x := by
  have hxS : probeSigma k m hk hm x ∈ baseSet S := h1
  have hxS' : probeSigma k m hk hm x ∈ baseSet S' := h2
  have hxt : x ∈ Work.Projective.chartSet t.1 := by
    rw [Zt_baseSet k m t] at h3; exact h3
  refine ContinuousLinearMap.ext (fun y => ?_)
  rw [ContinuousLinearMap.comp_apply, probePhiInv_apply_of_mem k m hk hm S t x hxS,
    probePhiInv_apply_of_mem k m hk hm S' t x hxS']
  have hcc : ((Zb k m hk hm).coordChange S S' x)
      = (tautologicalBundle k m).coordChange S S' (probeSigma k m hk hm x) :=
    Work.Thom.bundleComap_coordChange (tautologicalBundle k m) (probeSigma k m hk hm) S S' x
  rw [hcc]
  exact coordChange_toECoordAt' k m S S' (probeSigma k m hk hm x) hxS hxS'
    (probeReconCLM k m hk hm t.1 x y) (memPlane_probeRecon k m hk hm t.1 x hxt y)

theorem probePhi_hleft (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2)
    (v : Amb k) (hb : x ∈ (Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) :
    probePhiInv k m hk hm S t x (probePhi k m hk hm S t x v) = v := by
  have hxS : probeSigma k m hk hm x ∈ baseSet S := hb.1
  have hxt : x ∈ Work.Projective.chartSet t.1 := by
    rw [Zt_baseSet k m t] at hb; exact hb.2
  rw [probePhi_apply_of_mem k m hk hm S t x hxS v,
    probePhiInv_apply_of_mem k m hk hm S t x hxS]
  set w := evalChartO S ⟨probeSigma k m hk hm x, hxS⟩ v with hw
  have hmem : memPlane (probeSigma k m hk hm x) w := memPlane_evalChartO S _ hxS v
  have hdecomp := probePlaneDecomp k m hk hm t.1 x hxt w hmem
  have hline := probePlaneLine k m hk hm t.1 x hxt w hmem
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hline
  -- the reconstructed line element is the line element of `w`
  have hxi : probeXiCLM k m hk hm t.1 x (probeCpart k m hk hm t.1 x w)
      = cxE.symm (probeCy k m hk hm w) := by
    rw [probeXiCLM_apply, probeCpart_apply, ContinuousLinearEquiv.symm_apply_apply,
      Work.Gen.scF_mkF]
    simp only [starRingEnd_apply, star_star]
    rw [← hα, inner_smul_right]
    congr 1
    have hI : inner ℂ (cxOf (Work.Gen.uVec t.1 x)) (cxOf (Work.Gen.uVec t.1 x)) ≠ 0 := by
      rw [inner_self_ne_zero]
      exact cxOf_ne_zero (Work.Gen.uVec_ne_zero t.1 x)
    rw [mul_comm α (inner ℂ (cxOf (Work.Gen.uVec t.1 x)) (cxOf (Work.Gen.uVec t.1 x))),
      ← mul_assoc, inv_mul_cancel₀ hI, one_mul]
  -- the reconstruction is `w`
  have hrec : probeReconCLM k m hk hm t.1 x
      (Work.Whitney.sumFibreR 2 (k - 2)
        (probeCpart k m hk hm t.1 x w, probeUx k m hk w))
      = probeEmb k m hk hm (cxE (probeXiCLM k m hk hm t.1 x
          (probeCpart k m hk hm t.1 x w))) + probeTailComb k m hk (probeUx k m hk w) := by
    rw [probeReconCLM_apply]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [hrec, hxi, LinearIsometryEquiv.apply_symm_apply, ← hdecomp, hw]
  exact toECoordAt_evalChartO S (probeSigma k m hk hm x) hxS v

theorem probePhi_hright (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) (x : CP 2)
    (y : EuclideanSpace ℝ (Fin (2 + (k - 2))))
    (hb : x ∈ (Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) :
    probePhi k m hk hm S t x (probePhiInv k m hk hm S t x y) = y := by
  have hxS : probeSigma k m hk hm x ∈ baseSet S := hb.1
  have hxt : x ∈ Work.Projective.chartSet t.1 := by
    rw [Zt_baseSet k m t] at hb; exact hb.2
  rw [probePhiInv_apply_of_mem k m hk hm S t x hxS,
    probePhi_apply_of_mem k m hk hm S t x hxS]
  have hplane : memPlane (probeSigma k m hk hm x) (probeReconCLM k m hk hm t.1 x y) :=
    memPlane_probeRecon k m hk hm t.1 x hxt y
  rw [evalChartO_toECoordAt S (probeSigma k m hk hm x) hxS _ hplane]
  set a := ((Work.Whitney.sumFibreR 2 (k - 2)).symm y).1 with ha
  set τ := ((Work.Whitney.sumFibreR 2 (k - 2)).symm y).2 with hτ
  have hrec : probeReconCLM k m hk hm t.1 x y
      = probeEmb k m hk hm (cxE (probeXiCLM k m hk hm t.1 x a)) + probeTailComb k m hk τ := by
    rw [probeReconCLM_apply]
  have hu : probeUx k m hk (probeEmb k m hk hm (cxE (probeXiCLM k m hk hm t.1 x a))
      + probeTailComb k m hk τ) = τ := by
    rw [map_add, probeUx_probeEmb, zero_add, probeUx_tailComb]
  have hc : probeCpart k m hk hm t.1 x (probeEmb k m hk hm (cxE (probeXiCLM k m hk hm t.1 x a))
      + probeTailComb k m hk τ)
      = equivC1R2 (Work.Gen.mkF (starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec t.1 x))
          (probeXiCLM k m hk hm t.1 x a)))) := by
    rw [probeCpart_apply, map_add, probeCy_probeEmb, probeCy_tailComb, add_zero,
      LinearIsometryEquiv.symm_apply_apply]
  rw [hrec, hc, hu]
  -- the line coordinate of the reconstruction is the original one
  have hkey : starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec t.1 x))
      (probeXiCLM k m hk hm t.1 x a)) = Work.Gen.scF (equivC1R2.symm a) := by
    have hAnz : inner ℂ (cxOf (Work.Gen.uVec t.1 x)) (cxOf (Work.Gen.uVec t.1 x)) ≠ 0 := by
      rw [inner_self_ne_zero]
      exact cxOf_ne_zero (Work.Gen.uVec_ne_zero t.1 x)
    have hA : star (inner ℂ (cxOf (Work.Gen.uVec t.1 x)) (cxOf (Work.Gen.uVec t.1 x)))
        = inner ℂ (cxOf (Work.Gen.uVec t.1 x)) (cxOf (Work.Gen.uVec t.1 x)) := by
      rw [inner_self_eq_norm_sq_to_K, pow_two]
      simp
    have hcA : star ((inner ℂ (cxOf (Work.Gen.uVec t.1 x))
          (cxOf (Work.Gen.uVec t.1 x)))⁻¹)
        = ((inner ℂ (cxOf (Work.Gen.uVec t.1 x)) (cxOf (Work.Gen.uVec t.1 x)))⁻¹) := by
      rw [star_inv₀, hA]
    rw [probeXiCLM_apply, inner_smul_right, starRingEnd_apply, star_mul, star_mul,
      starRingEnd_apply, star_star, hA, hcA]
    rw [mul_comm (Work.Gen.scF (equivC1R2.symm a)), ← mul_assoc,
      mul_inv_cancel₀ hAnz, one_mul]
  rw [hkey, Work.Gen.mkF_scF, ContinuousLinearEquiv.apply_symm_apply]
  rw [show (a, τ) = (Work.Whitney.sumFibreR 2 (k - 2)).symm y from Prod.ext ha hτ]
  exact ContinuousLinearEquiv.apply_symm_apply (Work.Whitney.sumFibreR 2 (k - 2)) y

set_option backward.isDefEq.respectTransparency true

/-! ## Joint continuity of the pieces of the gauge -/

theorem continuous_probeCpart_joint (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) :
    Continuous (fun p : ↥(Work.Projective.chartSet i) × Amb (k + m) =>
      probeCpart k m hk hm i p.1.1 p.2) := by
  have hu : Continuous (fun p : ↥(Work.Projective.chartSet i) × Amb (k + m) =>
      Work.Gen.uVec i p.1.1) :=
    (continuousOn_uVec i).comp_continuous (continuous_subtype_val.comp continuous_fst)
      (fun p => p.1.2)
  have hcx : Continuous (fun p : ↥(Work.Projective.chartSet i) × Amb (k + m) =>
      cxOf (Work.Gen.uVec i p.1.1)) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℂ)).comp hu
  have hw : Continuous (fun p : ↥(Work.Projective.chartSet i) × Amb (k + m) =>
      cxE.symm (probeCy k m hk hm p.2)) :=
    (cxE.symm : Amb 6 →L[ℝ] E3).continuous.comp
      ((probeCy k m hk hm).continuous.comp continuous_snd)
  have hinner : Continuous (fun p : ↥(Work.Projective.chartSet i) × Amb (k + m) =>
      starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec i p.1.1))
        (cxE.symm (probeCy k m hk hm p.2)))) :=
    continuous_star.comp (continuous_inner.comp (hcx.prodMk hw))
  have hmk : Continuous (fun p : ↥(Work.Projective.chartSet i) × Amb (k + m) =>
      Work.Gen.mkF (starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec i p.1.1))
        (cxE.symm (probeCy k m hk hm p.2))))) :=
    Work.Gen.continuous_mkF.comp hinner
  refine Continuous.congr ?_ (fun p => (probeCpart_apply k m hk hm i p.1.1 p.2).symm)
  exact (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).continuous.comp hmk

theorem continuous_probeXiCLM_joint (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) :
    Continuous (fun p : ↥(Work.Projective.chartSet i) × EuclideanSpace ℝ (Fin 2) =>
      probeXiCLM k m hk hm i p.1.1 p.2) := by
  have hu : Continuous (fun p : ↥(Work.Projective.chartSet i) × EuclideanSpace ℝ (Fin 2) =>
      cxOf (Work.Gen.uVec i p.1.1)) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℂ)).comp
      ((continuousOn_uVec i).comp_continuous (continuous_subtype_val.comp continuous_fst)
      (fun p => p.1.2))
  have hA : Continuous (fun p : ↥(Work.Projective.chartSet i) × EuclideanSpace ℝ (Fin 2) =>
      inner ℂ (cxOf (Work.Gen.uVec i p.1.1)) (cxOf (Work.Gen.uVec i p.1.1))) :=
    continuous_inner.comp (hu.prodMk hu)
  have hAne : ∀ p : ↥(Work.Projective.chartSet i) × EuclideanSpace ℝ (Fin 2),
      inner ℂ (cxOf (Work.Gen.uVec i p.1.1)) (cxOf (Work.Gen.uVec i p.1.1)) ≠ 0 :=
    fun p => inner_self_ne_zero.mpr (cxOf_ne_zero (Work.Gen.uVec_ne_zero i p.1.1))
  have hb : Continuous (fun p : ↥(Work.Projective.chartSet i) × EuclideanSpace ℝ (Fin 2) =>
      starRingEnd ℂ (Work.Gen.scF (equivC1R2.symm p.2))) :=
    continuous_star.comp (Work.Gen.continuous_scF.comp
      ((equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℂ (Fin 1)).continuous.comp continuous_snd))
  have hsc : Continuous (fun p : ↥(Work.Projective.chartSet i) × EuclideanSpace ℝ (Fin 2) =>
      (inner ℂ (cxOf (Work.Gen.uVec i p.1.1)) (cxOf (Work.Gen.uVec i p.1.1)))⁻¹
        * starRingEnd ℂ (Work.Gen.scF (equivC1R2.symm p.2))) := hA.inv₀ hAne |>.mul hb
  refine Continuous.congr ?_ (fun p => (probeXiCLM_apply k m hk hm i p.1.1 p.2).symm)
  exact hsc.smul hu

theorem continuous_toECoordAtCLM_joint (S : ChartIdx k m) :
    Continuous (fun p : ↥(baseSet S) × Amb (k + m) => toECoordAtCLM S p.1.1 p.2) := by
  have hmat : Continuous (fun p : ↥(baseSet S) × Amb (k + m) =>
      matLin (orientMat S (p.1.1 : OG k m))) :=
    continuous_matLin.comp ((continuous_orientMat_subtype S).comp continuous_fst)
  have hvec : Continuous (fun p : ↥(baseSet S) × Amb (k + m) =>
      WithLp.toLp 2 (coordProj S (WithLp.ofLp p.2))) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin k => ℝ)).comp
      ((LinearMap.continuous_of_finiteDimensional (coordProj S)).comp
        ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin (k + m) => ℝ)).comp continuous_snd))
  refine Continuous.congr (hmat.clm_apply hvec) (fun p => ?_)
  show matLin (orientMat S (p.1.1 : OG k m)) (WithLp.toLp 2 (coordProj S (WithLp.ofLp p.2)))
    = toECoordAtCLM S p.1.1 p.2
  rw [toECoordAtCLM_apply, toECoordAt]

theorem probePhi_hcont (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) :
    ContinuousOn (fun x => probePhi k m hk hm S t x)
      ((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine Work.Thom.continuous_clm_of_continuous_apply_gen (𝕜 := ℝ)
    (fun x : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) =>
      probePhi k m hk hm S t x.1) ?_
  have hE : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) × Amb k =>
      evalChartO S ⟨probeSigma k m hk hm p.1.1, p.1.2.1⟩ p.2) :=
    (continuous_evalChartO S).comp (Continuous.prodMk (Continuous.subtype_mk
      ((probeSigma k m hk hm).continuous.comp (continuous_subtype_val.comp continuous_fst)) (fun p => p.1.2.1))
      continuous_snd)
  have hu : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) × Amb k =>
      cxOf (Work.Gen.uVec t.1 p.1.1)) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℂ)).comp
      ((continuousOn_uVec t.1).comp_continuous (continuous_subtype_val.comp continuous_fst)
        (fun p => (Zt_baseSet k m t).le p.1.2.2))
  have hw : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) × Amb k =>
      cxE.symm (probeCy k m hk hm
        (evalChartO S ⟨probeSigma k m hk hm p.1.1, p.1.2.1⟩ p.2))) :=
    (cxE.symm : Amb 6 →L[ℝ] E3).continuous.comp ((probeCy k m hk hm).continuous.comp hE)
  have hsc : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) × Amb k =>
      starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec t.1 p.1.1))
        (cxE.symm (probeCy k m hk hm
          (evalChartO S ⟨probeSigma k m hk hm p.1.1, p.1.2.1⟩ p.2))))) :=
    continuous_star.comp (continuous_inner.comp (hu.prodMk hw))
  have hcp : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) × Amb k =>
      equivC1R2 (Work.Gen.mkF (starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec t.1 p.1.1))
        (cxE.symm (probeCy k m hk hm
          (evalChartO S ⟨probeSigma k m hk hm p.1.1, p.1.2.1⟩ p.2))))))) :=
    (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).continuous.comp
      (Work.Gen.continuous_mkF.comp hsc)
  have hux : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) × Amb k =>
      probeUx k m hk (evalChartO S ⟨probeSigma k m hk hm p.1.1, p.1.2.1⟩ p.2)) :=
    (probeUx k m hk).continuous.comp hE
  have hfin : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) × Amb k =>
      Work.Whitney.sumFibreR 2 (k - 2)
        (equivC1R2 (Work.Gen.mkF (starRingEnd ℂ (inner ℂ (cxOf (Work.Gen.uVec t.1 p.1.1))
          (cxE.symm (probeCy k m hk hm
            (evalChartO S ⟨probeSigma k m hk hm p.1.1, p.1.2.1⟩ p.2)))))),
         probeUx k m hk (evalChartO S ⟨probeSigma k m hk hm p.1.1, p.1.2.1⟩ p.2))) :=
    (Work.Whitney.sumFibreR 2 (k - 2)).continuous.comp (hcp.prodMk hux)
  refine Continuous.congr hfin (fun p => ?_)
  rw [← probeCpart_apply]
  exact (probePhi_apply_of_mem k m hk hm S t p.1.1 p.1.2.1 p.2).symm

theorem probePhi_hcontinv (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (S : ChartIdx k m)
    (t : Fin 3 × Fin 1) :
    ContinuousOn (fun x => probePhiInv k m hk hm S t x)
      ((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine Work.Thom.continuous_clm_of_continuous_apply_gen (𝕜 := ℝ)
    (fun x : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t) =>
      probePhiInv k m hk hm S t x.1) ?_
  have ha : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      ((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).1) :=
    continuous_fst.comp ((Work.Whitney.sumFibreR 2 (k - 2)).symm.continuous.comp continuous_snd)
  have hτ : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      ((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).2) :=
    continuous_snd.comp ((Work.Whitney.sumFibreR 2 (k - 2)).symm.continuous.comp continuous_snd)
  have hu : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      cxOf (Work.Gen.uVec t.1 p.1.1)) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℂ)).comp
      ((continuousOn_uVec t.1).comp_continuous (continuous_subtype_val.comp continuous_fst)
        (fun p => (Zt_baseSet k m t).le p.1.2.2))
  have hA : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      inner ℂ (cxOf (Work.Gen.uVec t.1 p.1.1)) (cxOf (Work.Gen.uVec t.1 p.1.1))) :=
    continuous_inner.comp (hu.prodMk hu)
  have hAne : ∀ p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))),
      inner ℂ (cxOf (Work.Gen.uVec t.1 p.1.1)) (cxOf (Work.Gen.uVec t.1 p.1.1)) ≠ 0 :=
    fun p => inner_self_ne_zero.mpr (cxOf_ne_zero (Work.Gen.uVec_ne_zero t.1 p.1.1))
  have hstar : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      starRingEnd ℂ (Work.Gen.scF (equivC1R2.symm
        (((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).1)))) :=
    continuous_star.comp (Work.Gen.continuous_scF.comp
      ((equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℂ (Fin 1)).continuous.comp ha))
  have hxi : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      ((inner ℂ (cxOf (Work.Gen.uVec t.1 p.1.1))
          (cxOf (Work.Gen.uVec t.1 p.1.1)))⁻¹
        * starRingEnd ℂ (Work.Gen.scF (equivC1R2.symm
            (((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).1))))
        • cxOf (Work.Gen.uVec t.1 p.1.1)) :=
    (hA.inv₀ hAne).mul hstar |>.smul hu
  have hrecon : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      probeEmb k m hk hm (cxE (((inner ℂ (cxOf (Work.Gen.uVec t.1 p.1.1))
            (cxOf (Work.Gen.uVec t.1 p.1.1)))⁻¹
          * starRingEnd ℂ (Work.Gen.scF (equivC1R2.symm
              (((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).1))))
            • cxOf (Work.Gen.uVec t.1 p.1.1)))
        + probeTailComb k m hk ((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).2) :=
    ((probeEmb k m hk hm).continuous.comp ((cxE : E3 →L[ℝ] Amb 6).continuous.comp hxi)).add
      ((probeTailComb k m hk).continuous.comp hτ)
  have hmat : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      matLin (orientMat S (probeSigma k m hk hm p.1.1))) :=
    continuous_matLin.comp ((continuousOn_orientMat S).comp_continuous
      ((probeSigma k m hk hm).continuous.comp (continuous_subtype_val.comp continuous_fst)) (fun p => p.1.2.1))
  have hvec : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      WithLp.toLp 2 (coordProj S (WithLp.ofLp
        (probeEmb k m hk hm (cxE (((inner ℂ (cxOf (Work.Gen.uVec t.1 p.1.1))
              (cxOf (Work.Gen.uVec t.1 p.1.1)))⁻¹
            * starRingEnd ℂ (Work.Gen.scF (equivC1R2.symm
                (((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).1))))
              • cxOf (Work.Gen.uVec t.1 p.1.1)))
          + probeTailComb k m hk ((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).2)))) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin k => ℝ)).comp
      ((LinearMap.continuous_of_finiteDimensional (coordProj S)).comp
        ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin (k + m) => ℝ)).comp hrecon))
  have hjoint : Continuous (fun p : ↥((Zb k m hk hm).baseSet S ∩ (Zt k m).baseSet t)
      × EuclideanSpace ℝ (Fin (2 + (k - 2))) =>
      matLin (orientMat S (probeSigma k m hk hm p.1.1))
        (WithLp.toLp 2 (coordProj S (WithLp.ofLp
          (probeEmb k m hk hm (cxE (((inner ℂ (cxOf (Work.Gen.uVec t.1 p.1.1))
                (cxOf (Work.Gen.uVec t.1 p.1.1)))⁻¹
              * starRingEnd ℂ (Work.Gen.scF (equivC1R2.symm
                  (((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).1))))
                • cxOf (Work.Gen.uVec t.1 p.1.1)))
            + probeTailComb k m hk ((Work.Whitney.sumFibreR 2 (k - 2)).symm p.2).2))))) :=
    hmat.clm_apply hvec
  refine Continuous.congr hjoint (fun p => ?_)
  rw [probePhiInv_apply_of_mem k m hk hm S t p.1.1 p.1.2.1 p.2, toECoordAt,
    probeReconCLM_apply, probeXiCLM_apply]

/-- **The probe identifies the pulled-back tautological bundle with `zStd ⊕ ε^{k-2}`.** -/
theorem probeBundleIso_aux (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) :
    Nonempty (Work.Thom.BundleIso (Zb k m hk hm) (Zt k m)) :=
  Work.Thom.nonempty_bundleIso_of_gauge _ _ (probePhi k m hk hm) (probePhiInv k m hk hm)
    (probePhi_hcont k m hk hm) (probePhi_hcontinv k m hk hm)
    (probePhi_htgt k m hk hm) (probePhi_hsrc k m hk hm)
    (probePhi_htgtinv k m hk hm) (probePhi_hsrcinv k m hk hm)
    (probePhi_hleft k m hk hm) (probePhi_hright k m hk hm)

end

end Work.ThomBordism.Grassmann
