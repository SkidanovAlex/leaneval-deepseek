import Mathlib
import Submission.Work.Thom.realSumStableDefs
import Submission.Work.Thom.exists_rhoC_compat
import Submission.Work.Thom.BundleIso_comap_exists
import Submission.Work.Thom.sumStableMain
import Submission.Work.Thom.sumStableCorollaries
import Submission.Work.Thom.manifoldP1
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

/-!
# Stability of the Pontryagin classes

This module assembles the *real* incarnation of the stability of the characteristic classes,
`p₁(E ⊕ ε¹) = p₁(E)`, from the complex one (`Work.Thom.chernClass_sumEps`) and the explicit
splittings `Work.Thom.rhoR` / `Work.Thom.rhoC` (`Submission/Work/Thom/realSumStableDefs.lean`,
`Submission/Work/Thom/exists_rhoC_compat.lean`).

The two standard-fibre presentations used are

* `Work.Thom.sumEpsR ι₀ Z` — the real bundle `Z ⊕ ε¹` in the standard real fibre `ℝ^{k+1}`, with
  transition functions `rhoR k (Z.cc × id) (rhoR k)⁻¹`;
* `Work.Thom.sumEpsC ι₀ W` — the complex bundle `W ⊕ ε¹` in the standard complex fibre `ℂ^{m+1}`,
  with transition functions `rhoC m (W.cc × id) (rhoC m)⁻¹`.

Because `rhoC` is the *complexification* of `rhoR` (`Work.Thom.exists_rhoC_compat`), the
complexification of `sumEpsR ι₀ Z` is *literally* `sumEpsC ι₀ (complexificationCore Z)`
(`Work.Thom.complexificationCore_sumEpsR`), and `sumEpsC ι₀ W ≅ sumEps ι₀ W` by the constant gauge
`prodFinEquiv ∘ (rhoC)⁻¹`, so `chernClass` stability transfers.  The main results are

* `Work.Thom.chernClass_sumEpsC` — `c_j(W ⊕ ε¹) = c_j(W)` for the explicit complex presentation;
* `Work.Thom.chernClass_complexification_sumEpsR` — for real standard-fibre bundles `Z`, `Z'` with
  an isomorphism `sumEpsR ι₀ Z ≅ Z'`, `c_j(ℂZ') = c_j(ℂZ)`;
* `Work.Thom.pontryagin1_sumEpsR` — **`p₁(Z') = p₁(Z)`**.
-/

namespace Work.Thom

open Work.TangentClasses

open scoped RealInnerProductSpace

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- The defining equation of the complexification, as an identity of **continuous linear maps**. -/
theorem complexificationCore_coordChange_clm {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (i j : ι) (b : B) :
    (complexificationCore Z).coordChange i j b = cxTrans (Z.coordChange i j b) := by
  apply ContinuousLinearMap.ext
  intro v
  exact congrFun (complexificationCore_coordChange Z i j b) v


/-- **The complex splitting `ℂ^k × ℂ¹ ≃L[ℂ] ℂ^{k+1}`**, the complexification of the real splitting
`Work.Thom.rhoR k` (existence and the two characterising properties are
`Work.Thom.exists_rhoC_compat`). -/
noncomputable def rhoC (k : ℕ) :
    (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin 1)) ≃L[ℂ] EuclideanSpace ℂ (Fin (k + 1)) :=
  Classical.choose (exists_rhoC_compat k)

/-- The defining property of `Work.Thom.rhoC`: on real vectors it is `cxOfReal ∘ rhoR`. -/
theorem rhoC_cxOfReal (k : ℕ) (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin 1)) :
    rhoC k (cxOfReal u, cxOfReal v) = cxOfReal (rhoR k (u, v)) :=
  (Classical.choose_spec (exists_rhoC_compat k)).1 u v

/-- **The intertwining identity of the two splittings**: conjugating a real endomorphism of `ℝ^{k+1}`
by the real splitting and then complexifying is the same as conjugating its complexification by the
complex splitting. -/
theorem rhoC_conj (k : ℕ) (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (w : EuclideanSpace ℂ (Fin (k + 1))) :
    cxTrans (((rhoR k) : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (k + 1))).comp
        (((T.prodMap (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))).comp
          ((rhoR k).symm : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ]
            (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)))))) w
      = rhoC k (((cxTrans T).prodMap (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))))
          ((rhoC k).symm w)) :=
  (Classical.choose_spec (exists_rhoC_compat k)).2 T w

/-! ## The two standard-fibre presentations -/

/-- **The real sum `Z ⊕ ε¹` in the standard fibre `ℝ^{k+1}`**, along the *explicit* splitting
`rhoR k`. -/
noncomputable def sumEpsR (ι₀ : Type) [Inhabited ι₀] {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    RealBundle B (EuclideanSpace ℝ (Fin (k + 1))) (ι × ι₀) :=
  Classical.choose (exists_coreMapFibre (e := rhoR k)
    (bundleSum Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀)))

/-- The transition functions of `Work.Thom.sumEpsR`. -/
theorem sumEpsR_coordChange (ι₀ : Type) [Inhabited ι₀] {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (i j : ι × ι₀) (b : B) :
    (sumEpsR ι₀ Z).coordChange i j b
      = ((rhoR k) : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)) →L[ℝ]
            EuclideanSpace ℝ (Fin (k + 1))).comp
          (((bundleSum Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀)).coordChange i j b).comp
            ((rhoR k).symm : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ]
              (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)))) :=
  (Classical.choose_spec (exists_coreMapFibre (e := rhoR k)
    (bundleSum Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀)))).2.2.1 i j b

/-- The base sets of `Work.Thom.sumEpsR` are those of the Whitney sum. -/
theorem sumEpsR_baseSet (ι₀ : Type) [Inhabited ι₀] {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    (sumEpsR ι₀ Z).baseSet = (bundleSum Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀)).baseSet :=
  (Classical.choose_spec (exists_coreMapFibre (e := rhoR k)
    (bundleSum Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀)))).1

/-- The index map of `Work.Thom.sumEpsR` is that of the Whitney sum. -/
theorem sumEpsR_indexAt (ι₀ : Type) [Inhabited ι₀] {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    (sumEpsR ι₀ Z).indexAt = (bundleSum Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀)).indexAt :=
  (Classical.choose_spec (exists_coreMapFibre (e := rhoR k)
    (bundleSum Z (trivialVectorBundleCore ℝ B (EuclideanSpace ℝ (Fin 1)) ι₀)))).2.1

/-- **The complex sum `W ⊕ ε¹` in the standard fibre `ℂ^{m+1}`**, along the explicit splitting
`rhoC m`. -/
noncomputable def sumEpsC (ι₀ : Type) [Inhabited ι₀] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) (ι × ι₀) :=
  Classical.choose (exists_coreMapFibre (e := rhoC m)
    (bundleSum W (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))

/-- The transition functions of `Work.Thom.sumEpsC`. -/
theorem sumEpsC_coordChange (ι₀ : Type) [Inhabited ι₀] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i j : ι × ι₀) (b : B) :
    (sumEpsC ι₀ W).coordChange i j b
      = ((rhoC m) : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
            EuclideanSpace ℂ (Fin (m + 1))).comp
          (((bundleSum W (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)).coordChange
            i j b).comp
            ((rhoC m).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
              (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))) :=
  (Classical.choose_spec (exists_coreMapFibre (e := rhoC m)
    (bundleSum W (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))).2.2.1 i j b

/-- The base sets of `Work.Thom.sumEpsC` are those of the Whitney sum. -/
theorem sumEpsC_baseSet (ι₀ : Type) [Inhabited ι₀] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (sumEpsC ι₀ W).baseSet
      = (bundleSum W (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)).baseSet :=
  (Classical.choose_spec (exists_coreMapFibre (e := rhoC m)
    (bundleSum W (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))).1

/-- The index map of `Work.Thom.sumEpsC` is that of the Whitney sum. -/
theorem sumEpsC_indexAt (ι₀ : Type) [Inhabited ι₀] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (sumEpsC ι₀ W).indexAt
      = (bundleSum W (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)).indexAt :=
  (Classical.choose_spec (exists_coreMapFibre (e := rhoC m)
    (bundleSum W (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))).2.1

/-! ## The complexification of the real sum is the complex sum -/

/-- **The key core identity**: the complexification of `Work.Thom.sumEpsR ι₀ Z` *is*
`Work.Thom.sumEpsC ι₀ (complexificationCore Z)`.  Both have the same cover, base sets and index map,
and their transition functions agree by the intertwining identity `Work.Thom.rhoC_conj`. -/
theorem complexificationCore_sumEpsR (ι₀ : Type) [Inhabited ι₀] {k : ℕ}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    complexificationCore (sumEpsR ι₀ Z) = sumEpsC ι₀ (complexificationCore Z) := by
  refine bundleCore_ext ?_ ?_ ?_
  · funext i
    rw [complexificationCore_baseSet, sumEpsR_baseSet, sumEpsC_baseSet, bundleSum_baseSet,
      bundleSum_baseSet, complexificationCore_baseSet]
    rfl
  · funext b
    rw [complexificationCore_indexAt, sumEpsR_indexAt, sumEpsC_indexAt, bundleSum_indexAt,
      bundleSum_indexAt, complexificationCore_indexAt]
    rfl
  · intro i j b
    apply ContinuousLinearMap.ext
    intro w
    simp only [complexificationCore_coordChange_clm (sumEpsR ι₀ Z) i j b, sumEpsR_coordChange,
      sumEpsC_coordChange, complexificationCore_coordChange_clm Z i.1 j.1 b,
      bundleSum_trivial_coordChange, ContinuousLinearMap.comp_apply]
    exact rhoC_conj k (Z.coordChange i.1 j.1 b) w

/-! ## The constant gauge between the two complex presentations of `W ⊕ ε¹` -/

/-- The constant gauge `ℂ^{m+1} → ℂ^{m+1}` identifying the two standard-fibre presentations of
`W ⊕ ε¹`. -/
noncomputable def sumEpsC_gauge (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)) :=
  ((prodFinEquiv m) : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin (m + 1))).comp
    (((rhoC m).symm) : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))

/-- Its inverse. -/
noncomputable def sumEpsC_gaugeInv (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)) :=
  ((rhoC m) : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin (m + 1))).comp
    (((prodFinEquiv m).symm) : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))

theorem sumEpsC_gauge_comp (m : ℕ) : (sumEpsC_gauge m).comp (sumEpsC_gaugeInv m) = 1 := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.comp_apply, sumEpsC_gauge, sumEpsC_gaugeInv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem sumEpsC_gaugeInv_comp (m : ℕ) : (sumEpsC_gaugeInv m).comp (sumEpsC_gauge m) = 1 := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.comp_apply, sumEpsC_gauge, sumEpsC_gaugeInv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- **The transition functions of the two presentations of `W ⊕ ε¹` are conjugate by the constant
gauge `Work.Thom.sumEpsC_gauge`.** -/
theorem sumEpsC_gauge_conj (ι₀ : Type) [Inhabited ι₀] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i j : ι × ι₀) (b : B) :
    ((sumEps ι₀ W).coordChange i j b).comp (sumEpsC_gauge m)
      = (sumEpsC_gauge m).comp ((sumEpsC ι₀ W).coordChange i j b) := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, sumEpsC_coordChange, sumEps_coordChange,
    bundleSum_trivial_coordChange, sumEpsC_gauge, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The base sets of the two presentations agree. -/
theorem sumEpsC_baseSet_eq_sumEps_baseSet (ι₀ : Type) [Inhabited ι₀] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (sumEpsC ι₀ W).baseSet = (sumEps ι₀ W).baseSet := by
  rw [sumEpsC_baseSet, sumEps_baseSet]

/-- The index maps of the two presentations agree. -/
theorem sumEpsC_indexAt_eq_sumEps_indexAt (ι₀ : Type) [Inhabited ι₀] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (sumEpsC ι₀ W).indexAt = (sumEps ι₀ W).indexAt := by
  rw [sumEpsC_indexAt, sumEps_indexAt]

/-- A pointwise form of an identity of continuous linear maps. -/
theorem clm_apply_eq {m : ℕ} {A B : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
    EuclideanSpace ℂ (Fin (m + 1))} (h : A = B) (v : EuclideanSpace ℂ (Fin (m + 1))) :
    A v = B v :=
  congrFun (congrArg (fun C : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
    EuclideanSpace ℂ (Fin (m + 1)) => ⇑C) h) v

/-- **Chart expressions of a constant gauge.**  If two gluing data `X`, `Y` (same cover, same base
sets, same index map) have transition functions conjugate by a constant gauge `f` with inverse `g`,
then the two chart expressions of the gauge — the ones that the continuity of the total-space maps
of `f` and of `g` requires — are continuous. -/
theorem continuousOn_chartExpr_gauge {m : ℕ} {ι : Type}
    (X Y : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (f g : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (hfg : f.comp g = 1) (hgf : g.comp f = 1)
    (hbase : X.baseSet = Y.baseSet) (hindex : X.indexAt = Y.indexAt)
    (hconj : ∀ (i j : ι) (b : B), (Y.coordChange i j b).comp f = f.comp (X.coordChange i j b)) :
    (∀ i₁ i₂ : ι, ContinuousOn (fun b : B =>
        (Y.coordChange (Y.indexAt b) i₂ b).comp (f.comp (X.coordChange i₁ (X.indexAt b) b)))
        (X.baseSet i₁ ∩ Y.baseSet i₂)) ∧
    (∀ i₁ i₂ : ι, ContinuousOn (fun b : B =>
        (X.coordChange (X.indexAt b) i₂ b).comp (g.comp (Y.coordChange i₁ (Y.indexAt b) b)))
        (Y.baseSet i₁ ∩ X.baseSet i₂)) := by
  have hgf_pt : ∀ w : EuclideanSpace ℂ (Fin (m + 1)), g (f w) = w := fun w =>
    clm_apply_eq hgf w
  have hfg_pt : ∀ w : EuclideanSpace ℂ (Fin (m + 1)), f (g w) = w := fun w =>
    clm_apply_eq hfg w
  constructor
  · intro i₁ i₂
    have hsub : X.baseSet i₁ ∩ Y.baseSet i₂ ⊆ Y.baseSet i₁ ∩ Y.baseSet i₂ := by
      intro b hb
      refine ⟨?_, hb.2⟩
      rw [← hbase]
      exact hb.1
    have hcont : ContinuousOn (fun b : B => (Y.coordChange i₁ i₂ b).comp f)
        (X.baseSet i₁ ∩ Y.baseSet i₂) :=
      ((Y.continuousOn_coordChange i₁ i₂).mono hsub).clm_comp continuousOn_const
    refine hcont.congr (fun b hb => ?_)
    have hY : (Y.coordChange (Y.indexAt b) i₂ b).comp (Y.coordChange i₁ (Y.indexAt b) b)
        = Y.coordChange i₁ i₂ b :=
      Y.coordChange_linear_comp i₁ (Y.indexAt b) i₂ b
        ⟨⟨(by rw [← hbase]; exact hb.1), Y.mem_baseSet_at b⟩, hb.2⟩
    have hconjb : (Y.coordChange i₁ (Y.indexAt b) b).comp f
        = f.comp (X.coordChange i₁ (X.indexAt b) b) := by
      have h := hconj i₁ (X.indexAt b) b
      rw [← hindex]
      exact h
    calc (Y.coordChange (Y.indexAt b) i₂ b).comp (f.comp (X.coordChange i₁ (X.indexAt b) b))
        = (Y.coordChange (Y.indexAt b) i₂ b).comp
            ((Y.coordChange i₁ (Y.indexAt b) b).comp f) := by
            rw [hconjb]
      _ = ((Y.coordChange (Y.indexAt b) i₂ b).comp (Y.coordChange i₁ (Y.indexAt b) b)).comp f := by
            rw [ContinuousLinearMap.comp_assoc]
      _ = (Y.coordChange i₁ i₂ b).comp f := by rw [hY]
  · intro i₁ i₂
    have hsub : Y.baseSet i₁ ∩ X.baseSet i₂ ⊆ X.baseSet i₁ ∩ X.baseSet i₂ := by
      intro b hb
      refine ⟨?_, hb.2⟩
      rw [hbase]
      exact hb.1
    have hcont : ContinuousOn (fun b : B => (X.coordChange i₁ i₂ b).comp g)
        (Y.baseSet i₁ ∩ X.baseSet i₂) :=
      ((X.continuousOn_coordChange i₁ i₂).mono hsub).clm_comp continuousOn_const
    refine hcont.congr (fun b hb => ?_)
    have hX : (X.coordChange (X.indexAt b) i₂ b).comp (X.coordChange i₁ (X.indexAt b) b)
        = X.coordChange i₁ i₂ b :=
      X.coordChange_linear_comp i₁ (X.indexAt b) i₂ b
        ⟨⟨(by rw [hbase]; exact hb.1), X.mem_baseSet_at b⟩, hb.2⟩
    have h1 : (Y.coordChange i₁ (Y.indexAt b) b).comp f
        = f.comp (X.coordChange i₁ (X.indexAt b) b) := by
      have h := hconj i₁ (X.indexAt b) b
      rw [← hindex]
      exact h
    have hconjb : (X.coordChange i₁ (X.indexAt b) b).comp g
        = g.comp (Y.coordChange i₁ (Y.indexAt b) b) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply]
      have h1v : Y.coordChange i₁ (Y.indexAt b) b (f (g v))
          = f ((X.coordChange i₁ (X.indexAt b) b) (g v)) := clm_apply_eq h1 (g v)
      rw [hfg_pt v] at h1v
      rw [← hgf_pt ((X.coordChange i₁ (X.indexAt b) b) (g v)), ← h1v]
    calc (X.coordChange (X.indexAt b) i₂ b).comp (g.comp (Y.coordChange i₁ (Y.indexAt b) b))
        = (X.coordChange (X.indexAt b) i₂ b).comp
            ((X.coordChange i₁ (X.indexAt b) b).comp g) := by
            rw [hconjb]
      _ = ((X.coordChange (X.indexAt b) i₂ b).comp (X.coordChange i₁ (X.indexAt b) b)).comp g := by
            rw [ContinuousLinearMap.comp_assoc]
      _ = (X.coordChange i₁ i₂ b).comp g := by rw [hX]

/-- **The two complex presentations of `W ⊕ ε¹` are isomorphic** by the constant gauge. -/
theorem nonempty_bundleIso_sumEpsC (ι₀ : Type) [Inhabited ι₀] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Nonempty (BundleIso (sumEpsC ι₀ W) (sumEps ι₀ W)) := by
  have hchart := continuousOn_chartExpr_gauge (sumEpsC ι₀ W) (sumEps ι₀ W)
    (sumEpsC_gauge m) (sumEpsC_gaugeInv m) (sumEpsC_gauge_comp m) (sumEpsC_gaugeInv_comp m)
    (sumEpsC_baseSet_eq_sumEps_baseSet ι₀ W) (sumEpsC_indexAt_eq_sumEps_indexAt ι₀ W)
    (sumEpsC_gauge_conj ι₀ W)
  refine ⟨{ hom := fun _ => (sumEpsC_gauge m).toLinearMap
            inv := fun _ => (sumEpsC_gaugeInv m).toLinearMap
            left_inv := fun _ x => ?_
            right_inv := fun _ y => ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · show (sumEpsC_gaugeInv m) ((sumEpsC_gauge m) x) = x
    simp only [sumEpsC_gauge, sumEpsC_gaugeInv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  · show (sumEpsC_gauge m) ((sumEpsC_gaugeInv m) y) = y
    simp only [sumEpsC_gauge, sumEpsC_gaugeInv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  · exact continuous_totalSpaceMap_clm (sumEpsC ι₀ W) (sumEps ι₀ W) (ContinuousMap.id B)
      (fun _ => sumEpsC_gauge m) (fun i₁ i₂ => hchart.1 i₁ i₂)
  · exact continuous_totalSpaceMap_clm (sumEps ι₀ W) (sumEpsC ι₀ W) (ContinuousMap.id B)
      (fun _ => sumEpsC_gaugeInv m) (fun i₁ i₂ => hchart.2 i₁ i₂)

/-- **Stability for the explicit complex presentation**: `c_j(W ⊕ ε¹) = c_j(W)`. -/
theorem chernClass_sumEpsC (ι₀ : Type) [Inhabited ι₀] [Fintype ι] [Fintype ι₀] {m : ℕ}
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (j : ℕ) :
    chernClass (m + 1) j (sumEpsC ι₀ W) = chernClass m j W := by
  obtain ⟨e⟩ := nonempty_bundleIso_sumEpsC ι₀ W
  exact chernClass_eq_of_bundleIso_sumEps W (sumEpsC ι₀ W) e j

/-! ## Complexifying a real bundle isomorphism, and the real stability -/

/-- **The chart expression of the complexification of a real bundle isomorphism is continuous**:
it is the `cxTrans`-image of the (continuous) chart expression of `e`
(`Work.Thom.continuousOn_chartExpressionCLM_gen`), transported along the continuous map
`Work.Thom.cxTrans`. -/
theorem continuousOn_cxTrans_chartExpression {n : ℕ} {ι ι' : Type}
    (Z : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin n)) ι)
    (Z' : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin n)) ι')
    (e : BundleIso Z Z') (i₁ : ι) (i₂ : ι') :
    ContinuousOn (fun b : B =>
      cxTrans ((Z'.coordChange (Z'.indexAt b) i₂ b).comp
        ((e.clmGen b).comp (Z.coordChange i₁ (Z.indexAt b) b))))
      (Z.baseSet i₁ ∩ Z'.baseSet i₂) :=
  (continuous_cxTrans (k := n)).comp_continuousOn
    (continuousOn_chartExpressionCLM_gen Z Z' e i₁ i₂)

/-- **Complexification of a real bundle isomorphism** between standard-fibre real bundles: the
gauge `b ↦ cxTrans (e.clmGen b)`. -/
theorem nonempty_complexificationCore_bundleIso (ι₀ : Type) [Inhabited ι₀] {k : ℕ} {ι' : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin (k + 1))) ι')
    (e : BundleIso (sumEpsR ι₀ Z) Z') :
    Nonempty (BundleIso (complexificationCore (sumEpsR ι₀ Z)) (complexificationCore Z')) := by
  refine ⟨{ hom := fun b => (cxTrans (e.clmGen b)).toLinearMap
            inv := fun b => (cxTrans (e.symm.clmGen b)).toLinearMap
            left_inv := fun b x => ?_
            right_inv := fun b y => ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · show cxTrans (e.symm.clmGen b) (cxTrans (e.clmGen b) x) = x
    rw [← ContinuousLinearMap.comp_apply, ← cxTrans_comp]
    have hcomp : (e.symm.clmGen b).comp (e.clmGen b) = 1 := by
      apply ContinuousLinearMap.ext
      intro z
      rw [ContinuousLinearMap.comp_apply, BundleIso.clmGen_apply, BundleIso.clmGen_apply]
      exact e.left_inv b z
    rw [hcomp, cxTrans_one]
    rfl
  · show cxTrans (e.clmGen b) (cxTrans (e.symm.clmGen b) y) = y
    rw [← ContinuousLinearMap.comp_apply, ← cxTrans_comp]
    have hcomp : (e.clmGen b).comp (e.symm.clmGen b) = 1 := by
      apply ContinuousLinearMap.ext
      intro z
      rw [ContinuousLinearMap.comp_apply, BundleIso.clmGen_apply, BundleIso.clmGen_apply]
      exact e.right_inv b z
    rw [hcomp, cxTrans_one]
    rfl
  · refine continuous_totalSpaceMap_clm (complexificationCore (sumEpsR ι₀ Z))
      (complexificationCore Z') (ContinuousMap.id B) (fun b => cxTrans (e.clmGen b)) ?_
    intro i₁ i₂
    refine (continuousOn_cxTrans_chartExpression (sumEpsR ι₀ Z) Z' e i₁ i₂).congr
      (fun b hb => ?_)
    simp only [ContinuousMap.id_apply, complexificationCore_indexAt]
    rw [complexificationCore_coordChange_clm (sumEpsR ι₀ Z) i₁ _ b,
      complexificationCore_coordChange_clm Z' _ i₂ b]
    rw [← cxTrans_comp, ← cxTrans_comp]
  · refine continuous_totalSpaceMap_clm (complexificationCore Z')
      (complexificationCore (sumEpsR ι₀ Z)) (ContinuousMap.id B)
      (fun b => cxTrans (e.symm.clmGen b)) ?_
    intro i₁ i₂
    refine (continuousOn_cxTrans_chartExpression Z' (sumEpsR ι₀ Z) e.symm i₁ i₂).congr
      (fun b hb => ?_)
    simp only [ContinuousMap.id_apply, complexificationCore_indexAt]
    rw [complexificationCore_coordChange_clm (sumEpsR ι₀ Z) _ i₂ b,
      complexificationCore_coordChange_clm Z' i₁ _ b]
    rw [← cxTrans_comp, ← cxTrans_comp]

/-! ## The stability of the Pontryagin classes -/

/-- **Stability of the complexified real sum**: for real standard-fibre bundles `Z` of rank `k` and
`Z'` of rank `k+1` with an isomorphism `sumEpsR ι₀ Z ≅ Z'` (i.e. `Z'` is a presentation of
`Z ⊕ ε¹`), the Chern classes of the complexifications agree. -/
theorem chernClass_complexification_sumEpsR (ι₀ : Type) [Inhabited ι₀] [Fintype ι]
    [Fintype ι₀] {k : ℕ} {ι' : Type} [Fintype ι']
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin (k + 1))) ι')
    (e : BundleIso (sumEpsR ι₀ Z) Z') (j : ℕ) :
    chernClass (k + 1) j (complexificationCore Z')
      = chernClass k j (complexificationCore Z) := by
  obtain ⟨e'⟩ := nonempty_complexificationCore_bundleIso ι₀ Z Z' e
  rw [← chernClass_BundleIso (j := j) (complexificationCore (sumEpsR ι₀ Z))
    (complexificationCore Z') e']
  rw [complexificationCore_sumEpsR ι₀ Z]
  exact chernClass_sumEpsC ι₀ (complexificationCore Z) j

/-- **STABILITY OF THE FIRST PONTRYAGIN CLASS**: adding a trivial real line summand does not change
`p₁`.  This is deliverable item 3 for real bundles, and the input of `p₁(TSⁿ) = 0` for stably
trivial bundles. -/
theorem pontryagin1_sumEpsR (ι₀ : Type) [Inhabited ι₀] [Fintype ι] [Fintype ι₀]
    {k : ℕ} {ι' : Type} [Fintype ι']
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin (k + 1))) ι')
    (e : BundleIso (sumEpsR ι₀ Z) Z') :
    pontryagin1 Z' = pontryagin1 Z := by
  rw [pontryagin1_def, pontryagin1_def,
    chernClass_complexification_sumEpsR ι₀ Z Z' e 2]

end

end Work.Thom
