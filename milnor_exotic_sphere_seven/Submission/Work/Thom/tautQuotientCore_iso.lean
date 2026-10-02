import Mathlib
import Submission.Work.Thom.coreMorphism
import Submission.Work.Thom.realification_homeo
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.Iso
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.tautQuotientCore_defs
import Submission.Work.Thom.continuousOn_quoCLM
import Submission.Work.Thom.continuousOn_chartExpressionCLM

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
# The tautological quotient is natural under a bundle isomorphism

For a bundle isomorphism `e : BundleIso Z Z'` of two complex bundles of rank `m + 1` over `B`, with
induced homeomorphism `φ = Work.Thom.punctHomeo Z Z' e` of the punctured total spaces, the
tautological quotients are isomorphic:

`Work.Thom.tautQuotientCore Z ≅ φ^*(Work.Thom.tautQuotientCore Z')`.

The fibrewise linear map is `Work.Thom.gaugeFwd e` and its inverse `Work.Thom.gaugeBwd e`.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {m : ℕ} {B : Type} [TopologicalSpace B] {ι ι' : Type}

/-! ## Elementary facts about the preferred chart -/

/-- The preferred-chart coordinate of a point of `realification Z` is its own fibre vector. -/
theorem localTriv_indexAt_snd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (p : (realification Z).TotalSpace) :
    (Z.localTriv (Z.indexAt p.1) p).2 = p.2 := by
  rw [VectorBundleCore.localTriv_apply, Z.coordChange_self _ _ (Z.mem_baseSet_at p.1)]

/-- `Work.Thom.tqCoord` selects a coordinate of the fibre vector itself, which is non-zero. -/
theorem tqCoord_spec' (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    (fibre p).ofLp (tqCoord Z p) ≠ 0 := by
  have h := tqCoord_spec Z p
  rwa [localTriv_indexAt_snd Z (p : (realification Z).TotalSpace)] at h

/-- **The punctured homeomorphism of a bundle isomorphism acts on the fibre vector by the
fibrewise map of the isomorphism.** -/
theorem punctHomeo_snd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι')
    (f : BundleIso Z Z') (p : ↥(zeroComplement (realification Z))) :
    ((punctHomeo Z Z' f p : (realification Z').TotalSpace)).2 =
      f.hom ((p : (realification Z).TotalSpace).1) ((p : (realification Z).TotalSpace).2) := by
  show (f.punctHomeomorph (zeroComplementHomeomorph Z p) : Z'.TotalSpace).2 = _
  rw [BundleIso.punctHomeomorph_apply, BundleIso.punctMap_apply]
  rfl

/-- The fibre vector of the punctured homeomorphism, in the form used below. -/
theorem punctHomeo_snd' (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι')
    (f : BundleIso Z Z') (p : ↥(zeroComplement (realification Z))) :
    ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
        (realification Z').TotalSpace).2 =
      f.clm ((p : (realification Z).TotalSpace).1) (fibre p) := by
  rw [punctHomeo_snd Z Z' f p, BundleIso.clm_apply]
  rfl

/-! ## The transport identity at the level of continuous linear maps -/

/-- `Work.Thom.quoFun_transport`, as an identity of continuous linear maps. -/
theorem quoCLM_comp_transport {n : ℕ} (l o : Fin (n+1))
    (A : EuclideanSpace ℂ (Fin (n+1)) →L[ℂ] EuclideanSpace ℂ (Fin (n+1)))
    (wj wm : EuclideanSpace ℂ (Fin (n+1))) (hwj : wj.ofLp l ≠ 0) (hwm : wm.ofLp o ≠ 0)
    (hA : A wj = wm) :
    (quoCLM o wm).comp A
      = (quoCLM o wm).comp ((A.comp (fillCLM l)).comp (quoCLM l wj)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, quoCLM_apply, fillCLM_apply]
  exact quoFun_transport l o A wj wm u hwj hwm hA

/-- `Work.Thom.quoFun_fillFun`, as an identity of continuous linear maps. -/
theorem quoCLM_comp_fillCLM {n : ℕ} (l : Fin (n+1)) (w : EuclideanSpace ℂ (Fin (n+1)))
    (hw : w.ofLp l ≠ 0) :
    (quoCLM l w).comp (fillCLM l) = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n)) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact quoFun_fillFun l w z hw

/-! ## The defining formulas of the two gauges -/

variable {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
  {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι'}

theorem gaugeFwd_apply (f : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) (x : EuclideanSpace ℂ (Fin m)) :
    gaugeFwd f p x =
      quoFun (tqCoord Z' (punctHomeo Z Z' f p))
        ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
          (realification Z').TotalSpace).2
        (f.clm ((p : (realification Z).TotalSpace).1) (fillFun (tqCoord Z p) x)) := by
  rw [gaugeFwd, punctHomeo_snd']
  simp only [ContinuousLinearMap.comp_apply, fillCLM_apply, quoCLM_apply]

theorem gaugeBwd_apply (f : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) (y : EuclideanSpace ℂ (Fin m)) :
    gaugeBwd f p y =
      quoFun (tqCoord Z p) (fibre p)
        (f.symm.clm ((p : (realification Z).TotalSpace).1)
          (fillFun (tqCoord Z' (punctHomeo Z Z' f p)) y)) := by
  rw [gaugeBwd]
  simp only [ContinuousLinearMap.comp_apply, fillCLM_apply, quoCLM_apply]

/-! ## The two gauges are mutually inverse -/

theorem gaugeBwd_gaugeFwd (f : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) (x : EuclideanSpace ℂ (Fin m)) :
    gaugeBwd f p (gaugeFwd f p x) = x := by
  rw [gaugeFwd_apply, gaugeBwd_apply]
  have hwm : (fibre p).ofLp (tqCoord Z p) ≠ 0 := tqCoord_spec' Z p
  have hwj : (f.clm ((p : (realification Z).TotalSpace).1) (fibre p)).ofLp
      (tqCoord Z' (punctHomeo Z Z' f p)) ≠ 0 := by
    have h := tqCoord_spec' Z' (punctHomeo Z Z' f p)
    rw [show fibre (Z := Z') (punctHomeo Z Z' f p) = ((punctHomeo Z Z' f p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace).2 from rfl,
      punctHomeo_snd Z Z' f p, ← BundleIso.clm_apply] at h
    simpa only [fibre] using h
  have hA : f.symm.clm ((p : (realification Z).TotalSpace).1)
      (f.clm ((p : (realification Z).TotalSpace).1) (fibre p)) = fibre p := by
    rw [BundleIso.clm_apply, BundleIso.clm_apply]
    exact f.left_inv _ _
  rw [show ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
      (realification Z').TotalSpace).2 =
      f.clm ((p : (realification Z).TotalSpace).1) (fibre p) from punctHomeo_snd' Z Z' f p,
    ← quoFun_transport (tqCoord Z' (punctHomeo Z Z' f p)) (tqCoord Z p)
      (f.symm.clm ((p : (realification Z).TotalSpace).1))
      (f.clm ((p : (realification Z).TotalSpace).1) (fibre p)) (fibre p)
      (f.clm ((p : (realification Z).TotalSpace).1) (fillFun (tqCoord Z p) x))
      hwj hwm hA]
  have hEE : f.symm.clm ((p : (realification Z).TotalSpace).1)
      (f.clm ((p : (realification Z).TotalSpace).1) (fillFun (tqCoord Z p) x))
      = fillFun (tqCoord Z p) x := by
    rw [BundleIso.clm_apply, BundleIso.clm_apply]
    exact f.left_inv _ _
  rw [hEE]
  exact quoFun_fillFun (tqCoord Z p) (fibre p) x hwm

theorem gaugeFwd_gaugeBwd (f : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) (y : EuclideanSpace ℂ (Fin m)) :
    gaugeFwd f p (gaugeBwd f p y) = y := by
  rw [gaugeFwd_apply, gaugeBwd_apply]
  have hwm : (fibre p).ofLp (tqCoord Z p) ≠ 0 := tqCoord_spec' Z p
  have hwj : (f.clm ((p : (realification Z).TotalSpace).1) (fibre p)).ofLp
      (tqCoord Z' (punctHomeo Z Z' f p)) ≠ 0 := by
    have h := tqCoord_spec' Z' (punctHomeo Z Z' f p)
    rw [show fibre (Z := Z') (punctHomeo Z Z' f p) = ((punctHomeo Z Z' f p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace).2 from rfl,
      punctHomeo_snd Z Z' f p, ← BundleIso.clm_apply] at h
    simpa only [fibre] using h
  rw [show ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
      (realification Z').TotalSpace).2 =
      f.clm ((p : (realification Z).TotalSpace).1) (fibre p) from punctHomeo_snd' Z Z' f p,
    ← quoFun_transport (tqCoord Z p) (tqCoord Z' (punctHomeo Z Z' f p))
      (f.clm ((p : (realification Z).TotalSpace).1)) (fibre p)
      (f.clm ((p : (realification Z).TotalSpace).1) (fibre p))
      (f.symm.clm ((p : (realification Z).TotalSpace).1)
        (fillFun (tqCoord Z' (punctHomeo Z Z' f p)) y))
      hwm hwj rfl]
  have hEE : f.clm ((p : (realification Z).TotalSpace).1)
      (f.symm.clm ((p : (realification Z).TotalSpace).1)
        (fillFun (tqCoord Z' (punctHomeo Z Z' f p)) y))
      = fillFun (tqCoord Z' (punctHomeo Z Z' f p)) y := by
    rw [BundleIso.clm_apply, BundleIso.clm_apply]
    exact f.right_inv _ _
  rw [hEE]
  exact quoFun_fillFun (tqCoord Z' (punctHomeo Z Z' f p)) _ y hwj

/-! ## Membership in the charts -/

theorem mem_tqBaseSet_of {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    {i : ι} {k : Fin (m+1)} {p : ↥(zeroComplement (realification Z))}
    (h : p ∈ (tautQuotientCore Z).baseSet (i, k)) :
    ((p : (realification Z).TotalSpace).1) ∈ Z.baseSet i ∧
      (Z.localTriv i (p : (realification Z).TotalSpace)).2 k ≠ 0 := by
  have h' : p ∈ tqBaseSet Z i k := by rwa [tautQuotientCore_baseSet] at h
  simpa only [tqBaseSet, Set.mem_ofPred_eq] using h'

/-- The membership facts on the common cover used in the two comparison lemmas. -/
theorem mem_s_fwd {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι'}
    (e : BundleIso Z Z') {i : ι} {i' : ι'} {k₁ k₂ : Fin (m+1)}
    {p : ↥(zeroComplement (realification Z))}
    (hp : p ∈ (tautQuotientCore Z).baseSet (i, k₁) ∩
      (bundleComap (tautQuotientCore Z') (punctHomeo Z Z' e)).baseSet (i', k₂)) :
    (((p : (realification Z).TotalSpace).1) ∈ Z.baseSet i) ∧
      (((p : (realification Z).TotalSpace).1) ∈ Z'.baseSet i') ∧
      (phiCoord e i' p) k₂ ≠ 0 := by
  obtain ⟨h1, h2⟩ := mem_tqBaseSet_of hp.1
  have h3 : (punctHomeo Z Z' e p) ∈ (tautQuotientCore Z').baseSet (i', k₂) := by
    have hh := hp.2
    rw [bundleComap_baseSet] at hh
    exact hh
  obtain ⟨h3', h4⟩ := mem_tqBaseSet_of (Z := Z') h3
  refine ⟨h1, ?_, ?_⟩
  · rwa [← punctHomeo_proj Z Z' e p]
  · simpa only [phiCoord] using h4

/-! ## Continuity prerequisites -/

/-- **The `Z'`-chart coordinate of the punctured map of a bundle isomorphism is continuous.** -/
theorem continuousOn_localTriv_snd_punctHomeo
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι')
    (f : BundleIso Z Z') (i' : ι') :
    ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      (((realification Z').localTriv i')
        ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
          (realification Z').TotalSpace)).2)
      {p | ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
          (realification Z').TotalSpace) ∈ ((realification Z').localTriv i').source} := by
  have hg : Continuous (fun p : ↥(zeroComplement (realification Z)) =>
      ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
        (realification Z').TotalSpace)) :=
    continuous_subtype_val.comp (punctHomeo Z Z' f).continuous
  have h1 : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      ((realification Z').localTriv i')
        ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
          (realification Z').TotalSpace))
      {p | ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
          (realification Z').TotalSpace) ∈ ((realification Z').localTriv i').source} :=
    ((realification Z').localTriv i').continuousOn.comp hg.continuousOn (fun p hp => hp)
  exact continuous_snd.comp_continuousOn h1

/-! ## The comparison of the chart expressions of the tautological quotients -/

theorem gaugeFwd_chart_comp (f : BundleIso Z Z') (i : ι) (i' : ι')
    (k₁ k₂ : Fin (m+1)) (p : ↥(zeroComplement (realification Z)))
    (hwg : (phiCoord f i' p) k₂ ≠ 0) :
    ((bundleComap (tautQuotientCore Z') (punctHomeo Z Z' f)).coordChange
        ((bundleComap (tautQuotientCore Z') (punctHomeo Z Z' f)).indexAt p) (i', k₂) p).comp
      ((gaugeFwd f p).comp ((tautQuotientCore Z).coordChange (i, k₁)
        ((tautQuotientCore Z).indexAt p) p))
    = (quoCLM k₂ (phiCoord f i' p)).comp
      (((Z'.coordChange (Z'.indexAt (phiBase f p)) i' (phiBase f p)).comp
        ((f.clm ((p : (realification Z).TotalSpace).1)).comp
          (Z.coordChange i (Z.indexAt ((p : (realification Z).TotalSpace).1))
            ((p : (realification Z).TotalSpace).1)))).comp
        (fillCLM k₁)) := by
  have hQ : (tautQuotientCore Z).coordChange (i, k₁)
        ((tautQuotientCore Z).indexAt p) p
      = (quoCLM (tqCoord Z p) (fibre p)).comp
        ((Z.coordChange i (Z.indexAt ((p : (realification Z).TotalSpace).1))
            ((p : (realification Z).TotalSpace).1)).comp (fillCLM k₁)) := by
    rw [tautQuotientCore_indexAt]
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply, fillCLM_apply, quoCLM_apply]
    rw [tautQuotientCore_coordChange]
    exact congrArg (fun w => quoFun (tqCoord Z p) w
        (Z.coordChange i (Z.indexAt ((p : (realification Z).TotalSpace).1))
          ((p : (realification Z).TotalSpace).1) (fillFun k₁ z)))
      (show (Z.localTriv (Z.indexAt (p : (realification Z).TotalSpace).1)
          (p : (realification Z).TotalSpace)).2 = fibre p from
        localTriv_indexAt_snd Z (p : (realification Z).TotalSpace))
  have hP : (bundleComap (tautQuotientCore Z') (punctHomeo Z Z' f)).coordChange
        ((bundleComap (tautQuotientCore Z') (punctHomeo Z Z' f)).indexAt p) (i', k₂) p
      = (quoCLM k₂ (phiCoord f i' p)).comp
        ((Z'.coordChange (Z'.indexAt (phiBase f p)) i' (phiBase f p)).comp
          (fillCLM (tqCoord Z' (punctHomeo Z Z' f p)))) := by
    rw [bundleComap_coordChange, bundleComap_indexAt, tautQuotientCore_indexAt]
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply, fillCLM_apply, quoCLM_apply]
    rw [tautQuotientCore_coordChange]
    simp only [phiCoord, phiBase]
    rfl
  have hwm : (fibre p).ofLp (tqCoord Z p) ≠ 0 := tqCoord_spec' Z p
  have hwj : (f.clm ((p : (realification Z).TotalSpace).1) (fibre p)).ofLp
      (tqCoord Z' (punctHomeo Z Z' f p)) ≠ 0 := by
    have h := tqCoord_spec' Z' (punctHomeo Z Z' f p)
    rw [show fibre (Z := Z') (punctHomeo Z Z' f p) = ((punctHomeo Z Z' f p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace).2 from rfl,
      punctHomeo_snd Z Z' f p, ← BundleIso.clm_apply] at h
    simpa only [fibre] using h
  have hA : (Z'.coordChange (Z'.indexAt (phiBase f p)) i' (phiBase f p))
      (f.clm ((p : (realification Z).TotalSpace).1) (fibre p)) = phiCoord f i' p := by
    rw [← punctHomeo_snd' Z Z' f p]
    simp only [phiCoord, phiBase, VectorBundleCore.localTriv_apply]
  rw [hQ, hP, gaugeFwd]
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, fillCLM_apply, quoCLM_apply]
  rw [← quoFun_transport (tqCoord Z p) (tqCoord Z' (punctHomeo Z Z' f p))
      (f.clm ((p : (realification Z).TotalSpace).1)) (fibre p)
      (f.clm ((p : (realification Z).TotalSpace).1) (fibre p))
      ((Z.coordChange i (Z.indexAt ((p : (realification Z).TotalSpace).1))
          ((p : (realification Z).TotalSpace).1)) (fillFun k₁ z))
      hwm hwj rfl,
    ← quoFun_transport (tqCoord Z' (punctHomeo Z Z' f p)) k₂
      (Z'.coordChange (Z'.indexAt (phiBase f p)) i' (phiBase f p))
      (f.clm ((p : (realification Z).TotalSpace).1) (fibre p))
      (phiCoord f i' p)
      (f.clm ((p : (realification Z).TotalSpace).1)
        ((Z.coordChange i (Z.indexAt ((p : (realification Z).TotalSpace).1))
          ((p : (realification Z).TotalSpace).1)) (fillFun k₁ z)))
      hwj hwg hA]

/-! ## Membership in the common cover, backwards -/

theorem mem_s_bwd {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι'}
    (e : BundleIso Z Z') {i : ι} {i' : ι'} {k₁ k₂ : Fin (m+1)}
    {p : ↥(zeroComplement (realification Z))}
    (hp : p ∈ (bundleComap (tautQuotientCore Z') (punctHomeo Z Z' e)).baseSet (i', k₂) ∩
      (tautQuotientCore Z).baseSet (i, k₁)) :
    (((p : (realification Z).TotalSpace).1) ∈ Z.baseSet i) ∧
      (((p : (realification Z).TotalSpace).1) ∈ Z'.baseSet i') ∧
      (zCoord i p) k₁ ≠ 0 := by
  obtain ⟨h1', h2'⟩ := mem_tqBaseSet_of hp.2
  have h1 : (punctHomeo Z Z' e p) ∈ (tautQuotientCore Z').baseSet (i', k₂) := by
    have hh := hp.1
    rw [bundleComap_baseSet] at hh
    exact hh
  obtain ⟨h3', h4'⟩ := mem_tqBaseSet_of (Z := Z') h1
  refine ⟨h1', ?_, ?_⟩
  · rwa [← punctHomeo_proj Z Z' e p]
  · simpa only [zCoord] using h2'

theorem localTriv_indexAt_phi (f : BundleIso Z Z') (p : ↥(zeroComplement (realification Z))) :
    (Z'.localTriv (Z'.indexAt (phiBase f p)) ((punctHomeo Z Z' f p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace)).2
      = f.clm ((p : (realification Z).TotalSpace).1) (fibre p) := by
  rw [show (Z'.localTriv (Z'.indexAt (phiBase f p)) ((punctHomeo Z Z' f p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace)).2
      = ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
          (realification Z').TotalSpace).2 from
    localTriv_indexAt_snd Z' ((punctHomeo Z Z' f p :
      ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace)]
  exact punctHomeo_snd' Z Z' f p

/-! ## The comparison of the chart expressions, backwards -/

theorem gaugeBwd_chart_comp (f : BundleIso Z Z') (i : ι) (i' : ι')
    (k₁ k₂ : Fin (m+1)) (p : ↥(zeroComplement (realification Z)))
    (hw : (zCoord i p) k₁ ≠ 0) :
    ((tautQuotientCore Z).coordChange ((tautQuotientCore Z).indexAt p) (i, k₁) p).comp
      ((gaugeBwd f p).comp ((bundleComap (tautQuotientCore Z') (punctHomeo Z Z' f)).coordChange
        (i', k₂) ((bundleComap (tautQuotientCore Z') (punctHomeo Z Z' f)).indexAt p) p))
    = (quoCLM k₁ (zCoord i p)).comp
      (((Z.coordChange (Z.indexAt ((p : (realification Z).TotalSpace).1)) i
            ((p : (realification Z).TotalSpace).1)).comp
        ((f.symm.clm ((p : (realification Z).TotalSpace).1)).comp
          (Z'.coordChange i' (Z'.indexAt (phiBase f p)) (phiBase f p)))).comp
        (fillCLM k₂)) := by
  have hQ : (tautQuotientCore Z).coordChange ((tautQuotientCore Z).indexAt p) (i, k₁) p
      = (quoCLM k₁ (zCoord i p)).comp
        ((Z.coordChange (Z.indexAt ((p : (realification Z).TotalSpace).1)) i
            ((p : (realification Z).TotalSpace).1)).comp (fillCLM (tqCoord Z p))) := by
    rw [tautQuotientCore_indexAt]
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply, fillCLM_apply, quoCLM_apply]
    rw [tautQuotientCore_coordChange]
    rfl
  have hP : (bundleComap (tautQuotientCore Z') (punctHomeo Z Z' f)).coordChange
        (i', k₂) ((bundleComap (tautQuotientCore Z') (punctHomeo Z Z' f)).indexAt p) p
      = (quoCLM (tqCoord Z' (punctHomeo Z Z' f p))
          ((Z'.localTriv (Z'.indexAt (phiBase f p)) ((punctHomeo Z Z' f p :
            ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace)).2)).comp
        ((Z'.coordChange i' (Z'.indexAt (phiBase f p)) (phiBase f p)).comp
          (fillCLM k₂)) := by
    rw [bundleComap_coordChange, bundleComap_indexAt, tautQuotientCore_indexAt]
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply, fillCLM_apply, quoCLM_apply]
    rw [tautQuotientCore_coordChange]
    simp only [phiBase]
    rfl
  have hwm : (fibre p).ofLp (tqCoord Z p) ≠ 0 := tqCoord_spec' Z p
  have hwj : ((Z'.localTriv (Z'.indexAt (phiBase f p)) ((punctHomeo Z Z' f p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace)).2).ofLp
      (tqCoord Z' (punctHomeo Z Z' f p)) ≠ 0 :=
    show ((Z'.localTriv (Z'.indexAt (phiBase f p)) ((punctHomeo Z Z' f p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace)).2).ofLp
        (tqCoord Z' (punctHomeo Z Z' f p)) ≠ 0 from
      tqCoord_spec Z' (punctHomeo Z Z' f p)
  have hA₁ : f.symm.clm ((p : (realification Z).TotalSpace).1)
      ((Z'.localTriv (Z'.indexAt (phiBase f p)) ((punctHomeo Z Z' f p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace)).2)
      = fibre p := by
    rw [localTriv_indexAt_phi f p, BundleIso.clm_apply, BundleIso.clm_apply]
    exact f.left_inv _ _
  have hA₂ : (Z.coordChange (Z.indexAt ((p : (realification Z).TotalSpace).1)) i
      ((p : (realification Z).TotalSpace).1)) (fibre p) = zCoord i p := by
    simp only [zCoord, VectorBundleCore.localTriv_apply]
    rfl
  rw [hQ, hP, gaugeBwd]
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, fillCLM_apply, quoCLM_apply]
  rw [← quoFun_transport (tqCoord Z' (punctHomeo Z Z' f p)) (tqCoord Z p)
      (f.symm.clm ((p : (realification Z).TotalSpace).1))
      ((Z'.localTriv (Z'.indexAt (phiBase f p)) ((punctHomeo Z Z' f p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace)).2) (fibre p)
      ((Z'.coordChange i' (Z'.indexAt (phiBase f p)) (phiBase f p)) (fillFun k₂ z))
      hwj hwm hA₁,
    ← quoFun_transport (tqCoord Z p) k₁
      (Z.coordChange (Z.indexAt ((p : (realification Z).TotalSpace).1)) i
        ((p : (realification Z).TotalSpace).1))
      (fibre p) (zCoord i p)
      (f.symm.clm ((p : (realification Z).TotalSpace).1)
        ((Z'.coordChange i' (Z'.indexAt (phiBase f p)) (phiBase f p)) (fillFun k₂ z)))
      hwm hw hA₂]


/-! ## The isomorphism of tautological quotients -/

theorem tautQuotientCore_iso {m : ℕ} {B : Type} [TopologicalSpace B] {ι ι' : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι')
    (e : Work.Thom.BundleIso Z Z') :
    Nonempty (Work.Thom.BundleIso (Work.Thom.tautQuotientCore Z)
      (Work.Thom.bundleComap (Work.Thom.tautQuotientCore Z')
        (Work.Thom.punctHomeo Z Z' e : C(↥(Work.Thom.zeroComplement (Work.Thom.realification Z)),
          ↥(Work.Thom.zeroComplement (Work.Thom.realification Z')))))) := by
  refine ⟨{
    hom := fun p => (gaugeFwd e p).toLinearMap
    inv := fun p => (gaugeBwd e p).toLinearMap
    left_inv := fun p x => gaugeBwd_gaugeFwd e p x
    right_inv := fun p y => gaugeFwd_gaugeBwd e p y
    continuous_hom := ?_
    continuous_inv := ?_ }⟩
  · refine continuous_totalSpaceMap_clm (tautQuotientCore Z)
      (bundleComap (tautQuotientCore Z')
        (punctHomeo Z Z' e : C(↥(zeroComplement (realification Z)),
          ↥(zeroComplement (realification Z')))))
      (ContinuousMap.id _) (gaugeFwd e) ?_
    rintro ⟨i, k₁⟩ ⟨i', k₂⟩
    set s : Set ↥(zeroComplement (realification Z)) := (tautQuotientCore Z).baseSet (i, k₁) ∩
      (bundleComap (tautQuotientCore Z') (punctHomeo Z Z' e : C(↥(zeroComplement (realification Z)),
        ↥(zeroComplement (realification Z'))))).baseSet (i', k₂) with hs
    have hm : ∀ p ∈ s, (((p : (realification Z).TotalSpace).1) ∈ Z.baseSet i) ∧
        (((p : (realification Z).TotalSpace).1) ∈ Z'.baseSet i') ∧
        (phiCoord e i' p) k₂ ≠ 0 := fun p hp => mem_s_fwd e (hs ▸ hp)
    have hMg : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        (Z'.coordChange (Z'.indexAt ((p : (realification Z).TotalSpace).1)) i'
          ((p : (realification Z).TotalSpace).1)).comp
        ((e.clm ((p : (realification Z).TotalSpace).1)).comp
          (Z.coordChange i (Z.indexAt ((p : (realification Z).TotalSpace).1))
            ((p : (realification Z).TotalSpace).1)))) s := by
      refine (continuousOn_chartExpressionCLM Z Z' e i i').comp ?_ ?_
      · exact ((realification Z).continuous_proj.comp continuous_subtype_val).continuousOn
      · intro p hp
        exact ⟨(hm p hp).1, (hm p hp).2.1⟩
    have hMg' : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        (Z'.coordChange (Z'.indexAt (phiBase e p)) i' (phiBase e p)).comp
        ((e.clm ((p : (realification Z).TotalSpace).1)).comp
          (Z.coordChange i (Z.indexAt ((p : (realification Z).TotalSpace).1))
            ((p : (realification Z).TotalSpace).1)))) s := by
      refine hMg.congr (fun p hp => ?_)
      rw [show (Z'.coordChange (Z'.indexAt (phiBase e p)) i' (phiBase e p)) =
          (Z'.coordChange (Z'.indexAt ((p : (realification Z).TotalSpace).1)) i'
            ((p : (realification Z).TotalSpace).1)) from
        congrArg (fun b => Z'.coordChange (Z'.indexAt b) i' b)
          (show phiBase e p = ((p : (realification Z).TotalSpace).1) from by
            rw [phiBase]
            exact punctHomeo_proj Z Z' e p)]
    have hwg : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        phiCoord e i' p) s := by
      have hR : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
          ((realification Z').localTriv i'
            ((punctHomeo Z Z' e p : ↥(zeroComplement (realification Z'))) :
              (realification Z').TotalSpace)).2)
          {p | ((punctHomeo Z Z' e p : ↥(zeroComplement (realification Z'))) :
              (realification Z').TotalSpace) ∈ ((realification Z').localTriv i').source} :=
        continuousOn_localTriv_snd_punctHomeo Z Z' e i'
      have hsub : s ⊆ {p | ((punctHomeo Z Z' e p : ↥(zeroComplement (realification Z'))) :
            (realification Z').TotalSpace) ∈ ((realification Z').localTriv i').source} := by
        intro p hp
        change ((punctHomeo Z Z' e p : ↥(zeroComplement (realification Z'))) :
          (realification Z').TotalSpace) ∈ ((realification Z').localTriv i').source
        rw [VectorBundleCore.mem_localTriv_source, realification_baseSet]
        rw [punctHomeo_proj Z Z' e p]
        exact (hm p hp).2.1
      refine (hR.mono hsub).congr (fun p hp => ?_)
      exact (localTriv_snd_eq Z' i' ((punctHomeo Z Z' e p :
        ↥(zeroComplement (realification Z'))) : (realification Z').TotalSpace)).symm
    have hq : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        quoCLM k₂ (phiCoord e i' p)) s :=
      (continuousOn_quoCLM k₂).comp hwg (fun p hp => (hm p hp).2.2)
    have hfill : ContinuousOn (fun _ : ↥(zeroComplement (realification Z)) =>
        (fillCLM k₁ : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin (m+1)))) s :=
      continuousOn_const
    exact (hq.clm_comp (hMg'.clm_comp hfill)).congr
      (fun p hp => gaugeFwd_chart_comp e i i' k₁ k₂ p (hm p hp).2.2)
  · refine continuous_totalSpaceMap_clm
      (bundleComap (tautQuotientCore Z')
        (punctHomeo Z Z' e : C(↥(zeroComplement (realification Z)),
          ↥(zeroComplement (realification Z')))))
      (tautQuotientCore Z) (ContinuousMap.id _) (gaugeBwd e) ?_
    rintro ⟨i', k₂⟩ ⟨i, k₁⟩
    set s : Set ↥(zeroComplement (realification Z)) :=
      (bundleComap (tautQuotientCore Z') (punctHomeo Z Z' e : C(↥(zeroComplement (realification Z)),
        ↥(zeroComplement (realification Z'))))).baseSet (i', k₂) ∩
      (tautQuotientCore Z).baseSet (i, k₁) with hs
    have hm : ∀ p ∈ s, (((p : (realification Z).TotalSpace).1) ∈ Z.baseSet i) ∧
        (((p : (realification Z).TotalSpace).1) ∈ Z'.baseSet i') ∧
        (zCoord i p) k₁ ≠ 0 := fun p hp => mem_s_bwd e (hs ▸ hp)
    have hMg : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        (Z.coordChange (Z.indexAt ((p : (realification Z).TotalSpace).1)) i
          ((p : (realification Z).TotalSpace).1)).comp
        ((e.symm.clm ((p : (realification Z).TotalSpace).1)).comp
          (Z'.coordChange i' (Z'.indexAt ((p : (realification Z).TotalSpace).1))
            ((p : (realification Z).TotalSpace).1)))) s := by
      refine (continuousOn_chartExpressionCLM Z' Z e.symm i' i).comp ?_ ?_
      · exact ((realification Z).continuous_proj.comp continuous_subtype_val).continuousOn
      · intro p hp
        exact ⟨(hm p hp).2.1, (hm p hp).1⟩
    have hMg' : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        (Z.coordChange (Z.indexAt ((p : (realification Z).TotalSpace).1)) i
          ((p : (realification Z).TotalSpace).1)).comp
        ((e.symm.clm ((p : (realification Z).TotalSpace).1)).comp
          (Z'.coordChange i' (Z'.indexAt (phiBase e p)) (phiBase e p)))) s := by
      refine hMg.congr (fun p hp => ?_)
      rw [show (Z'.coordChange i' (Z'.indexAt (phiBase e p)) (phiBase e p)) =
          (Z'.coordChange i' (Z'.indexAt ((p : (realification Z).TotalSpace).1))
            ((p : (realification Z).TotalSpace).1)) from
        congrArg (fun b => Z'.coordChange i' (Z'.indexAt b) b)
          (show phiBase e p = ((p : (realification Z).TotalSpace).1) from by
            rw [phiBase]
            exact punctHomeo_proj Z Z' e p)]
    have hwg : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        zCoord i p) s := by
      have hR : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
          ((realification Z).localTriv i (p : (realification Z).TotalSpace)).2) s := by
        refine (continuousOn_localTriv_snd_realification Z i).comp
          continuous_subtype_val.continuousOn (fun p hp => ?_)
        rw [VectorBundleCore.mem_localTriv_source, realification_baseSet]
        exact (hm p hp).1
      refine hR.congr (fun p hp => ?_)
      exact (localTriv_snd_eq Z i (p : (realification Z).TotalSpace)).symm
    have hq : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
        quoCLM k₁ (zCoord i p)) s :=
      (continuousOn_quoCLM k₁).comp hwg (fun p hp => (hm p hp).2.2)
    have hfill : ContinuousOn (fun _ : ↥(zeroComplement (realification Z)) =>
        (fillCLM k₂ : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin (m+1)))) s :=
      continuousOn_const
    exact (hq.clm_comp (hMg'.clm_comp hfill)).congr
      (fun p hp => gaugeBwd_chart_comp e i i' k₁ k₂ p (hm p hp).2.2)

end

end Work.Thom
