import Mathlib
import Submission.Work.Gen.RealIsoGaugeDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Gen

open Work.Thom Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {m : ℕ} {ι ι' : Type}

/-- The real chart change of the realification, as a real linear map, is the restriction of
scalars of the complex chart change. -/
theorem realification_coordChange_toLinearMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i j : ι) (b : B) :
    ((realification Z).coordChange i j b).toLinearMap
      = (Z.coordChange i j b).restrictScalars ℝ := by
  apply LinearMap.ext
  intro v
  exact congrFun (realification_coordChange Z i j b) v

theorem continuous_realIsoGauge
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso (realification Z) (realification Z')) (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i') :
    Continuous (realIsoGauge Z Z' e i i' hWi hWi') := by
  apply continuous_clm_of_continuous_apply
  have hbaseZ : ∀ q : ↥W × EuclideanSpace ℂ (Fin m), (q.1 : B) ∈ (realification Z).baseSet i :=
    fun q => hWi q.1.2
  have hbaseZ' : ∀ q : ↥W × EuclideanSpace ℂ (Fin m), (q.1 : B) ∈ (realification Z').baseSet i' :=
    fun q => hWi' q.1.2
  have hG1 : Continuous fun q : ↥W × EuclideanSpace ℂ (Fin m) =>
      (⟨(q.1 : B), ((realification Z).localTriv i).symm (q.1 : B) q.2⟩ :
        (realification Z).TotalSpace) := by
    have hsymm := @Bundle.Trivialization.continuousOn_symm B (EuclideanSpace ℂ (Fin m))
      (realification Z).Fiber ‹TopologicalSpace B›
      (inferInstance : TopologicalSpace (EuclideanSpace ℂ (Fin m)))
      ((realification Z).toTopologicalSpace) (fun x => ⟨0⟩) ((realification Z).localTriv i)
    refine hsymm.comp_continuous
      (f := fun q : ↥W × EuclideanSpace ℂ (Fin m) => ((q.1 : B), q.2)) ?_ ?_
    · exact Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd
    · intro q; exact ⟨hbaseZ q, Set.mem_univ q.2⟩
  have hG : Continuous fun q : ↥W × EuclideanSpace ℂ (Fin m) =>
      e.toTotalSpace (⟨(q.1 : B), ((realification Z).localTriv i).symm (q.1 : B) q.2⟩ :
        (realification Z).TotalSpace) :=
    e.continuous_hom.comp hG1
  have hGmem : ∀ q : ↥W × EuclideanSpace ℂ (Fin m),
      e.toTotalSpace (⟨(q.1 : B), ((realification Z).localTriv i).symm (q.1 : B) q.2⟩ :
        (realification Z).TotalSpace) ∈ ((realification Z').localTriv i').source := by
    intro q
    rw [VectorBundleCore.mem_localTriv_source]
    exact hbaseZ' q
  have hH : Continuous fun q : ↥W × EuclideanSpace ℂ (Fin m) =>
      ((realification Z').localTriv i')
        (e.toTotalSpace (⟨(q.1 : B), ((realification Z).localTriv i).symm (q.1 : B) q.2⟩ :
          (realification Z).TotalSpace)) :=
    ((realification Z').localTriv i').continuousOn.comp_continuous hG hGmem
  let K : ↥W × EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin m) :=
    fun q => (((realification Z').localTriv i')
      (e.toTotalSpace (⟨(q.1 : B), ((realification Z).localTriv i).symm (q.1 : B) q.2⟩ :
        (realification Z).TotalSpace))).2
  have hK : Continuous K := hH.snd
  have hKval : ∀ q : ↥W × EuclideanSpace ℂ (Fin m), K q =
      ((realification Z').coordChange ((realification Z').indexAt (q.1 : B)) i' (q.1 : B))
        (e.hom (q.1 : B) (((realification Z).coordChange i ((realification Z).indexAt (q.1 : B))
          (q.1 : B)) q.2)) := by
    intro q
    have hbZ : (q.1 : B) ∈ ((realification Z).localTriv i).baseSet := by
      show (q.1 : B) ∈ (realification Z).baseSet i
      exact hbaseZ q
    show (((realification Z').localTriv i')
      (e.toTotalSpace (⟨(q.1 : B), ((realification Z).localTriv i).symm (q.1 : B) q.2⟩ :
        (realification Z).TotalSpace))).2 = _
    rw [VectorBundleCore.localTriv_apply]
    dsimp only
    rw [BundleIso.toTotalSpace_apply]
    dsimp only
    rw [VectorBundleCore.localTriv_symm_apply (realification Z) i hbZ]
  have hΦ : Continuous fun p : ↥W × EuclideanSpace ℝ (Fin (2 * m)) =>
      (p.1, (covE (m := m)).symm p.2) :=
    Continuous.prodMk continuous_fst ((covE (m := m)).symm.continuous.comp continuous_snd)
  have hfinal : Continuous fun p : ↥W × EuclideanSpace ℝ (Fin (2 * m)) =>
      (covE (m := m)) (K (p.1, (covE (m := m)).symm p.2)) :=
    (covE (m := m)).continuous.comp (hK.comp hΦ)
  refine hfinal.congr (fun p => ?_)
  rw [realIsoGauge_apply]
  refine congrArg (fun w => (covE (m := m)) w) ?_
  rw [hKval (p.1, (covE (m := m)).symm p.2)]

/-- **The real determinant of the gauge has the sign of `det (e.hom x)`.**  For an everywhere
negative fibrewise determinant the gauge is orientation reversing. -/
theorem det_realIsoGauge_neg
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso (realification Z) (realification Z')) (i : ι) (i' : ι') {W : Set B}
    (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i')
    (hdet : ∀ b : B, LinearMap.det (e.hom b) < 0) (x : ↥W) :
    LinearMap.det ((realIsoGauge Z Z' e i i' hWi hWi' x).toLinearMap) < 0 := by
  let Cc : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    ((realification Z).coordChange i ((realification Z).indexAt (x : B)) (x : B)).toLinearMap
  let Cc' : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    ((realification Z').coordChange ((realification Z').indexAt (x : B)) i' (x : B)).toLinearMap
  let Ex : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) := e.hom (x : B)
  let Bm : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) := Cc'.comp (Ex.comp Cc)
  have hlin : (realIsoGauge Z Z' e i i' hWi hWi' x).toLinearMap
      = (covE (m := m)).toLinearEquiv.conj Bm := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply]
    change (realIsoGauge Z Z' e i i' hWi hWi' x) v
      = (covE (m := m)) (Bm ((covE (m := m)).symm v))
    rw [realIsoGauge_apply]
    rfl
  have hdetg : LinearMap.det ((realIsoGauge Z Z' e i i' hWi hWi' x).toLinearMap)
      = LinearMap.det Bm := by
    rw [hlin]
    exact LinearMap.det_conj Bm ((covE (m := m)).toLinearEquiv)
  rw [hdetg]
  have hC : 0 < LinearMap.det Cc := by
    have h1 : Cc = (Z.coordChange i (Z.indexAt (x : B)) (x : B)).restrictScalars ℝ := by
      show ((realification Z).coordChange i ((realification Z).indexAt (x : B)) (x : B)).toLinearMap
        = _
      rw [realification_indexAt]
      exact realification_coordChange_toLinearMap Z i (Z.indexAt (x : B)) (x : B)
    rw [h1]
    refine det_restrictScalars_pos ?_
    rw [realification_baseSet] at hWi
    exact coordChange_bijective Z i (Z.indexAt (x : B)) ⟨hWi x.2, Z.mem_baseSet_at _⟩
  have hC' : 0 < LinearMap.det Cc' := by
    have h1 : Cc'
        = (Z'.coordChange (Z'.indexAt (x : B)) i' (x : B)).restrictScalars ℝ := by
      show ((realification Z').coordChange ((realification Z').indexAt (x : B)) i'
        (x : B)).toLinearMap = _
      rw [realification_indexAt]
      exact realification_coordChange_toLinearMap Z' (Z'.indexAt (x : B)) i' (x : B)
    rw [h1]
    refine det_restrictScalars_pos ?_
    rw [realification_baseSet] at hWi'
    exact coordChange_bijective Z' (Z'.indexAt (x : B)) i' ⟨Z'.mem_baseSet_at _, hWi' x.2⟩
  have hE : LinearMap.det Ex < 0 := hdet (x : B)
  have hBm : LinearMap.det Bm
      = LinearMap.det Cc' * LinearMap.det Ex * LinearMap.det Cc := by
    show LinearMap.det (Cc'.comp (Ex.comp Cc)) = _
    rw [LinearMap.det_comp, LinearMap.det_comp]
    ring
  rw [hBm]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hC' hE) hC

end

end Work.Gen
