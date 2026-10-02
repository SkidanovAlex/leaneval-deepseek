import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.reflOph_mem_contDiffGroupoid
import Submission.Work.ThomBordism.CofAtlas.det_reflLin

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The corrected chart structure on the coframed level set

Vocabulary and first structural facts for the proof of
`Work.ThomBordism.levelSet_positiveAtlas_of_coframing`: the charts `newChart D x` are in the
maximal atlas of the `Lvl` chart structure, they form a charted space with the same boundary as the
`Lvl` one, and the associated extended charts are the `Lvl` extended charts composed with the
reflection.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-- The reflection used at `x`, as a continuous linear map of the model space. -/
noncomputable def reflectLin (D : Cof k n M) (x : D.S.Pre) :
    EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9) :=
  if D.flipBool x then (reflE : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9))
  else 1

theorem reflectLin_of_flip (D : Cof k n M) (x : D.S.Pre) (h : D.flipBool x = true) :
    reflectLin D x = (reflE : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9)) := by
  rw [reflectLin, h]; rfl

theorem reflectLin_of_not_flip (D : Cof k n M) (x : D.S.Pre) (h : D.flipBool x = false) :
    reflectLin D x = 1 := by
  rw [reflectLin, h]; rfl

theorem reflectMap_of_flip (D : Cof k n M) (x : D.S.Pre) (h : D.flipBool x = true) :
    D.reflectMap x = reflOph := by
  rw [Cof.reflectMap, h]; rfl

theorem reflectMap_of_not_flip (D : Cof k n M) (x : D.S.Pre) (h : D.flipBool x = false) :
    D.reflectMap x = OpenPartialHomeomorph.refl (EuclideanHalfSpace 9) := by
  rw [Cof.reflectMap, h]; rfl

theorem reflectLin_coord_zero (D : Cof k n M) (x : D.S.Pre) (v : EuclideanSpace ℝ (Fin 9)) :
    (reflectLin D x v).ofLp 0 = v.ofLp 0 := by
  by_cases h : D.flipBool x
  · rw [reflectLin_of_flip D x h,
      show ((reflE : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9)) :
        EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 9)) v = reflLin v from rfl]
    exact reflLin_apply_zero v
  · rw [reflectLin_of_not_flip D x (Bool.eq_false_iff.mpr h)]; rfl

theorem reflectLin_nonneg (D : Cof k n M) (x : D.S.Pre) {v : EuclideanSpace ℝ (Fin 9)}
    (hv : 0 ≤ v.ofLp 0) : 0 ≤ (reflectLin D x v).ofLp 0 := by
  rw [reflectLin_coord_zero]; exact hv

theorem reflectMap_val (D : Cof k n M) (x : D.S.Pre) (y : EuclideanHalfSpace 9) :
    (D.reflectMap x y).1 = reflectLin D x y.1 := by
  by_cases h : D.flipBool x
  · rw [reflectMap_of_flip D x h, reflectLin_of_flip D x h, reflOph_toFun_val,
      show ((reflE : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9)) :
        EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 9)) y.1 = reflLin y.1 from rfl]
  · rw [reflectMap_of_not_flip D x (Bool.eq_false_iff.mpr h),
      reflectLin_of_not_flip D x (Bool.eq_false_iff.mpr h)]
    rfl

theorem reflectMap_apply (D : Cof k n M) (x : D.S.Pre) (y : EuclideanHalfSpace 9) :
    D.reflectMap x y = ⟨reflectLin D x y.1, reflectLin_nonneg D x y.2⟩ := by
  refine Subtype.ext ?_
  exact reflectMap_val D x y

theorem reflectMap_coord (D : Cof k n M) (x : D.S.Pre) (y : EuclideanHalfSpace 9) :
    (𝓡∂ 9) (D.reflectMap x y) = reflectLin D x ((𝓡∂ 9) y) := by
  rw [reflectMap_apply]; rfl

theorem reflectMap_symm_apply (D : Cof k n M) (x : D.S.Pre) (y : EuclideanHalfSpace 9) :
    (D.reflectMap x).symm y = D.reflectMap x y := by
  by_cases h : D.flipBool x
  · rw [reflectMap_of_flip D x h]; rfl
  · rw [reflectMap_of_not_flip D x (Bool.eq_false_iff.mpr h)]; rfl

theorem reflectMap_source (D : Cof k n M) (x : D.S.Pre) : (D.reflectMap x).source = univ := by
  by_cases h : D.flipBool x
  · rw [reflectMap_of_flip D x h]; exact reflOph_source
  · rw [reflectMap_of_not_flip D x (Bool.eq_false_iff.mpr h)]; simp

theorem reflectMap_reflectMap (D : Cof k n M) (x : D.S.Pre) (y : EuclideanHalfSpace 9) :
    D.reflectMap x (D.reflectMap x y) = y := by
  refine Subtype.ext ?_
  rw [reflectMap_val, reflectMap_val]
  by_cases h : D.flipBool x
  · rw [reflectLin_of_flip D x h,
      show ((reflE : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9)) :
        EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 9)) y.1 = reflLin y.1 from rfl,
      show ((reflE : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9)) :
        EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 9)) (reflLin y.1)
          = reflLin (reflLin y.1) from rfl]
    exact reflLin.apply_symm_apply y.1
  · rw [reflectLin_of_not_flip D x (Bool.eq_false_iff.mpr h)]; rfl

/-- The determinant of the reflection used at `x` is its sign.  (The hypothesis `hne` is automatic
for the `Cof` data; it is recorded here to keep the statement purely algebraic.) -/
theorem reflectLin_det (D : Cof k n M) (x : D.S.Pre) (hne : D.flipSign x ≠ 0) :
    LinearMap.det (reflectLin D x).toLinearMap = (D.flipSign x : ℝ) := by
  by_cases h : D.flipBool x
  · rw [reflectLin_of_flip D x h]
    have hflip : D.flipSign x = -1 := of_decide_eq_true h
    rw [hflip]
    exact det_reflLin
  · have hf : D.flipSign x = 1 := by
      cases hf : D.flipSign x with
      | zero => exact absurd hf hne
      | pos => rfl
      | neg =>
        exact absurd (show D.flipBool x = true by rw [Cof.flipBool, hf]; rfl) h
    rw [reflectLin_of_not_flip D x (Bool.eq_false_iff.mpr h), hf]
    show LinearMap.det (1 : EuclideanSpace ℝ (Fin 9) →ₗ[ℝ] EuclideanSpace ℝ (Fin 9))
      = ((1 : SignType) : ℝ)
    simp

/-! ## The new chart -/

theorem newChart_eq (D : Cof k n M) (x : D.S.Pre) :
    D.newChart x = ((D.lvlChart x).trans (D.reflectMap x)).restr (D.src x) := rfl

theorem newChart_source (D : Cof k n M) (x : D.S.Pre) : (D.newChart x).source = D.src x := by
  rw [newChart_eq, OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.trans_source,
    reflectMap_source, preimage_univ, inter_univ]
  rw [(Cof.src_open D x).interior_eq]
  exact inter_eq_right.mpr (D.src_subset_chartSource x)

theorem newChart_apply (D : Cof k n M) (x z : D.S.Pre) :
    D.newChart x z = D.reflectMap x (D.lvlChart x z) := by
  rw [newChart_eq]
  change ((D.lvlChart x).trans (D.reflectMap x)) z = _
  rw [OpenPartialHomeomorph.trans_apply]

theorem newChart_symm_apply (D : Cof k n M) (x : D.S.Pre) (y : EuclideanHalfSpace 9) :
    (D.newChart x).symm y = (D.lvlChart x).symm (D.reflectMap x y) := by
  rw [newChart_eq]
  change (((D.lvlChart x).trans (D.reflectMap x)).symm) y = _
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  change (D.lvlChart x).symm ((D.reflectMap x).symm y) = _
  rw [reflectMap_symm_apply]

/-! ## The corrected charted space -/

/-- The charted space structure on the level set given by the corrected charts. -/
@[instance_reducible]
noncomputable def newChartedSpace (D : Cof k n M) :
    ChartedSpace (EuclideanHalfSpace 9) D.S.Pre where
  atlas := D.newAtlas
  chartAt := D.newChart
  mem_chart_source x := by
    rw [newChart_source]
    exact Cof.mem_src_self D x
  chart_mem_atlas x := ⟨x, rfl⟩

theorem newChartedSpace_chartAt (D : Cof k n M) :
    @chartAt (EuclideanHalfSpace 9) _ D.S.Pre _ (newChartedSpace D) = D.newChart := rfl

theorem newChartedSpace_atlas (D : Cof k n M) :
    @atlas (EuclideanHalfSpace 9) _ D.S.Pre _ (newChartedSpace D) = D.newAtlas := rfl

end

end Work.ThomBordism.CofAtlas
