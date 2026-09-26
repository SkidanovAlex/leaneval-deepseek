import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Branch

/-!
# Local-arcness passes to open subspaces

`isLocallyArcIsOpen`: an open subspace of a locally-arc space is locally arc.  The auxiliary
construction `homeomorphIoo` realises `ℝ ≃ₜ ↥(Ioo (-ε) ε)`.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function
open scoped Topology

noncomputable section

/-- Rescaling `(-π/2, π/2)` to `(-ε, ε)`. -/
private def scale1 (ε : ℝ) (t : ℝ) : ℝ := t * (2 * ε / Real.pi)

/-- The inverse rescaling. -/
private def scale2 (ε : ℝ) (y : ℝ) : ℝ := y * (Real.pi / (2 * ε))

private lemma scale1_mem {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (ht : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) : scale1 ε t ∈ Set.Ioo (-ε) ε := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hc : 0 < 2 * ε / Real.pi := by positivity
  refine ⟨?_, ?_⟩
  · have h := mul_lt_mul_of_pos_right ht.1 hc
    have he : (-(Real.pi / 2)) * (2 * ε / Real.pi) = -ε := by field_simp
    simp only [scale1]; linarith [h, he]
  · have h := mul_lt_mul_of_pos_right ht.2 hc
    have he : (Real.pi / 2) * (2 * ε / Real.pi) = ε := by field_simp
    simp only [scale1]; linarith [h, he]

private lemma scale2_mem {ε : ℝ} (hε : 0 < ε) {y : ℝ}
    (hy : y ∈ Set.Ioo (-ε) ε) : scale2 ε y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hc : 0 < Real.pi / (2 * ε) := by positivity
  refine ⟨?_, ?_⟩
  · have h := mul_lt_mul_of_pos_right hy.1 hc
    have he : (-ε) * (Real.pi / (2 * ε)) = -(Real.pi / 2) := by field_simp
    simp only [scale2]; linarith [h, he]
  · have h := mul_lt_mul_of_pos_right hy.2 hc
    have he : ε * (Real.pi / (2 * ε)) = Real.pi / 2 := by field_simp
    simp only [scale2]; linarith [h, he]

private lemma scale2_scale1 {ε : ℝ} (hε : 0 < ε) (t : ℝ) : scale2 ε (scale1 ε t) = t := by
  simp only [scale1, scale2]; field_simp

private lemma scale1_scale2 {ε : ℝ} (hε : 0 < ε) (y : ℝ) : scale1 ε (scale2 ε y) = y := by
  simp only [scale1, scale2]; field_simp

/-- `ℝ ≃ₜ ↥(Ioo (-ε) ε)` (via `arctan` and a rescaling). -/
def homeomorphIoo (ε : ℝ) (hε : 0 < ε) : ℝ ≃ₜ ↥(Set.Ioo (-ε) ε) :=
  (Real.tanOrderIso.symm.toHomeomorph).trans
    { toFun := fun t => ⟨scale1 ε t.1, scale1_mem hε t.2⟩
      invFun := fun y => ⟨scale2 ε y.1, scale2_mem hε y.2⟩
      left_inv := fun t => Subtype.ext (scale2_scale1 hε t.1)
      right_inv := fun y => Subtype.ext (scale1_scale2 hε y.1)
      continuous_toFun := Continuous.subtype_mk
        (by simp only [scale1]; fun_prop) (fun t => scale1_mem hε t.2)
      continuous_invFun := Continuous.subtype_mk
        (by simp only [scale2]; fun_prop) (fun y => scale2_mem hε y.2) }

/-- `homeomorphIoo` fixes `0`. -/
@[simp] lemma homeomorphIoo_zero (ε : ℝ) (hε : 0 < ε) :
    (homeomorphIoo ε hε) 0 = ⟨0, ⟨by linarith, by linarith⟩⟩ := by
  apply Subtype.ext
  show scale1 ε ((Real.tanOrderIso.symm (0:ℝ) : ℝ)) = 0
  rw [show ((Real.tanOrderIso.symm (0:ℝ) : ℝ)) = 0 from by
    rw [show Real.tanOrderIso.symm (0:ℝ) = ⟨Real.arctan 0, Real.arctan_mem_Ioo 0⟩ from rfl]
    simp]
  simp [scale1]

/-- A point in the image of an interval under a chart lies in the chart. -/
private lemma mem_chart_of_mem_image {X : Type*} [TopologicalSpace X] {x₀ : X}
    (c : ArcChart X x₀) {ε : ℝ} {z : X} (hz : z ∈ c.map '' Set.Ioo (-ε) ε) : z ∈ c.V := by
  obtain ⟨t, -, hte⟩ := hz
  rw [← hte]
  exact c.map_mem t

/-- The coordinate of a point of the image of an interval lies in that interval. -/
private lemma coord_mem_of_mem_image {X : Type*} [TopologicalSpace X] {x₀ : X}
    (c : ArcChart X x₀) {ε : ℝ} {y : c.V} (hy : (y : X) ∈ c.map '' Set.Ioo (-ε) ε) :
    c.coord y ∈ Set.Ioo (-ε) ε := by
  obtain ⟨t, ht, hte⟩ := hy
  have hy' : y = ⟨c.map t, c.map_mem t⟩ := Subtype.ext hte.symm
  rw [hy', c.coord_apply_map]
  exact ht

/-- The restriction of a chart to an interval, as a homeomorphism onto its image. -/
def restrictMapHomeomorph {X : Type*} [TopologicalSpace X] {x₀ : X} (c : ArcChart X x₀)
    (ε : ℝ) : ↥(Set.Ioo (-ε) ε) ≃ₜ ↥(c.map '' Set.Ioo (-ε) ε) where
  toFun t := ⟨c.map t.1, t.1, t.2, rfl⟩
  invFun y := ⟨c.coord ⟨y.1, mem_chart_of_mem_image c y.2⟩, coord_mem_of_mem_image c y.2⟩
  left_inv t := by
    apply Subtype.ext
    simp only [ArcChart.coord_apply_map]
  right_inv y := by
    apply Subtype.ext
    exact c.map_coord _
  continuous_toFun := Continuous.subtype_mk
    (c.continuous_map.comp continuous_subtype_val) (fun t => ⟨t.1, t.2, rfl⟩)
  continuous_invFun := Continuous.subtype_mk
    ((c.continuous_coord).comp (Continuous.subtype_mk continuous_subtype_val
      (fun y => mem_chart_of_mem_image c y.2)))
    (fun y => coord_mem_of_mem_image c y.2)

/-- The canonical homeomorphism `↥s ≃ₜ ↥{y : ↥U | (y : X) ∈ s}` for a subset `s ⊆ U`. -/
def subtypeSubtypeHomeomorph {X : Type*} [TopologicalSpace X] {U : Set X} {s : Set X}
    (hs : s ⊆ U) : ↥s ≃ₜ ↥{y : U | (y : X) ∈ s} where
  toFun z := ⟨⟨z.1, hs z.2⟩, z.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv z := rfl
  right_inv y := rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun z => hs z.2)) (fun z => z.2)
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)

/-- **Local-arcness passes to open subspaces.** -/
theorem isLocallyArcIsOpen {X : Type*} [TopologicalSpace X] (H : IsLocallyArc X)
    {U : Set X} (hU : IsOpen U) : IsLocallyArc U := by
  intro x
  obtain ⟨c⟩ := H x.1
  have hmem : (c.homeo ⁻¹' (Subtype.val ⁻¹' U)) ∈ 𝓝 (0 : ℝ) := by
    have h1 : (Subtype.val : c.V → X) ⁻¹' U ∈ 𝓝 (c.homeo 0) := by
      rw [c.homeo_zero]
      exact continuous_subtype_val.continuousAt.preimage_mem_nhds (hU.mem_nhds x.2)
    exact c.homeo.continuous.continuousAt.preimage_mem_nhds h1
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hVU : c.map '' Set.Ioo (-ε) ε ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    exact hεsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  refine ⟨{ V := {y : U | (y : X) ∈ c.map '' Set.Ioo (-ε) ε}
            isOpen_V := ?_
            mem_V := ⟨0, ⟨by linarith, by linarith⟩, c.map_zero⟩
            homeo := ?_
            homeo_zero := ?_ }⟩
  · have h1 : {y : U | (y : X) ∈ c.map '' Set.Ioo (-ε) ε} =
        Subtype.val ⁻¹' (c.map '' Set.Ioo (-ε) ε) := rfl
    rw [h1]
    exact (isOpen_chartMap_Ioo c ε).preimage continuous_subtype_val
  · exact (homeomorphIoo ε hε).trans ((restrictMapHomeomorph c ε).trans (subtypeSubtypeHomeomorph hVU))
  · apply Subtype.ext
    apply Subtype.ext
    rw [Homeomorph.trans_apply, Homeomorph.trans_apply, homeomorphIoo_zero]
    exact c.map_zero

end

end Work.Smooth.SphereJordan.LocalArc
