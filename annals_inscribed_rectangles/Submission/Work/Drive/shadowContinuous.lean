import Mathlib
import Submission.Work.Drive.scaleSweep
import Submission.Work.Drive.haReduction

/-!
# Joint continuity of the dilation and continuity of the shadow

The transport's chart adapter (`Work.Drive.exists_even_colCount_add2_of_chart`) asks for the
*compactness* of the two bottom-face images `shadow cᵢ hcᵢ '' (Pᵢ '' unitBox 1)`.  This file supplies
the brick that produces it: the radial dilation acts *jointly* continuously on the capping space
(`continuous_scaleCapping₂`), hence so does the shadow `p ↦ scaleCapping (c / levelOf p) p`
(`continuous_shadow`), and the bottom-face image of a compact box is compact
(`isCompact_shadow_image`).

All declarations are `sorry`-free and rest on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff

noncomputable section

/-- **The dilation acts jointly continuously on the model.** -/
lemma continuous_scaleModel₂ :
    Continuous (fun q : Pos × (Set.Ioi (0 : ℝ) × LensSpace) => scaleModel q.1 q.2) := by
  refine Continuous.prodMk ?_ ?_
  · refine Continuous.subtype_mk ?_ _
    show Continuous fun q : Pos × (Set.Ioi (0 : ℝ) × LensSpace) =>
      ((q.1 : ℝ) * ((q.2).1 : ℝ))
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  · show Continuous fun q : Pos × (Set.Ioi (0 : ℝ) × LensSpace) => (scaleModel q.1 q.2).2
    simp only [scaleModel_snd]
    exact continuous_snd.comp continuous_snd

/-- **The dilation acts jointly continuously on the capping space.** -/
lemma continuous_scaleCapping₂ :
    Continuous (fun q : Pos × CappingSpace => scaleCapping q.1 q.2) := by
  have h : (fun q : Pos × CappingSpace => scaleCapping q.1 q.2)
      = fun q => Ψ (scaleModel q.1 (Φ q.2)) := by
    funext q
    rfl
  rw [h]
  exact continuous_Ψ.comp (continuous_scaleModel₂.comp
    (continuous_fst.prodMk (continuous_Φ.comp continuous_snd)))

/-- **The shadow map is continuous.** -/
lemma continuous_shadow (c : ℝ) (hc : 0 < c) : Continuous (shadow c hc) := by
  have hA : Continuous fun p : CappingSpace =>
      (⟨c / levelOf p, div_pos hc (levelOf_pos p)⟩ : Pos) :=
    Continuous.subtype_mk (continuous_const.div continuous_levelOf
      (fun p => ne_of_gt (levelOf_pos p))) (fun p => div_pos hc (levelOf_pos p))
  have h : shadow c hc
      = fun p : CappingSpace =>
          scaleCapping (⟨c / levelOf p, div_pos hc (levelOf_pos p)⟩ : Pos) p := by
    funext p
    rfl
  rw [h]
  exact continuous_scaleCapping₂.comp (hA.prodMk continuous_id)

/-- **The bottom-face image of a compact box is compact.**  This discharges the two compactness
hypotheses `hS₁K`, `hS₂K` of `Work.Drive.exists_even_colCount_add2_of_chart`. -/
theorem isCompact_shadow_image {c : ℝ} (hc : 0 < c)
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace} (hP : Continuous P) :
    IsCompact (shadow c hc '' (P '' Submission.Drive.unitBox 1)) :=
  ((isCompact_unitBox 1).image hP).image (continuous_shadow c hc)

end

end Work.Drive
