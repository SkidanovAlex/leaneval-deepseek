/-
Copyright: work module for the Elgindi finite-time singularity project.

# Measurability of a shifted slice

Companion of `aemeasurable_shift_pair` in the same directory: there the profile factor is
evaluated at the shifted point `(zShift z p₁, thShift θ p₂)` of the pair `(base point, shift)`, so
the measure lives on `((ℝ × ℝ) × (ℝ × ℝ))`.  Here the shift `p` is *fixed* and only the base
point `q` varies, so the statement is about the map

  `q ↦ G (zShift q.1 p.1) (thShift q.2 p.2)`

on `ℝ × ℝ`, against the product measure `(volume.restrict Iz).prod (volume.restrict Iθ)`.

As in the pair case the only content is the profile factor: `G` is assumed `ContinuousOn Quad`
and the shift of a base point in `Quad` stays in `Quad`, whence the composite is continuous on
`Quad`, a conull set for the product measure (its complement is contained in the union of the two
coordinate hyperplanes `z = 0` and `θ ∉ (0, π/2)`, which are null).  Passing through the
indicator of `Quad` and `ENNReal.ofReal` gives the result.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_pair

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

open Work.FTS.StrongEps
open Work.Spaces

/-! ## The two null sets of the boundary -/

/-- `z = 0` is null for `volume.restrict Iz` with `Iz = [0, ∞)`. -/
private lemma measure_Iz_compl_Ioi_slice :
    (volume.restrict Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioi.compl]
  refine measure_mono_null ?_ (measure_singleton (0 : ℝ))
  intro x hx
  simp only [Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff, Set.mem_Ioi,
    Set.mem_singleton_iff] at hx ⊢
  exact le_antisymm (not_lt.mp hx.1) hx.2

/-- `θ = 0` and `θ = π/2` are null for `volume.restrict Iθ` with `Iθ = [0, π/2]`. -/
private lemma measure_Iθ_compl_Ioo_slice :
    (volume.restrict Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  have h0 : (volume : Measure ℝ) ({0} ∪ {π / 2}) = 0 :=
    measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
  refine measure_mono_null ?_ h0
  intro x hx
  simp only [Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
    Set.mem_union, Set.mem_singleton_iff] at hx ⊢
  obtain ⟨hxn, hxI⟩ := hx
  rcases lt_or_ge (0 : ℝ) x with h | h
  · rcases lt_or_ge x (π / 2) with h2 | h2
    · exact absurd ⟨h, h2⟩ hxn
    · exact Or.inr (le_antisymm hxI.2 h2)
  · exact Or.inl (le_antisymm h hxI.1)

/-- The complement of the quadrant is null for `(volume.restrict Iz).prod (volume.restrict Iθ)`:
it is contained in the union of the two coordinate hyperplanes. -/
private lemma measure_quad_compl_slice :
    (volume.restrict Iz).prod (volume.restrict Iθ) Quadᶜ = 0 := by
  have hsub : Quadᶜ ⊆ (Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ := by
    intro x hx
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and] at hx ⊢
    tauto
  have h1 : (volume.restrict Iz).prod (volume.restrict Iθ)
      ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
        (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) = 0 := by
    rw [measure_union_null_iff]
    constructor
    · rw [Measure.prod_prod, measure_Iz_compl_Ioi_slice, zero_mul]
    · rw [Measure.prod_prod, measure_Iθ_compl_Ioo_slice, mul_zero]
  exact measure_mono_null hsub h1

/-! ## Continuity of the shift along a fixed parameter -/

/-- On the quadrant, `cos` does not vanish, so `tan` is continuous there. -/
private lemma cos_ne_zero_of_mem_quad_slice {q : ℝ × ℝ} (hq : q ∈ Quad) :
    Real.cos q.2 ≠ 0 := by
  have h2 : q.2 ∈ Set.Ioo 0 (π / 2) := hq.2
  exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h2.1], h2.2⟩).ne'

/-- For a fixed `p₂`, the `θ`-shift `q ↦ thShift q.2 p₂` is continuous on the quadrant
(the monotone `tan` factor is harmless there because `cos ≠ 0`). -/
private lemma continuousOn_thShift_slice (p₂ : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => thShift q.2 p₂) Quad := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => Real.tan q.2 * Real.exp (-p₂)) Quad :=
    (Real.continuousOn_tan.comp continuousOn_snd
      (fun q hq => cos_ne_zero_of_mem_quad_slice hq)).mul continuousOn_const
  have h2 := Real.continuous_arctan.comp_continuousOn h1
  simpa only [thShift, Function.comp_def] using h2

/-- For a fixed parameter `p`, the shifted point `q ↦ (zShift q.1 p.1, thShift q.2 p.2)` is
continuous on the quadrant. -/
private lemma continuousOn_shift_slice_of_quad (p : ℝ × ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => (zShift q.1 p.1, thShift q.2 p.2)) Quad := by
  refine ContinuousOn.prodMk ?_ (continuousOn_thShift_slice p.2)
  simp only [zShift]
  exact continuousOn_fst.mul continuousOn_const

/-- The shifted point of a base point of the quadrant lies again in the quadrant. -/
private lemma shift_mem_Quad_slice (p : ℝ × ℝ) {q : ℝ × ℝ} (hq : q ∈ Quad) :
    (zShift q.1 p.1, thShift q.2 p.2) ∈ Quad :=
  ⟨zShift_pos hq.1, thShift_mem hq.2⟩

/-! ## The target -/

theorem aemeasurable_shift_slice {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (fun q : ℝ × ℝ => G q.1 q.2) Work.FTS.StrongEps.Quad) (p : ℝ × ℝ) :
    AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (G (Work.FTS.StrongEps.zShift q.1 p.1)
        (Work.FTS.StrongEps.thShift q.2 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  classical
  have hSmeas : MeasurableSet Quad := (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hnull : (volume.restrict Iz).prod (volume.restrict Iθ) Quadᶜ = 0 :=
    measure_quad_compl_slice
  -- On the quadrant the composite is continuous.
  have hcont : ContinuousOn (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2)) Quad :=
    hG.comp (continuousOn_shift_slice_of_quad p) (fun q hq => shift_mem_Quad_slice p hq)
  have hA : AEMeasurable (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2))
      (Measure.restrict ((volume.restrict Iz).prod (volume.restrict Iθ)) Quad) :=
    hcont.aemeasurable hSmeas
  -- Multiply by the indicator of the quadrant and remove it again using conullity.
  have hind : AEMeasurable (Quad.indicator
      (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2)))
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  have hcongr : (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2))
      =ᵐ[(volume.restrict Iz).prod (volume.restrict Iθ)]
      Quad.indicator (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2)) := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
    simp only [Set.mem_compl_iff, not_not] at hq
    exact (Set.indicator_of_mem hq
      (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2))).symm
  have hGae : AEMeasurable (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2))
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    hind.congr hcongr.symm
  exact ENNReal.measurable_ofReal.comp_aemeasurable hGae

end Work.FTS.StrongEps.HkSqAux
