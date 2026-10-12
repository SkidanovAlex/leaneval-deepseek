import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.measurableBoxMeasure`

Measurability of the map `u ↦ |Λ(u) \ M|`, where `Λ(u) = bsBox ℓ u = ℓu + [−ℓ/2,ℓ/2]³`
is FS's sliding box and `M` is any measurable set.

## The argument

The moving box is a translate of the fixed cube: `x ∈ bsBox ℓ u ↔ x - ℓ•u ∈ acube ℓ`.
Hence `bsBox ℓ u \ M` is the section (in the `x`-coordinate) at parameter `u` of the
*fixed* measurable subset of `ℝ³ × ℝ³`

  `boxSection ℓ M = {p | p.1 - ℓ • p.2 ∈ acube ℓ ∧ p.1 ∉ M}`,

i.e. `x ∈ bsBox ℓ u \ M ↔ (x, u) ∈ boxSection ℓ M`.  The general fact that the
`u`-section volume of a measurable set is a measurable function of `u` is Mathlib's
`measurable_measure_prodMk_right` (Tonelli/Fubini for the s-finite measure `volume`
on the `x`-coordinate, see `measurable_volume_section`); composing the two gives the
statement.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Momentum

/-- The measurable subset of `ℝ³ × ℝ³` whose `u`-section (in the first coordinate) is
`bsBox ℓ u \ M`:  `(x, u) ∈ boxSection ℓ M ↔ x - ℓ • u ∈ acube ℓ ∧ x ∉ M`. -/
def boxSection (ℓ : ℝ) (M : Set (EuclideanSpace ℝ (Fin 3))) :
    Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 - ℓ • p.2 ∈ Submission.BoseGases.acube ℓ ∧ p.1 ∉ M}

/-- `boxSection ℓ M` is measurable. -/
lemma boxSection_measurable (ℓ : ℝ) {M : Set (EuclideanSpace ℝ (Fin 3))} (hM : MeasurableSet M) :
    MeasurableSet (boxSection ℓ M) := by
  have hcont : Continuous fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      p.1 - ℓ • p.2 := by fun_prop
  exact ((Submission.BoseGases.acube_measurable ℓ).preimage hcont.measurable).inter
    (hM.compl.preimage measurable_fst)

/-- The `u`-section of `boxSection ℓ M` is exactly `bsBox ℓ u \ M`. -/
lemma preimage_boxSection (ℓ : ℝ) (M : Set (EuclideanSpace ℝ (Fin 3)))
    (u : EuclideanSpace ℝ (Fin 3)) :
    (fun x : EuclideanSpace ℝ (Fin 3) => (x, u)) ⁻¹' boxSection ℓ M
      = Work.BSKinetic.bsBox ℓ u \ M := by
  ext x
  simp only [boxSection, Work.BSKinetic.bsBox, Set.mem_sdiff, Set.mem_ofPred_eq,
    Set.mem_preimage]

/-- **The section volume of a measurable set is measurable** (preimage form).  For a
measurable `P ⊆ ℝ³ × ℝ³`, the function `u ↦ |{x | (x,u) ∈ P}|` is measurable.

This is Mathlib's `measurable_measure_prodMk_right` (Tonelli applied to `volume` on the
first coordinate). -/
lemma measurable_volume_section_preimage
    {P : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))} (hP : MeasurableSet P) :
    Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        ((fun x : EuclideanSpace ℝ (Fin 3) => (x, u)) ⁻¹' P)) :=
  measurable_measure_prodMk_right
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) hP

/-- **The section volume of a measurable set is measurable** (set-builder form). -/
lemma measurable_volume_section
    {P : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))} (hP : MeasurableSet P) :
    Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) {x | (x, u) ∈ P}) := by
  have h := measurable_volume_section_preimage hP
  rw [show (fun u : EuclideanSpace ℝ (Fin 3) =>
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) {x | (x, u) ∈ P})
      = (fun u : EuclideanSpace ℝ (Fin 3) =>
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
          ((fun x : EuclideanSpace ℝ (Fin 3) => (x, u)) ⁻¹' P)) from
    funext fun _ => rfl]
  exact h

theorem measurableBoxMeasure (ℓ : ℝ) {M : Set (EuclideanSpace ℝ (Fin 3))} (hM : MeasurableSet M) :
    Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) (Work.BSKinetic.bsBox ℓ u \ M)) := by
  have hsec := measurable_volume_section_preimage (boxSection_measurable ℓ hM)
  rw [show (fun u : EuclideanSpace ℝ (Fin 3) =>
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
          (Work.BSKinetic.bsBox ℓ u \ M))
      = (fun u : EuclideanSpace ℝ (Fin 3) =>
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
          ((fun x : EuclideanSpace ℝ (Fin 3) => (x, u)) ⁻¹' boxSection ℓ M)) from
    funext fun u => by rw [preimage_boxSection]]
  exact hsec

end Work.BoseKinLoc.Momentum
