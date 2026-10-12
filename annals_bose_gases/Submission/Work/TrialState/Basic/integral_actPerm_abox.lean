import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.TrialState.Basic.measurePreserving_actPerm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.TrialState.Basic

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

/-- The centred box `abox N ℓ` is invariant under relabelling the particles. -/
lemma actPerm_mem_abox_iff {N : ℕ} {ℓ : ℝ} (σ : Equiv.Perm (Fin N))
    (x : Fin N → EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.actPerm N σ x ∈ Submission.BoseGases.abox N ℓ
      ↔ x ∈ Submission.BoseGases.abox N ℓ := by
  simp only [Submission.BoseGases.mem_abox_iff]
  constructor
  · intro h i
    simpa [Submission.BoseGases.actPerm] using h (σ.symm i)
  · intro h i
    simpa [Submission.BoseGases.actPerm] using h (σ i)

/-- `actPerm N σ` is a measurable embedding (it is a measurable equivalence). -/
lemma measurableEmbedding_actPerm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurableEmbedding (Submission.BoseGases.actPerm N σ) := by
  rw [actPerm_eq_piCongrLeft N σ]
  exact MeasurableEquiv.measurableEmbedding _

/-- Relabelling the particles preserves Lebesgue measure restricted to the
centred box `abox N ℓ`. -/
lemma measurePreserving_restrict_abox {N : ℕ} {ℓ : ℝ} (σ : Equiv.Perm (Fin N)) :
    MeasureTheory.MeasurePreserving (Submission.BoseGases.actPerm N σ)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin N → EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.abox N ℓ))
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin N → EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.abox N ℓ)) := by
  have hmeas : Measurable (Submission.BoseGases.actPerm N σ) :=
    (Submission.BoseGases.actPerm_continuous σ).measurable
  have hpre : (Submission.BoseGases.actPerm N σ) ⁻¹' Submission.BoseGases.abox N ℓ
      = Submission.BoseGases.abox N ℓ :=
    Set.ext (fun x => actPerm_mem_abox_iff σ x)
  refine ⟨hmeas, ?_⟩
  have h1 := MeasureTheory.Measure.restrict_map (μ := (MeasureTheory.volume :
      MeasureTheory.Measure (Fin N → EuclideanSpace ℝ (Fin 3))))
    (f := Submission.BoseGases.actPerm N σ) hmeas
    (s := Submission.BoseGases.abox N ℓ) (Submission.BoseGases.abox_measurable N ℓ)
  rw [MeasureTheory.MeasurePreserving.map_eq (measurePreserving_actPerm N σ), hpre] at h1
  exact h1.symm

theorem integral_actPerm_abox {N : ℕ} {ℓ : ℝ} (σ : Equiv.Perm (Fin N))
    (g : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ) :
    (∫ x in Submission.BoseGases.abox N ℓ, g (Submission.BoseGases.actPerm N σ x))
      = ∫ x in Submission.BoseGases.abox N ℓ, g x := by
  exact MeasureTheory.MeasurePreserving.integral_comp
    (measurePreserving_restrict_abox (N := N) (ℓ := ℓ) σ)
    (measurableEmbedding_actPerm σ) g

end Work.TrialState.Basic
