import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.TrialState.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.TrialState.Basic

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

/-- The relabelling `x ↦ x ∘ σ` of the `N`-particle configuration space, expressed as the
measurable equivalence `MeasurableEquiv.piCongrLeft` moving the index set along `σ.symm`.
(The variance is chosen so that the *forward* map of `piCongrLeft` is `actPerm σ`.) -/
lemma actPerm_eq_piCongrLeft (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    Submission.BoseGases.actPerm N σ =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N => EuclideanSpace ℝ (Fin 3)) σ.symm) := by
  funext x i
  rw [MeasurableEquiv.coe_piCongrLeft]
  have key := Equiv.piCongrLeft_apply_apply
    (P := fun _ : Fin N => EuclideanSpace ℝ (Fin 3)) (e := σ.symm) x (σ i)
  rw [show σ.symm (σ i) = i from Equiv.symm_apply_apply σ i] at key
  simpa [Submission.BoseGases.actPerm] using key.symm

/-- Lebesgue measure on the configuration space is invariant under relabelling the particles. -/
theorem measurePreserving_actPerm (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    MeasureTheory.MeasurePreserving (Submission.BoseGases.actPerm N σ)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin N → EuclideanSpace ℝ (Fin 3)))
      MeasureTheory.volume := by
  rw [actPerm_eq_piCongrLeft]
  exact MeasureTheory.volume_measurePreserving_piCongrLeft
    (α := fun _ : Fin N => EuclideanSpace ℝ (Fin 3)) σ.symm

end Work.TrialState.Basic
