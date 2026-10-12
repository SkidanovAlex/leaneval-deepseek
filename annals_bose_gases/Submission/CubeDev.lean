import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ChallengeDeps
import Submission.Neumann
import Submission.NeumannPoincare
import Submission.PSDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real ENNReal

namespace Submission.BoseGases

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

abbrev T3 := Fin 3 → ℝ
abbrev T2 := Fin 2 → ℝ
abbrev T1 := Fin 1 → ℝ

/-- the 1D interval [0, L] -/
def CI (L : ℝ) : Set ℝ := Set.Icc (0 : ℝ) L

/-- the function-space cube `{x : Fin d → ℝ | ∀ k, x k ∈ [0,L]}` -/
def cubeF (d : ℕ) (L : ℝ) : Set (Fin d → ℝ) := {x | ∀ k, x k ∈ CI L}

lemma cubeF_eq_pi (d : ℕ) (L : ℝ) : cubeF d L = Set.univ.pi (fun _ : Fin d => CI L) := by
  ext x
  rw [Set.mem_pi]
  simp [cubeF, CI]

lemma cubeF_measurable (d : ℕ) (L : ℝ) : MeasurableSet (cubeF d L) := by
  rw [cubeF_eq_pi]
  exact MeasurableSet.pi (s := (Set.univ : Set (Fin d))) (t := fun _ : Fin d => CI L)
    Set.countable_univ (by intro i hi; exact measurableSet_Icc)

lemma restrict_cubeF_eq_pi (d : ℕ) (L : ℝ) :
    (volume : Measure (Fin d → ℝ)).restrict (cubeF d L) =
      Measure.pi (fun _ : Fin d => (volume : Measure ℝ).restrict (CI L)) := by
  rw [cubeF_eq_pi]
  change (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin d => CI L)) = Measure.pi (fun _ : Fin d => (volume : Measure ℝ).restrict (CI L))
  rw [Measure.restrict_pi_pi]

lemma volume_cubeF (d : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (volume : Measure (Fin d → ℝ)) (cubeF d L) = ENNReal.ofReal (L ^ d) := by
  rw [← Measure.restrict_apply_univ, restrict_cubeF_eq_pi, Measure.pi_univ]
  simp [CI, Real.volume_Icc, ENNReal.ofReal_pow hL, Finset.prod_const, Fintype.card_fin]

lemma peel3_mp (L : ℝ) : MeasurePreserving
    (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2))
    ((volume : Measure (T3)).restrict (cubeF 3 L))
    (((volume : Measure ℝ).restrict (CI L)).prod ((volume : Measure (T2)).restrict (cubeF 2 L))) := by
  rw [restrict_cubeF_eq_pi 3 L, restrict_cubeF_eq_pi 2 L]
  have h := measurePreserving_piFinSuccAbove (μ := fun _ : Fin 3 => (volume : Measure ℝ).restrict (CI L)) 2
  simpa using h

lemma peel2_mp (L : ℝ) : MeasurePreserving
    (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 1))
    ((volume : Measure (T2)).restrict (cubeF 2 L))
    (((volume : Measure ℝ).restrict (CI L)).prod ((volume : Measure (T1)).restrict (cubeF 1 L))) := by
  rw [restrict_cubeF_eq_pi 2 L, restrict_cubeF_eq_pi 1 L]
  have h := measurePreserving_piFinSuccAbove (μ := fun _ : Fin 2 => (volume : Measure ℝ).restrict (CI L)) 1
  simpa using h

lemma peel1_mp (L : ℝ) : MeasurePreserving
    (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 1 => ℝ) 0))
    ((volume : Measure (T1)).restrict (cubeF 1 L))
    (((volume : Measure ℝ).restrict (CI L)).prod ((volume : Measure (Fin 0 → ℝ)).restrict (cubeF 0 L))) := by
  rw [restrict_cubeF_eq_pi 1 L, restrict_cubeF_eq_pi 0 L]
  have h := measurePreserving_piFinSuccAbove (μ := fun _ : Fin 1 => (volume : Measure ℝ).restrict (CI L)) 0
  simpa using h

end Submission.BoseGases
