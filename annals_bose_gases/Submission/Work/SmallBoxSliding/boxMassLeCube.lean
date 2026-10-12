import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.flatArmSlidingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `boxMass ℓ d u ≤ (ℓd)³` — the sliding box is no larger than the small cube

The true volume of the sliding small box

    B(u) = acube ℓ ∩ ((ℓd)•u + acube (ℓd))

is at most the volume `(ℓd)³` of the *outer* cube `acube (ℓd)`, because `B(u)` is
contained in the translate `(ℓd)•u + acube (ℓd)`.  This is the elementary
`V ≤ boxVol` bookkeeping used wherever the sliding box is compared with its
nominal volume `boxVol ℓ d = (ℓd)³` (e.g. in the diluteness/volume comparisons
`boxMass ≍ boxVol` on the good set).

The proof is the volume monotonicity for the measure-theoretic form of
`boxMass` (`boxMass_eq_measureReal`), together with the exact cube volume
`acube_volume` and the translation invariance `measure_preimage_add` of
Lebesgue measure.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

open Submission.BoseGases

theorem boxMassLeCube {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.SmallBoxSliding.boxMass ℓ d u ≤ (ℓ * d) ^ 3 := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  -- `B(u)` sits inside the translate `(ℓd)•u + acube (ℓd)` of the small cube.
  have hsub : dlBox ℓ d u ⊆
      (fun y : EuclideanSpace ℝ (Fin 3) => (-((ℓ * d) • u)) + y) ⁻¹' acube (ℓ * d) := by
    intro x hx
    simp only [Set.mem_preimage]
    have h := (mem_dlBox_iff ℓ d u x).mp hx
    have hx' : (-((ℓ * d) • u)) + x = x - (ℓ * d) • u := by abel
    rw [hx']
    exact h.2
  -- the volume of that translate is the volume of the small cube, `(ℓd)³`.
  have hT : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        ((fun y : EuclideanSpace ℝ (Fin 3) => (-((ℓ * d) • u)) + y) ⁻¹' acube (ℓ * d))
      = ENNReal.ofReal ((ℓ * d) ^ 3) := by
    rw [measure_preimage_add volume (-((ℓ * d) • u)) (acube (ℓ * d)),
      acube_volume _ hℓd.le]
  calc boxMass ℓ d u = (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (dlBox ℓ d u) :=
        boxMass_eq_measureReal ℓ d u
    _ ≤ (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
          ((fun y : EuclideanSpace ℝ (Fin 3) => (-((ℓ * d) • u)) + y) ⁻¹' acube (ℓ * d)) := by
        rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def]
        exact ENNReal.toReal_mono (by rw [hT]; exact ENNReal.ofReal_ne_top) (measure_mono hsub)
    _ = (ℓ * d) ^ 3 := by
        rw [MeasureTheory.Measure.real_def, hT, ENNReal.toReal_ofReal (pow_nonneg hℓd.le 3)]

end Work.SmallBoxSliding
