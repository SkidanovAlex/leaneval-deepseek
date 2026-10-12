import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.boxMass_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `|B(u)| ≤ (ℓd)³`

The sliding box `dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` is contained in the
translate `(ℓd)•u + acube (ℓd)` of the small cube, whose Lebesgue volume is `(ℓd)³`
(`acube_volume` + translation invariance `measure_preimage_add`).  Since
`boxMass ℓ d u` is the (real) volume of `dlBox ℓ d u`, the bound follows by monotonicity
of `ENNReal.toReal`.

Only `0 < ℓ * d` is needed: for `ℓ, d` not both positive it is still true that
`dlBox ℓ d u` sits inside the translate of `acube (ℓ * d)` of volume `(ℓd)³`.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped ENNReal

open Submission.BoseGases

theorem boxMassLeDlCubeB1 {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) (h : 0 < ℓ * d) :
    Work.SmallBoxSliding.boxMass ℓ d u ≤ (ℓ * d) ^ 3 := by
  -- `dlBox ℓ d u ⊆ ((ℓd)•u + acube (ℓd))`, i.e. the preimage of `acube (ℓd)` under
  -- the translation `x ↦ -(ℓd)•u + x`.
  have hsub : dlBox ℓ d u ⊆
      (fun x : EuclideanSpace ℝ (Fin 3) => (-((ℓ * d) • u)) + x) ⁻¹'
        acube (ℓ * d) := by
    intro x hx
    have hx2 : x - (ℓ * d) • u ∈ acube (ℓ * d) :=
      (mem_dlBox_iff ℓ d u x).mp hx |>.2
    have heq : (-((ℓ * d) • u)) + x = x - (ℓ * d) • u := by
      rw [sub_eq_add_neg, add_comm]
    simpa [heq] using hx2
  have hmono :
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) (dlBox ℓ d u)
        ≤ (volume : Measure (EuclideanSpace ℝ (Fin 3)))
            ((fun x : EuclideanSpace ℝ (Fin 3) => (-((ℓ * d) • u)) + x) ⁻¹'
              acube (ℓ * d)) :=
    measure_mono hsub
  -- the translate has the volume of `acube (ℓd)`, which is `(ℓd)³` (as an `ℝ≥0∞`).
  have htrans : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        ((fun x : EuclideanSpace ℝ (Fin 3) => (-((ℓ * d) • u)) + x) ⁻¹'
          acube (ℓ * d))
      = ENNReal.ofReal ((ℓ * d) ^ 3) := by
    rw [measure_preimage_add volume (-((ℓ * d) • u)) (acube (ℓ * d)),
      acube_volume (ℓ * d) h.le]
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
  calc ((volume : Measure (EuclideanSpace ℝ (Fin 3))) (dlBox ℓ d u)).toReal
      ≤ (ENNReal.ofReal ((ℓ * d) ^ 3)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne (le_trans hmono htrans.le)
    _ = (ℓ * d) ^ 3 := ENNReal.toReal_ofReal (pow_nonneg h.le 3)

end Work.BoseFixB1S
