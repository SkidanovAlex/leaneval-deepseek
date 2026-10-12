import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.RadialIntegral
import Submission.Work.BoseRowsFS.LatRiemann.Geom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.ballInvSq`

The Coulomb-type ball integral in `ℝ³`:

    `∫_{‖x‖ < R} A/‖x‖² dx ≤ 4π A R`   (`A ≥ 0`, `R ≥ 0`),

with `x ↦ A/‖x‖²` integrable on the ball.  The value is *exact*:
`∫_{‖x‖<R} A/‖x‖² dx = 4π A R` — the singularity at the origin is integrable in
dimension three.

The proof is polar coordinates on `ℝ³` (`Submission.BoseGases.integral_radial_ball_r3`
and `Submission.BoseGases.integrable_radial_ball_r3`, Mathlib's
`MeasureTheory.integral_fun_norm_addHaar` at dimension three):

    `∫_{‖x‖ < R} A/‖x‖² dx = 4π ∫_{r ∈ (0,R)} r² · (A/r²) dr = 4π ∫_{r ∈ (0,R)} A dr = 4π A R`.

The middle identity uses `r ≠ 0` on `(0,R)`.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseRowsFS.LatRiemann

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- On `(0,R)` the profile of `A/‖·‖²` multiplies back to the constant `A`. -/
private lemma eqOn_mul_invSq (A R : ℝ) :
    Set.EqOn (fun r : ℝ => r ^ 2 * (A / r ^ 2)) (fun _ : ℝ => A) (Set.Ioo 0 R) := by
  intro r hr
  have hr0 : r ≠ 0 := ne_of_gt hr.1
  field_simp

/-- The radial profile `r ↦ r²·(A/r²)` of `A/‖·‖²` is integrable on `(0,R)`
(it agrees there with the constant `A`). -/
private lemma integrableOn_mul_invSq (A R : ℝ) :
    IntegrableOn (fun r : ℝ => r ^ 2 * (A / r ^ 2)) (Set.Ioo 0 R) volume := by
  have hconst : IntegrableOn (fun _ : ℝ => A) (Set.Ioo 0 R) volume := by
    apply integrableOn_const
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    · simp
  exact hconst.congr_fun (fun r hr => (eqOn_mul_invSq A R hr).symm) measurableSet_Ioo

/-- The radial integral: `∫_{(0,R)} r²·(A/r²) dr = A R`. -/
private lemma integral_mul_invSq {A R : ℝ} (hR : 0 ≤ R) :
    (∫ r in Set.Ioo (0 : ℝ) R, r ^ 2 * (A / r ^ 2)) = A * R := by
  rw [setIntegral_congr_fun measurableSet_Ioo (eqOn_mul_invSq A R)]
  rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioo, sub_zero,
    ENNReal.toReal_ofReal hR]
  ring

theorem ballInvSq {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    (MeasureTheory.IntegrableOn (fun x : EuclideanSpace ℝ (Fin 3) => A / ‖x‖ ^ 2)
        (Metric.ball 0 R) MeasureTheory.volume) ∧
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R, A / ‖x‖ ^ 2
        ≤ 4 * Real.pi * A * R) := by
  have hint : IntegrableOn (fun r : ℝ => r ^ 2 * (A / r ^ 2)) (Set.Ioo 0 R) volume :=
    integrableOn_mul_invSq A R
  have hInt : IntegrableOn (fun x : ℝ³ => A / ‖x‖ ^ 2) (Metric.ball (0 : ℝ³) R) volume :=
    (Submission.BoseGases.integrable_radial_ball_r3 (f := fun r : ℝ => A / r ^ 2) R).mpr hint
  have hVal : (∫ x in Metric.ball (0 : ℝ³) R, A / ‖x‖ ^ 2) = 4 * Real.pi * (A * R) := by
    rw [Submission.BoseGases.integral_radial_ball_r3 (f := fun r : ℝ => A / r ^ 2) R hint,
      integral_mul_invSq (A := A) hR]
  exact ⟨hInt, by rw [hVal]; exact le_of_eq (by ring)⟩

end Work.BoseRowsFS.LatRiemann
