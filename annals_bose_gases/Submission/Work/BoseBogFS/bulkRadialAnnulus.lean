import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.RadialIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Work.BoseBogFS.bulkRadialAnnulus` — polar coordinates on the annulus

The volume element of `ℝ³` is `4π r² dr`, so the integral over the annulus
`{a < ‖t‖ ≤ T}` of a radial function `G ‖·‖` is `4π∫_{a}^{T} r²G(r)dr`.  This is the
unconditional Bochner identity `Submission.BoseGases.integral_fun_norm_r3`, so no
integrability hypothesis is needed.
-/

noncomputable section

/-- **Polar coordinates on the annulus** `{a < ‖t‖ ≤ T}`. -/
theorem bulk_radial_eq (G : ℝ → ℝ) {a T : ℝ} (ha : 0 < a) (hle : a ≤ T) :
    (∫ t in {t : E3 | a < ‖t‖ ∧ ‖t‖ ≤ T}, G ‖t‖)
      = 4 * Real.pi * (∫ r in Set.Ioc a T, r ^ 2 * G r) := by
  have hSmeas : MeasurableSet {t : E3 | a < ‖t‖ ∧ ‖t‖ ≤ T} := by measurability
  rw [← MeasureTheory.integral_indicator (μ := volume) (s := {t : E3 | a < ‖t‖ ∧ ‖t‖ ≤ T})
    (f := fun t : E3 => G ‖t‖) hSmeas]
  have hpoint : ∀ t : E3,
      ({t : E3 | a < ‖t‖ ∧ ‖t‖ ≤ T}.indicator (fun t : E3 => G ‖t‖)) t
        = ((Set.Ioc a T).indicator G) ‖t‖ := by
    intro t
    simp only [Set.indicator, Set.mem_setOf_eq, Set.mem_Ioc]
  rw [show (∫ t : E3, ({t : E3 | a < ‖t‖ ∧ ‖t‖ ≤ T}.indicator (fun t : E3 => G ‖t‖)) t)
      = ∫ t : E3, ((Set.Ioc a T).indicator G) ‖t‖ from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [Submission.BoseGases.integral_fun_norm_r3 (g := (Set.Ioc a T).indicator G)]
  congr 1
  have hfun : ∀ r : ℝ, r ^ 2 * ((Set.Ioc a T).indicator G) r
      = (Set.Ioc a T).indicator (fun r => r ^ 2 * G r) r := by
    intro r
    by_cases h : r ∈ Set.Ioc a T
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [show (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * ((Set.Ioc a T).indicator G) r)
      = ∫ r in Set.Ioi (0 : ℝ), (Set.Ioc a T).indicator (fun r => r ^ 2 * G r) r from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => hfun r)]
  rw [MeasureTheory.setIntegral_indicator (s := Set.Ioi (0 : ℝ)) (t := Set.Ioc a T)
    (f := fun r => r ^ 2 * G r) measurableSet_Ioc]
  rw [show (Set.Ioi (0 : ℝ)) ∩ Set.Ioc a T = Set.Ioc a T from by
    ext r
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨lt_trans ha h.1, h⟩]

end

end Work.BoseBogFS
