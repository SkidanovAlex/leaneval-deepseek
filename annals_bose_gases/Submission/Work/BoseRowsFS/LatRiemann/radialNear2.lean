import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.RadialIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.radialNear2`

The elementary near-field (Coulomb) bound

    `∫_{‖p‖ ≤ R} ‖p‖^{-2} dp = 4πR`   (for `R ≥ 0`),

together with the integrability of the integrand.

The integrand is radial, so the polar-coordinate identity
`Submission.BoseGases.integral_fun_norm_r3`
(`∫ x : ℝ³, g ‖x‖ = 4π ∫_0^∞ r² g r dr`) reduces the integral to

    `4π ∫_0^R r² · (r²)⁻¹ dr = 4π ∫_0^R 1 dr = 4πR`,

so the bound `≤ 4πR` is attained with equality.

Integrability likewise comes from the same identity: on `(0,∞)` the radial profile
`r² · (r²)⁻¹` is the indicator of the bounded interval `(0, R]`, which is integrable.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseRowsFS.LatRiemann

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The radial profile of the integrand `p ↦ if ‖p‖ ≤ R then ‖p‖⁻² else 0`. -/
private def nearProfile (R r : ℝ) : ℝ := if r ≤ R then (r ^ 2)⁻¹ else 0

/-- On `(0,∞)` the radial measure factor turns the profile into the indicator of `(0,R]`. -/
private lemma mul_nearProfile_eq_indicator (R : ℝ) :
    ∀ r ∈ Set.Ioi (0 : ℝ),
      r ^ 2 * nearProfile R r = (Set.Ioc (0 : ℝ) R).indicator (fun _ => (1 : ℝ)) r := by
  intro r hr
  have hr0 : (0 : ℝ) < r := hr
  by_cases hle : r ≤ R
  · have hmem : r ∈ Set.Ioc (0 : ℝ) R := ⟨hr0, hle⟩
    rw [Set.indicator_of_mem hmem]
    simp only [nearProfile, if_pos hle]
    field_simp
  · have hmem : r ∉ Set.Ioc (0 : ℝ) R := fun h => hle h.2
    rw [Set.indicator_of_notMem hmem]
    simp only [nearProfile, if_neg hle, mul_zero]

/-- The indicator of the bounded interval `(0,R]` is integrable on the whole line. -/
private lemma integrable_indicator_Ioc_one (R : ℝ) :
    Integrable ((Set.Ioc (0 : ℝ) R).indicator (fun _ => (1 : ℝ))) :=
  (integrable_indicator_iff measurableSet_Ioc).2
    (integrableOn_const (C := (1 : ℝ))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by simp))

/-- The radial profile of the near-field integrand is integrable on `(0,∞)`. -/
private lemma integrableOn_mul_nearProfile (R : ℝ) :
    IntegrableOn (fun r : ℝ => r ^ 2 * nearProfile R r) (Set.Ioi (0 : ℝ)) volume :=
  (integrable_indicator_Ioc_one R).integrableOn.congr_fun
    (fun r hr => (mul_nearProfile_eq_indicator R r hr).symm) measurableSet_Ioi

/-- The radial integral of the near-field profile: `∫_0^∞ r² · (r²)⁻¹ = R`. -/
private lemma integral_Ioi_mul_nearProfile (R : ℝ) (hR : 0 ≤ R) :
    (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * nearProfile R r) = R := by
  rw [setIntegral_congr_fun measurableSet_Ioi (mul_nearProfile_eq_indicator R)]
  rw [setIntegral_indicator measurableSet_Ioc]
  rw [Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self]
  rw [setIntegral_const]
  rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hR]
  simp

theorem radialNear2 (R : ℝ) (hR : 0 ≤ R) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        if ‖p‖ ≤ R then 1 / ‖p‖ ^ 2 else 0)
      ∧ (∫ p : EuclideanSpace ℝ (Fin 3), (if ‖p‖ ≤ R then 1 / ‖p‖ ^ 2 else 0))
          ≤ 4 * Real.pi * R := by
  have hpoint : (fun p : ℝ³ => if ‖p‖ ≤ R then 1 / ‖p‖ ^ 2 else 0)
      = fun p : ℝ³ => nearProfile R ‖p‖ := by
    funext p
    simp only [nearProfile, one_div]
  have hval : (∫ p : ℝ³, nearProfile R ‖p‖) = 4 * Real.pi * R := by
    rw [Submission.BoseGases.integral_fun_norm_r3 (g := fun r : ℝ => nearProfile R r),
      integral_Ioi_mul_nearProfile R hR]
  refine ⟨?_, ?_⟩
  · rw [hpoint]
    rw [Submission.BoseGases.integrable_radial_r3]
    exact integrableOn_mul_nearProfile R
  · rw [hpoint, hval]

end Work.BoseRowsFS.LatRiemann
