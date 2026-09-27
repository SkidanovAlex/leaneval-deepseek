import Mathlib
import Submission.Work.Mostow.VolDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

/-- Equality case of the weighted area formula. `hFJ` and `VolDefs.hjac_nonneg` give
`ofReal (hjac F u) ≤ 1 = ofReal 1` pointwise, so the hypothesis forces
`∫⁻ (1 - ofReal (hjac F u)) = 0` over `S`; `lintegral_eq_zero_iff` and injectivity of `ofReal` give
`hjac F u = 1` a.e. on `S`. -/
theorem hjacAeEqOneOfIntegralEq (n : ℕ) {F : E n → E n} (hF : ContDiff ℝ 1 F)
    (hFJ : ∀ u, hjac F u ≤ 1) {S : Set (E n)} (hS : MeasurableSet S) (hfin : volH n S < ⊤)
    (h : ∫⁻ u in S, ENNReal.ofReal (hjac F u) ∂(volH n) = volH n S) :
    ∀ᵐ u ∂(volH n), u ∈ S → hjac F u = 1 := by
  -- `ofReal (hjac F ·)` is measurable
  have hmeas : Measurable fun u : E n => ENNReal.ofReal (hjac F u) :=
    ENNReal.measurable_ofReal.comp (hjacContinuous n hF).measurable
  -- the integral of `ofReal (hjac F ·)` over `S` is finite
  have hg_fin : ∫⁻ u in S, ENNReal.ofReal (hjac F u) ∂(volH n) ≠ ∞ := by
    rw [h]; exact ne_of_lt hfin
  -- and it is dominated by `1`
  have hle : (fun u : E n => ENNReal.ofReal (hjac F u)) ≤ᵐ[(volH n).restrict S] (fun _ => 1) :=
    ae_of_all _ (fun u => (ENNReal.ofReal_le_one).mpr (hFJ u))
  -- hence the difference `1 - ofReal (hjac F ·)` integrates to `0`
  have hzero : ∫⁻ u in S, ((1:ℝ≥0∞) - ENNReal.ofReal (hjac F u)) ∂(volH n) = 0 := by
    rw [lintegral_sub hmeas hg_fin hle]
    rw [setLIntegral_one, h]
    simp
  -- `lintegral_eq_zero_iff` turns this into an a.e. vanishing, and `ae_restrict_iff'` removes the
  -- restriction to `S`
  have hae : (fun u : E n => (1:ℝ≥0∞) - ENNReal.ofReal (hjac F u)) =ᵐ[(volH n).restrict S] 0 :=
    (lintegral_eq_zero_iff (measurable_const.sub hmeas)).mp hzero
  rw [Filter.EventuallyEq, ae_restrict_iff' hS] at hae
  filter_upwards [hae] with u hu hS'
  -- `1 - ofReal (hjac F u) = 0` gives `1 ≤ ofReal (hjac F u)`, and `hFJ` gives the reverse bound
  have h2 : (1:ℝ≥0∞) ≤ ENNReal.ofReal (hjac F u) := tsub_eq_zero_iff_le.mp (hu hS')
  have h3 : ENNReal.ofReal (hjac F u) = 1 :=
    le_antisymm (ENNReal.ofReal_le_one.mpr (hFJ u)) h2
  exact ENNReal.ofReal_eq_one.mp h3

end Work.Mostow
