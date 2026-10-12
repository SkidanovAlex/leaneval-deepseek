import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs9.B.integral_chiB_mul_partialDeriv_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.integral_chiScale_sub_smul_mul_fderiv_eq_zero`

The first-moment (oddness) identity for the single scaled bump `chiScale a = χ((a)⁻¹ • ·)`
along the scaling `u ↦ c - a • u`:

    `∫_u chiScale a (c - a•u) · (∂ chiScale a (c - a•u)) e du = 0`.

## Why it is true

Write `w := a⁻¹ • c`.  Since `chiScale a y = χ(a⁻¹ • y)`, the substitution `y = c - a•u`
gives a *pure translation--reflection* in `u`, namely `chiScale a (c - a•u) = χ(w - u)`, and
by the rescaling rule for the gradient `fderiv ℝ (chiScale a) (c - a•u) e
= a⁻¹ · (fderiv ℝ χ (w - u)) e`.  Hence the integrand is `a⁻¹ · χ(w - u) · (∂χ(w-u)) e`
and the translation/reflection invariance of Lebesgue measure
(`MeasureTheory.integral_sub_left_eq_self`) turns the `u`-integral into
`a⁻¹ · ∫_v χ v · (∂χ v) e dv`, which vanishes because `v ↦ χ v · (∂χ v) e` is odd
(the derivative of an even function is odd).

## Contents

* `integral_chiScale_sub_smul_mul_fderiv_eq_zero` — the target identity.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real

namespace Work.UBBInputs9.B

open Submission.BoseGases Work.UBBInputs9.B.ChiDeriv

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 400000

theorem integral_chiScale_sub_smul_mul_fderiv_eq_zero (a : ℝ) (ha : 0 < a)
    (c e : EuclideanSpace ℝ (Fin 3)) :
    (∫ u : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiScale a (c - a • u) *
        fderiv ℝ (Submission.BoseGases.chiScale a) (c - a • u) e) = 0 := by
  have ha' : a ≠ 0 := ne_of_gt ha
  -- pointwise: the integrand is `a⁻¹ · χ(w - u) · (∂χ(w-u)) e` with `w = a⁻¹ • c`
  have hpt : ∀ u : ℝ³,
      chiScale a (c - a • u) * fderiv ℝ (chiScale a) (c - a • u) e
        = a⁻¹ * (chi (a⁻¹ • c - u) * fderiv ℝ chi (a⁻¹ • c - u) e) := by
    intro u
    rw [chiScale_sub_smul_eq a ha' c u, fderiv_chiScale_apply a (c - a • u) e]
    have hw : a⁻¹ • (c - a • u) = a⁻¹ • c - u := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ha', one_smul]
    rw [hw]
    ring
  -- translation--reflection invariance of the `u`-integral
  have hsub : (∫ u : ℝ³, chi (a⁻¹ • c - u) * fderiv ℝ chi (a⁻¹ • c - u) e)
      = (∫ v : ℝ³, chi v * fderiv ℝ chi v e) :=
    MeasureTheory.integral_sub_left_eq_self
      (fun v : ℝ³ => chi v * fderiv ℝ chi v e) volume (a⁻¹ • c)
  -- the remaining integral vanishes by oddness
  have hodd : (∫ v : ℝ³, chi v * fderiv ℝ chi v e) = 0 :=
    integral_odd_eq_zero (fun v : ℝ³ => chi v * fderiv ℝ chi v e)
      (odd_chi_mul_fderiv_chi e)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul, hsub, hodd, mul_zero]

end Work.UBBInputs9.B
