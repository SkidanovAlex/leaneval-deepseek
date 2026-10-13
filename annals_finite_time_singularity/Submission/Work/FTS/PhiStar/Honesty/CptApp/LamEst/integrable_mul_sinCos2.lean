import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `X · sin θ cos²θ` is integrable from `L²` weighted control of `X`

Let `Iθ = [0, π/2]`, `η = 99/100`, `w z = (1+z)²/z² > 0` (for `z > 0`) and
`φ θ = w z / sin(2θ)^{η/2}`.  If `X` is a.e. strongly measurable on `Iθ` and the weighted
square `(X · φ)²` is integrable there, then `θ ↦ X θ · sin θ cos²θ` is integrable on `Iθ`.

The argument is a pointwise AM–GM domination.  On `Iθ` one has `0 ≤ sin(2θ) ≤ 1`, so
`0 ≤ sin(2θ)^{η/2} ≤ 1`, and `sin θ cos²θ = (sin 2θ / 2) · cos θ` is bounded by `1` in
absolute value.  For `sin (2θ) ≠ 0` (i.e. off the two endpoints, a null set)

`X θ · sinθcos²θ = (X θ · φ θ) · (sinθcos²θ / φ θ)`,

and `|sinθcos²θ / φ θ| = |sinθcos²θ| · sin(2θ)^{η/2} / w z ≤ 1 / w z`.  Hence, by AM–GM,

`‖X θ · sinθcos²θ‖ ≤ (X θ · φ θ)²/2 + 1/(2 (w z)²)`,

and the right-hand side is an integrable majorant because `(X · φ)²` is integrable (hypothesis)
and the second term is a constant (`Iθ` has finite measure).  Measurability of
`X · sinθcos²θ` follows from `hXm` and continuity of `sinCos2`.
-/

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

theorem integrable_mul_sinCos2 {X : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hXm : MeasureTheory.AEStronglyMeasurable X (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hX2 : MeasureTheory.Integrable
      (fun θ => (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.Integrable (fun θ => X θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- `Iθ` has finite measure, so constants are integrable.
  have hfin : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- `w z > 0` for `z > 0`.
  have hW : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  -- the majorant `(X · φ)²/2 + 1/(2 (w z)²)` is integrable.
  have hmaj : MeasureTheory.Integrable
      (fun θ => (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 / 2
        + 1 / (2 * (Work.Spaces.w z) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hX2.div_const 2).add (MeasureTheory.integrable_const_iff.mpr (Or.inr hfin))
  -- a.e. strong measurability of the target.
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => X θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hXm.mul ?_
    exact (by unfold Work.Elliptic.sinCos2; fun_prop :
      Measurable Work.Elliptic.sinCos2).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  have hsnn : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  -- `sin θ cos²θ = (sin 2θ / 2) cos θ`
  have hsc_eq : Work.Elliptic.sinCos2 θ = Real.sin (2 * θ) / 2 * Real.cos θ := by
    unfold Work.Elliptic.sinCos2; rw [Real.sin_two_mul]; ring
  by_cases hs : Real.sin (2 * θ) = 0
  · -- at the endpoints both sides vanish
    have hsc : Work.Elliptic.sinCos2 θ = 0 := by rw [hsc_eq, hs]; ring
    rw [hsc, mul_zero, Real.norm_eq_abs, abs_zero]
    positivity
  · have hs_pos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hsnn (Ne.symm hs)
    have hsp : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs_pos _
    have hspne : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 := ne_of_gt hsp
    set φ : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hφdef
    have hφpos : 0 < φ := by rw [hφdef]; exact div_pos hW hsp
    have hφne : φ ≠ 0 := ne_of_gt hφpos
    -- `X θ · sinθcos²θ = (X θ · φ) · (sinθcos²θ / φ)`
    have hid : X θ * Work.Elliptic.sinCos2 θ
        = (X θ * φ) * (Work.Elliptic.sinCos2 θ / φ) := by
      rw [mul_assoc, mul_div_cancel₀ _ hφne]
    rw [hid, Real.norm_eq_abs, abs_mul]
    -- `|sinθcos²θ| ≤ 1`
    have hsc_abs : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
      rw [hsc_eq, abs_mul]
      have h3 : |Real.sin (2 * θ) / 2| ≤ 1 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [Real.abs_sin_le_one (2 * θ)]
      nlinarith [h3, Real.abs_cos_le_one θ, abs_nonneg (Real.sin (2 * θ) / 2),
        abs_nonneg (Real.cos θ)]
    have hsp_le : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hsnn (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
    -- `|sinθcos²θ / φ| ≤ 1 / w z`
    have hB : |Work.Elliptic.sinCos2 θ / φ| ≤ 1 / Work.Spaces.w z := by
      have hrew : Work.Elliptic.sinCos2 θ / φ
          = Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
            / Work.Spaces.w z := by
        rw [hφdef]; field_simp
      rw [hrew, abs_div, abs_of_pos hW]
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hW)
      rw [abs_mul]
      have h1 : |(Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| ≤ 1 := by
        rw [abs_of_nonneg (Real.rpow_nonneg hsnn _)]; exact hsp_le
      nlinarith [hsc_abs, h1, abs_nonneg (Work.Elliptic.sinCos2 θ),
        abs_nonneg ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))]
    have hB2 : (Work.Elliptic.sinCos2 θ / φ) ^ 2 ≤ 1 / (Work.Spaces.w z) ^ 2 := by
      rw [← sq_abs (Work.Elliptic.sinCos2 θ / φ), ← one_div_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hB 2
    -- AM–GM and the final assembly
    have hamgm : |X θ * φ| * |Work.Elliptic.sinCos2 θ / φ|
        ≤ ((X θ * φ) ^ 2 + (Work.Elliptic.sinCos2 θ / φ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|X θ * φ| - |Work.Elliptic.sinCos2 θ / φ|),
        sq_abs (X θ * φ), sq_abs (Work.Elliptic.sinCos2 θ / φ)]
    calc |X θ * φ| * |Work.Elliptic.sinCos2 θ / φ|
        ≤ ((X θ * φ) ^ 2 + (Work.Elliptic.sinCos2 θ / φ) ^ 2) / 2 := hamgm
      _ ≤ ((X θ * φ) ^ 2 + 1 / (Work.Spaces.w z) ^ 2) / 2 := by nlinarith [hB2]
      _ = (X θ * φ) ^ 2 / 2 + 1 / (2 * (Work.Spaces.w z) ^ 2) := by ring

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
