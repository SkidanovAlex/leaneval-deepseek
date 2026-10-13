import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.MeridianDyn.Bridge.Pieces

/-! ## The angular slice of `K · f / s`, with only *continuity* on the open quadrant

This is the honest-hypothesis version of `sliceK_integrableOn`: the smoothness input is
reduced from `Work.FTS.EllipticEst.SmoothOpen f` (`C^∞` on the open quadrant) to mere
`ContinuousOn (Function.uncurry f) Q0`.

`Work.Spaces.K θ = 3 sin θ cos²θ` is bounded by `3` everywhere, and for `s > 0` the weight
`w s ≥ 1` while `sin(2θ)^{η/2} ≤ 1` on `Iθ`, so on the angular interval the `i = 0` term of
`HkIntegrand α 4 f` dominates `(f s θ)²` (`Work.Spaces.sq_le_HkIntegrand_z`).  With
`HkMem α 4 f` this gives the square-integrability of the slice; the slice itself is then `L¹`
because `Iθ` has finite measure, and `K θ · f s θ / s` is a bounded (`≤ 3/s`) multiple of it.

Continuity on the *open* quadrant is used only through the a.e. strong measurability of the
slice (`Work.Spaces.aesm_slice_of_continuousOn_Qd`); the two endpoints `θ = 0, π/2` are null
and the `z = 0` slice is excluded by the hypothesis `0 < s`. -/

/-- `|K θ| ≤ 3` for every `θ`. -/
private theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hcos : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg (sq_nonneg (Real.cos θ))]
  nlinarith [abs_nonneg (Real.sin θ)]

/-- `θ ↦ K θ` is continuous. -/
private theorem continuous_K : Continuous Work.Spaces.K := by
  have h : Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 := by
    funext θ; rfl
  rw [h]
  exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)

/-- The angular slice `θ ↦ (f s θ)²` of an `HkMem α 4` datum with *continuity on the open
quadrant* is integrable on `Iθ` for `s > 0`.  This is the analogue of the helper inside
`Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn` (equivalently
`Work.FTS.H2.l12q_slice_sq_integrableOn`) with the hypothesis `SmoothOpen f` weakened to
`ContinuousOn (Function.uncurry f) Q0`. -/
private theorem slice_sq_integrableOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ := by
  -- the squared slice is a.e. strongly measurable (continuity on the open quadrant)
  have hquad : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hC
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
    simpa only [Function.uncurry] using h2
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f s θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) hquad hs
  -- domination by the `i = 0` term of `HkIntegrand`
  have hsI : s ∈ Work.Spaces.Iz := le_of_lt hs
  refine (hmem.1 s hsI).mono' haesm ?_
  -- the pointwise bound only fails on the two null endpoints
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := π / 2)).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hs]
  have hkey : 1 ≤ Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f s θ) ^ 2 ≤ (f s θ * (Work.Spaces.w s
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f s θ) ^ 2 = (f s θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f s θ) ^ 2
            * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f s θ * (Work.Spaces.w s
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f s θ) ^ 2‖ = (f s θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f s θ * (Work.Spaces.w s
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f s θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 0 (by norm_num)

/-- The slice `θ ↦ K θ · f s θ / s` is integrable on `Iθ` for `s > 0`, assuming only that
`f` is continuous on the open quadrant and lies in `ℋ⁴`. -/
theorem sliceK_integrableOn_of_continuousOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ := by
  intro s hs
  -- the slice square and its measurability
  have hsq := slice_sq_integrableOn hC hmem hs
  have hfm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hC hs
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.K θ / s) * f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((continuous_K.div_const s).aestronglyMeasurable).mul hfm
  -- the integrable majorant `(3/(2s))·(f² + 1)`
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const
      (by rw [Work.Spaces.Iθ]; exact ne_of_lt measure_Icc_lt_top) (by simp)
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (3 / (2 * s)) * ((f s θ) ^ 2 + 1)) Work.Spaces.Iθ :=
    (hsq.add hconst).const_mul _
  -- the pointwise bound `|K θ|·|f s θ|/s ≤ (3/(2s))·(f² + 1)`
  have hbd : ∀ θ : ℝ, ‖(Work.Spaces.K θ / s) * f s θ‖
      ≤ (3 / (2 * s)) * ((f s θ) ^ 2 + 1) := by
    intro θ
    have hK := abs_K_le_three θ
    have key : 2 * |f s θ| ≤ (f s θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|f s θ| - 1), sq_abs (f s θ)]
    have hc : 0 ≤ 3 / (2 * s) := div_nonneg (by norm_num) (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hs]
    calc |Work.Spaces.K θ| / s * |f s θ|
        ≤ 3 / s * |f s θ| :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK (le_of_lt hs))
            (abs_nonneg _)
      _ = (3 / (2 * s)) * (2 * |f s θ|) := by field_simp
      _ ≤ (3 / (2 * s)) * ((f s θ) ^ 2 + 1) := mul_le_mul_of_nonneg_left key hc
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.K θ / s) * f s θ)
      Work.Spaces.Iθ := by
    refine hmaj.mono' haesm ?_
    exact Filter.Eventually.of_forall hbd
  -- reassociate `K θ / s * f s θ` into `K θ * f s θ / s`
  refine hint.congr_fun (fun θ _ => ?_) ?_
  · ring
  · rw [Work.Spaces.Iθ]; exact measurableSet_Icc

end Work.FTS.MeridianDyn.Bridge.Pieces
