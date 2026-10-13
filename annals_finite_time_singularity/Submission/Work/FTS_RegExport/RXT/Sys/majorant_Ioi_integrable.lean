import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FM.Core
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn
import Submission.Work.FTS_RegExport.RXT.Sys.MajorantPieces.sqrt_div_sq_Ioi_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

open MeasureTheory Set Filter

/-- Integrability on `(0,∞)` of the majorant `3*(π/2)*(20/(1+s)² + Cw*s^{1/2}/(1+s)²)` and its
integral bound.

PROOF RECIPE.  `∫_{Ioi 0} 1/(1+s)² = 1` via `Work.FM.integral_Ioi_Fstar_div 0 le_rfl`
(`∫_{Ioi 0} FM.Fstar s/s = 2`) together with `FM.Fstar s / s = 2/(1+s)²` for `s ≠ 0` (a.e. on
`Ioi 0`; `FM.Fstar s = 2*s/(1+s)^2`), and `∫_{Ioi 0} s^{1/2}/(1+s)² ≤ 3`: dominate by
`(1+s)^{-1/2}*(1+s)^{-1} ` -- concretely `s^{1/2}/(1+s)² ≤ (1+s)^{-3/2}` (since `s^{1/2} ≤ (1+s)^{1/2}`)
and `∫_{Ioi 0} (1+s)^{-3/2} = 2` (primitive `-2*(1+s)^{-1/2}`; e.g.
`MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'`, or split `Ioi 0 = Ioc 0 1 ∪ Ioi 1` and use
`intervalIntegral` / `integral_Ioi_rpow_of_lt` after the shift).  All three integrands are
nonnegative, so `MeasureTheory.IntegrableOn` follows from the pointwise domination and the
integrability of the dominating functions (`MeasureTheory.Integrable.mono'`,
`ContinuousOn.aestronglyMeasurable`).  Finally distribute the constants with `integral_add`,
`integral_const_mul` and use `Real.pi_le_four` for `3*(π/2)*20 = 30π ≤ 120` and
`3*(π/2)*3*Cw = (9π/2)*Cw ≤ 18*Cw` (`hCw : 0 ≤ Cw`). -/
theorem majorant_Ioi_integrable {Cw : ℝ} (hCw : 0 ≤ Cw) :
    MeasureTheory.IntegrableOn
        (fun s : ℝ => 3 * (Real.pi / 2)
          * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
        (Set.Ioi 0) ∧
      (∫ s in Set.Ioi 0, 3 * (Real.pi / 2)
          * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
        ≤ 120 + 18 * Cw := by
  -- ## The first elementary tail integral: `∫_{(0,∞)} ds/(1+s)² = 1`
  -- `FM.Fstar s / s = 2/(1+s)²` on `(0,∞)`
  have hFcongr : EqOn (fun s : ℝ => Work.FM.Fstar s / s)
      (fun s : ℝ => 2 / (1 + s) ^ 2) (Set.Ioi 0) := by
    intro s hs
    have hs0 : s ≠ 0 := by have := hs.out; linarith
    unfold Work.FM.Fstar
    field_simp
  have htwo : (∫ s in Set.Ioi (0 : ℝ), 2 / (1 + s) ^ 2) = 2 := by
    have h := Work.FM.integral_Ioi_Fstar_div 0 le_rfl
    rw [setIntegral_congr_fun measurableSet_Ioi hFcongr] at h
    simpa using h
  have hA_int : IntegrableOn (fun s : ℝ => 1 / (1 + s) ^ 2) (Set.Ioi 0) := by
    have h2 := Work.FTS.MeridianDyn.Bridge.Pieces.integrableOn_two_div_one_add_sq 0 le_rfl
    refine MeasureTheory.IntegrableOn.congr_fun (h2.integrable.const_mul (1 / 2)) ?_
      measurableSet_Ioi
    intro s _
    ring
  have hA_val : (∫ s in Set.Ioi (0 : ℝ), 1 / (1 + s) ^ 2) = 1 := by
    have h2 : (∫ s in Set.Ioi (0 : ℝ), 2 * (1 / (1 + s) ^ 2)) = 2 := by
      rw [show (fun s : ℝ => 2 * (1 / (1 + s) ^ 2)) =
          fun s : ℝ => 2 / (1 + s) ^ 2 by funext s; ring]
      exact htwo
    rw [MeasureTheory.integral_const_mul (2 : ℝ)] at h2
    linarith
  -- ## The second elementary tail integral: `∫_{(0,∞)} s^{1/2}/(1+s)² ≤ 3`
  -- (the general tail bound `∫_{(z,∞)} ≤ 3` for `z ≥ 0` at `z = 0`)
  obtain ⟨hB_int, hB_val⟩ :=
    MajorantPieces.sqrt_div_sq_Ioi_integral_le (z := 0) le_rfl
  -- ## Integrability of the two summands of the majorant
  have h20_int : IntegrableOn (fun s : ℝ => 20 / (1 + s) ^ 2) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun (hA_int.integrable.const_mul 20)
      (fun s _ => by ring) measurableSet_Ioi
  have hCw_int : IntegrableOn (fun s : ℝ => Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
      (Set.Ioi 0) := hB_int.integrable.const_mul Cw
  have hsum_int : IntegrableOn
      (fun s : ℝ => 20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
      (Set.Ioi 0) := h20_int.add hCw_int
  refine ⟨hsum_int.integrable.const_mul (3 * (Real.pi / 2)), ?_⟩
  -- ## The two integral values
  have h20val : (∫ s in Set.Ioi (0 : ℝ), 20 / (1 + s) ^ 2) = 20 := by
    have hk : (∫ s in Set.Ioi (0 : ℝ), 20 * (1 / (1 + s) ^ 2))
        = 20 * (∫ s in Set.Ioi (0 : ℝ), 1 / (1 + s) ^ 2) :=
      MeasureTheory.integral_const_mul (20 : ℝ) (fun s : ℝ => 1 / (1 + s) ^ 2)
    rw [show (fun s : ℝ => 20 / (1 + s) ^ 2) = fun s : ℝ => 20 * (1 / (1 + s) ^ 2) by
      funext s; ring, hk, hA_val]
    norm_num
  have hCwval : (∫ s in Set.Ioi (0 : ℝ), Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) ≤ 3 * Cw := by
    have hk : (∫ s in Set.Ioi (0 : ℝ), Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
        = Cw * (∫ s in Set.Ioi (0 : ℝ), s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) :=
      MeasureTheory.integral_const_mul (Cw : ℝ)
        (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)
    rw [hk]
    calc Cw * (∫ s in Set.Ioi (0 : ℝ), s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) ≤ Cw * 3 :=
          mul_le_mul_of_nonneg_left hB_val hCw
      _ = 3 * Cw := by ring
  have hsum_val : (∫ s in Set.Ioi (0 : ℝ),
        (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))) ≤ 20 + 3 * Cw := by
    rw [MeasureTheory.integral_add h20_int hCw_int]
    linarith
  -- ## Distributing the constants
  have hconst : (∫ s in Set.Ioi (0 : ℝ), 3 * (Real.pi / 2)
        * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
      = 3 * (Real.pi / 2) * (∫ s in Set.Ioi (0 : ℝ),
          (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))) :=
    MeasureTheory.integral_const_mul (3 * (Real.pi / 2)) _
  rw [hconst]
  have hstep : 3 * (Real.pi / 2) * (∫ s in Set.Ioi (0 : ℝ),
        (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
      ≤ 3 * (Real.pi / 2) * (20 + 3 * Cw) :=
    mul_le_mul_of_nonneg_left hsum_val (by positivity)
  have h1 : 3 * (Real.pi / 2) * 20 ≤ 120 := by linarith [Real.pi_le_four]
  have h2 : 3 * (Real.pi / 2) * (3 * Cw) ≤ 18 * Cw := by
    have h3 : 3 * (Real.pi / 2) * 3 ≤ 18 := by linarith [Real.pi_le_four]
    calc 3 * (Real.pi / 2) * (3 * Cw) = (3 * (Real.pi / 2) * 3) * Cw := by ring
      _ ≤ 18 * Cw := mul_le_mul_of_nonneg_right h3 hCw
  linarith [hstep, h1, h2, mul_add (3 * (Real.pi / 2)) 20 (3 * Cw)]

end Work.FTS_RegExport.RXT.Sys
