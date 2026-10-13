/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `K`-weighted angular integral is `3(π/2)`-Lipschitz in the datum

This module proves

  `Work.FTS_RegExport.RXT.Sys.L12FKaux.KweightIntegralSub`,

the elementary but ubiquitous estimate that the angular functional

  `F ↦ ∫_{Iθ} K(θ) F(θ) dθ`,   `K(θ) = 3 sinθ cos²θ`,   `Iθ = [0,π/2]`,

changes by at most `3 (π/2) C` when the datum is changed by at most `C` pointwise almost
everywhere (both `K F` and `K F'` being integrable):

  `|∫_{Iθ} K F − ∫_{Iθ} K F'| ≤ 3 (π/2) C`.

The proof is the crude bound `|K| ≤ 3` on all of `ℝ` (so that `‖K·(F−F')‖ ≤ 3C` a.e.) fed
into `MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae` together with
`volume.real Iθ = π/2`.  The *sharp* constant of the functional is `1 = ∫_{Iθ} K` (since
`K = -(cos³)'`), but only the crude bound `3(π/2)` is needed, and it holds with no
positivity assumption on `C` beyond what the hypothesis `|F − F'| ≤ C` itself forces.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

set_option autoImplicit false

/-! ## Elementary facts about the weight `K` and the interval `Iθ` -/

/-- `|K(θ)| = |3 sinθ cos²θ| ≤ 3` for every real `θ` (in particular on `Iθ`). -/
private theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hb : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg hb]
  have h1 : |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 := by
    calc |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 * 1 := mul_le_mul hs hc hb (by norm_num)
      _ = 1 := by ring
  nlinarith [h1, abs_nonneg (Real.sin θ)]

/-- The Lebesgue measure of `Iθ = [0, π/2]` is `π/2`. -/
private theorem volume_real_Iθ : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [MeasureTheory.Measure.real_def, Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
  ring

/-- The Lebesgue measure of `Iθ = [0, π/2]` is finite. -/
private theorem volume_Iθ_lt_top : MeasureTheory.volume Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-! ## The estimate -/

theorem KweightIntegralSub {F F' : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hint : MeasureTheory.Integrable (fun θ => Work.Spaces.K θ * F θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hint' : MeasureTheory.Integrable (fun θ => Work.Spaces.K θ * F' θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), |F θ - F' θ| ≤ C) :
    |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F θ)
      - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F' θ)| ≤ 3 * (Real.pi / 2) * C := by
  -- the difference of the two integrals is the integral of the difference
  have hdiff : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F θ)
      - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F' θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (F θ - F' θ) := by
    rw [← MeasureTheory.integral_sub hint hint']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro θ _
    ring
  rw [hdiff]
  -- the pointwise (a.e.) bound `‖K θ · (F θ - F' θ)‖ ≤ 3 C` on `Iθ`
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * (F θ - F' θ)‖ ≤ 3 * C := by
    filter_upwards [hbd] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three θ) hθ (abs_nonneg _) (by norm_num)
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
    (μ := MeasureTheory.volume) (s := Work.Spaces.Iθ)
    (f := fun θ => Work.Spaces.K θ * (F θ - F' θ)) (C := 3 * C)
    volume_Iθ_lt_top hae
  rw [Real.norm_eq_abs, volume_real_Iθ] at h
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (F θ - F' θ)| ≤ 3 * C * (Real.pi / 2) := h
    _ = 3 * (Real.pi / 2) * C := by ring

end Work.FTS_RegExport.RXT.Sys.L12FKaux
