import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseB6.fsTau_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6 — the small-ball part of FS `lem:BogIntegral` (`I₁`, `|t| ≤ R`)

FS's `I₁`-estimate (`eq:LebesgueError-Total`, `Papers/fournais_solovej/final_v2.tex`)
controls the scaled Bogoliubov zero-point integral

  `I₁ = ∫_{ℝ³} [α(t) − √(α(t)² − β(t)²) − β(t)²/(2t²)] dt`,   `α = τ̃ + β`,

with `β(t) = a⁻¹Ŵ₁(√(ρ_z a) t)`, `0 ≤ β ≤ B`, and `τ̃ = τ̃(ε_T,c₁,c₂)` (`fsTau`).
The part of any such integral over the *small* ball `|t| ≤ R` (FS: `|t| ≤ 10(K_ℓs)⁻¹`,
with `c₁ ≈ ½(K_ℓs)⁻¹(μ/ρ_z)^{1/2}` and `R ≤ c₁`) is bounded by a constant times `c₁`.

This module proves the small-ball estimate needed in that reduction, in the raw
form in which the requester states it:

  `|∫_{‖t‖ ≤ R} (β‖t‖ − (β‖t‖)²/(2‖t‖²))| ≤ 10 (B + B²) c₁`   for `0 ≤ R ≤ c₁ ≤ 1`.

## Strategy

Polar coordinates on `ℝ³` (`Submission.BoseGases.integral_fun_norm_r3`,
Mathlib's `MeasureTheory.integral_fun_norm_addHaar`, dimension `3`, unit ball
`(4/3)π`) turn the ball integral of the radial integrand into the one-dimensional
integral

  `∫_{‖t‖ ≤ R} F(‖t‖) dt = 4π ∫_{r∈(0,R]} r² F(r) dr`;

because `r²((β r) − (β r)²/(2r²)) = r² (β r) − (β r)²/2` on `r > 0`, the radius
integrand is *bounded* (`|r²β r − (β r)²/2| ≤ B r² + B²/2`), so the profile
integral is at most `B R³/3 + B² R/2`, and `4π (B R³/3 + B² R/2) ≤ 10(B + B²)c₁`
since `R ≤ c₁`, `R ≤ 1`, `0 ≤ B` and `π < 4`.

The polar identity is *unconditional* for Bochner integrals (a function that is
not integrable has integral `0`), which is how the possibly non-measurable `β` is
handled: on the `(0,R]` side the integrand is dominated by an explicit integrable
majorant.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseB6

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Polar coordinates on the closed ball -/

/-- **Radial (polar) integration over the closed ball of `ℝ³`**, unconditionally:
`∫_{‖t‖ ≤ R} F(‖t‖) dt = 4π ∫_{r ∈ (0,R]} r² F(r) dr`.  This is
`Submission.BoseGases.integral_fun_norm_r3` applied to the indicator of `Iic R`
(so that the two sides see the closed ball and the half-open interval `(0,R]`),
with `dim ℝ³ = 3` and unit-ball measure `4π/3`. -/
lemma integral_radial_closedBall_r3 (R : ℝ) (F : ℝ → ℝ) :
    (∫ t in Metric.closedBall (0 : ℝ³) R, F ‖t‖)
      = 4 * Real.pi * ∫ r in Set.Ioc 0 R, r ^ 2 * F r := by
  have h1 : (fun x : ℝ³ => (Set.Iic R).indicator F ‖x‖)
      = (Metric.closedBall (0 : ℝ³) R).indicator (fun x : ℝ³ => F ‖x‖) := by
    funext x
    by_cases hx : ‖x‖ ≤ R <;> simp [hx, Metric.mem_closedBall, dist_eq_norm]
  have h2 : (fun r : ℝ => r ^ 2 * ((Set.Iic R).indicator F) r)
      = (Set.Iic R).indicator (fun r : ℝ => r ^ 2 * F r) := by
    funext r
    by_cases hr : r ≤ R <;> simp [hr]
  calc (∫ t in Metric.closedBall (0 : ℝ³) R, F ‖t‖)
      = ∫ x : ℝ³, (Metric.closedBall (0 : ℝ³) R).indicator (fun x : ℝ³ => F ‖x‖) x := by
        rw [MeasureTheory.integral_indicator measurableSet_closedBall]
    _ = ∫ x : ℝ³, (Set.Iic R).indicator F ‖x‖ := by rw [h1]
    _ = 4 * Real.pi * ∫ r in Set.Ioi 0, r ^ 2 * ((Set.Iic R).indicator F) r :=
        Submission.BoseGases.integral_fun_norm_r3 (g := (Set.Iic R).indicator F)
    _ = 4 * Real.pi * ∫ r in Set.Ioc 0 R, r ^ 2 * F r := by
        rw [h2, MeasureTheory.setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]

/-! ## 2. A one-dimensional dominated-integral bound -/

/-- If `|f| ≤ h` pointwise on `s`, `h` is integrable on `s` and the integral of
`f` is only ever taken in the (Bochner) sense "`0` when not integrable", then
`∫_s |f| ≤ ∫_s h`.  The point is that no measurability of `f` is assumed: the
non-integrable case is trivial. -/
lemma setIntegral_abs_le_of_le {f h : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hle : ∀ x ∈ s, |f x| ≤ h x) (hh : IntegrableOn h s volume) :
    ∫ x in s, |f x| ≤ ∫ x in s, h x := by
  rcases em (IntegrableOn (fun x => |f x|) s volume) with hf | hf
  · exact setIntegral_mono_on hf hh hs hle
  · rw [integral_undef hf]
    refine setIntegral_nonneg_of_ae_restrict ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    exact le_trans (abs_nonneg (f x)) (hle x hx)

/-! ## 3. The radius integral -/

/-- **The one-dimensional small-`r` bound.**  For `0 ≤ R` and `0 ≤ β ≤ Bu`,

  `|∫_{r ∈ (0,R]} r² (β r − (β r)²/(2r²)) dr| ≤ Bu R³/3 + Bu² R/2`.

On `r > 0` the integrand is `r²β r − (β r)²/2`, which is bounded in absolute
value by the integrable majorant `Bu r² + Bu²/2`. -/
lemma Ioc_integral_bound {Bu R : ℝ} (hR0 : 0 ≤ R) {β : ℝ → ℝ}
    (hβ0 : ∀ r, 0 ≤ β r) (hβB : ∀ r, β r ≤ Bu) :
    |∫ r in Set.Ioc 0 R, r ^ 2 * (β r - (β r) ^ 2 / (2 * r ^ 2))|
      ≤ Bu * R ^ 3 / 3 + Bu ^ 2 * R / 2 := by
  have hcongr : ∫ r in Set.Ioc 0 R, r ^ 2 * (β r - (β r) ^ 2 / (2 * r ^ 2))
      = ∫ r in Set.Ioc 0 R, (r ^ 2 * β r - (β r) ^ 2 / 2) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr.1
    field_simp
  have hcont : Continuous (fun r : ℝ => Bu * r ^ 2 + Bu ^ 2 / 2) := by fun_prop
  have hhint : IntegrableOn (fun r : ℝ => Bu * r ^ 2 + Bu ^ 2 / 2) (Set.Ioc 0 R) volume :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hR0).mp (hcont.intervalIntegrable 0 R)).mono_set
      Set.Ioc_subset_Icc_self
  have hle : ∀ x ∈ Set.Ioc 0 R, |x ^ 2 * β x - (β x) ^ 2 / 2| ≤ Bu * x ^ 2 + Bu ^ 2 / 2 := by
    intro x hx
    have hbx : 0 ≤ β x := hβ0 x
    have hb2 : (β x) ^ 2 ≤ Bu ^ 2 := pow_le_pow_left₀ hbx (hβB x) 2
    have h1 : 0 ≤ x ^ 2 * β x := mul_nonneg (sq_nonneg x) hbx
    have h2 : 0 ≤ (β x) ^ 2 / 2 := by positivity
    have h3 : x ^ 2 * β x ≤ Bu * x ^ 2 := by nlinarith [hβB x, sq_nonneg x]
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hhval : ∫ r in Set.Ioc 0 R, (Bu * r ^ 2 + Bu ^ 2 / 2)
      = Bu * R ^ 3 / 3 + Bu ^ 2 * R / 2 := by
    rw [← intervalIntegral.integral_of_le hR0]
    have hI1 : IntervalIntegrable (fun r : ℝ => Bu * r ^ 2) volume 0 R :=
      (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 R
    have hI2 : IntervalIntegrable (fun _ : ℝ => Bu ^ 2 / 2) volume 0 R :=
      continuous_const.intervalIntegrable 0 R
    rw [intervalIntegral.integral_add hI1 hI2]
    rw [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const]
    norm_num
    ring
  rw [hcongr]
  have habs : |∫ r in Set.Ioc 0 R, (r ^ 2 * β r - (β r) ^ 2 / 2)|
      ≤ ∫ r in Set.Ioc 0 R, |r ^ 2 * β r - (β r) ^ 2 / 2| :=
    MeasureTheory.abs_integral_le_integral_abs
      (f := fun r : ℝ => r ^ 2 * β r - (β r) ^ 2 / 2) (μ := volume.restrict (Set.Ioc 0 R))
  have hmaj : ∫ r in Set.Ioc 0 R, |r ^ 2 * β r - (β r) ^ 2 / 2|
      ≤ Bu * R ^ 3 / 3 + Bu ^ 2 * R / 2 := by
    rw [← hhval]
    exact setIntegral_abs_le_of_le measurableSet_Ioc hle hhint
  linarith

/-! ## 4. The requested bound -/

theorem I1_small_ball_bound {c1 c2 Bu R : ℝ} (hc1 : 0 ≤ c1) (hc1' : c1 ≤ 1) (hc12 : c1 ≤ c2)
    (hR0 : 0 ≤ R) (hR : R ≤ c1) (hBu : 0 ≤ Bu) {β : ℝ → ℝ} (hβ0 : ∀ r, 0 ≤ β r)
    (hβB : ∀ r, β r ≤ Bu) :
    |∫ t : EuclideanSpace ℝ (Fin 3) in {t : EuclideanSpace ℝ (Fin 3) | ‖t‖ ≤ R},
        (β ‖t‖ - (β ‖t‖) ^ 2 / (2 * ‖t‖ ^ 2))|
      ≤ 10 * (Bu + Bu ^ 2) * c1 := by
  have hset : {t : ℝ³ | ‖t‖ ≤ R} = Metric.closedBall (0 : ℝ³) R := by
    ext t; simp [Metric.mem_closedBall, dist_eq_norm]
  have hF : (fun t : ℝ³ => β ‖t‖ - (β ‖t‖) ^ 2 / (2 * ‖t‖ ^ 2))
      = (fun t : ℝ³ => (fun r : ℝ => β r - (β r) ^ 2 / (2 * r ^ 2)) ‖t‖) := rfl
  rw [hset, hF, integral_radial_closedBall_r3 R (fun r : ℝ => β r - (β r) ^ 2 / (2 * r ^ 2))]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
  have hb : |∫ r in Set.Ioc 0 R, r ^ 2 * ((fun r : ℝ => β r - (β r) ^ 2 / (2 * r ^ 2)) r)|
      ≤ Bu * R ^ 3 / 3 + Bu ^ 2 * R / 2 := Ioc_integral_bound hR0 hβ0 hβB
  have hR1 : R ≤ 1 := le_trans hR hc1'
  have hR2 : R ^ 2 ≤ 1 := by nlinarith
  have hR3 : R ^ 3 ≤ R := by nlinarith [hR2, hR0]
  have hBu2 : 0 ≤ Bu ^ 2 := sq_nonneg Bu
  have e1 : 4 * Real.pi * (Bu * R ^ 3 / 3 + Bu ^ 2 * R / 2)
      = (4 * Real.pi / 3) * (Bu * R ^ 3) + (2 * Real.pi) * (Bu ^ 2 * R) := by ring
  have e2 : 10 * (Bu + Bu ^ 2) * c1 = 10 * (Bu * c1) + 10 * (Bu ^ 2 * c1) := by ring
  have h1 : (4 * Real.pi / 3) * (Bu * R ^ 3) ≤ 10 * (Bu * c1) := by
    have hA : (0 : ℝ) ≤ 4 * Real.pi / 3 := by positivity
    calc (4 * Real.pi / 3) * (Bu * R ^ 3) ≤ (4 * Real.pi / 3) * (Bu * c1) := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact mul_le_mul_of_nonneg_left (le_trans hR3 hR) hBu
      _ ≤ 10 * (Bu * c1) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (mul_nonneg hBu hc1)
  have h2 : (2 * Real.pi) * (Bu ^ 2 * R) ≤ 10 * (Bu ^ 2 * c1) := by
    have hA : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc (2 * Real.pi) * (Bu ^ 2 * R) ≤ (2 * Real.pi) * (Bu ^ 2 * c1) := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact mul_le_mul_of_nonneg_left hR hBu2
      _ ≤ 10 * (Bu ^ 2 * c1) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (mul_nonneg hBu2 hc1)
  calc 4 * Real.pi * |∫ r in Set.Ioc 0 R,
          r ^ 2 * ((fun r : ℝ => β r - (β r) ^ 2 / (2 * r ^ 2)) r)|
      ≤ 4 * Real.pi * (Bu * R ^ 3 / 3 + Bu ^ 2 * R / 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (4 * Real.pi / 3) * (Bu * R ^ 3) + (2 * Real.pi) * (Bu ^ 2 * R) := e1
    _ ≤ 10 * (Bu * c1) + 10 * (Bu ^ 2 * c1) := add_le_add h1 h2
    _ = 10 * (Bu + Bu ^ 2) * c1 := e2.symm

end Work.BoseB6
