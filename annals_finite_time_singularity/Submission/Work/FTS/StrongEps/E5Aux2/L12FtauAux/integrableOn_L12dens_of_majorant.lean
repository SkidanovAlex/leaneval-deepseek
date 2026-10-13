import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the `L₁₂`-density from a radial majorant

`Work.FM.L12dens K h s = ∫_{θ ∈ [0,π/2]} K θ · h s θ / s` with `K θ = 3 sin θ cos²θ`.  Since
`K ≥ 0` on `[0,π/2]` and `∫_{[0,π/2]} K = 1`, the elementary bound

`|L12dens K h s| ≤ (∫_θ |K θ|) · Maj s / s = Maj s / s`   (`s > 0`)

holds as soon as `|h s θ| ≤ Maj s` on the *open* interval `(0,π/2)` — the endpoints `θ = 0`,
`θ = π/2` are harmless because `K` vanishes there.  Hence, if `Maj s / s` is integrable on
`(0,∞)` and `h` is continuous on the open quadrant (which gives a.e. strong measurability of
the density, `Work.FTS.StrongEps.E5Aux2.aesm_L12dens_of_contOn`), then so is `L12dens K h`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux2.L12FtauAux

/-! ## Elementary angular facts about `K θ = 3 sin θ cos²θ` -/

/-- The angular weight `K` is continuous. -/
theorem continuous_K : Continuous Work.Spaces.K := by
  rw [show Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 from by
    funext θ; rw [Work.Spaces.K]]
  exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)

/-- `K ≥ 0` on `Iθ = [0,π/2]`. -/
theorem K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  exact mul_nonneg (mul_nonneg (by norm_num)
    (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])))
    (sq_nonneg _)

/-- `K` vanishes at the endpoints of `Iθ`: if `θ ∈ Iθ` but `θ ∉ (0,π/2)` then `θ` is `0` or
`π/2`, and `K` vanishes there. -/
theorem K_eq_zero_of_mem_Iθ_of_not_mem_Ioo {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Ioo (0 : ℝ) (Real.pi / 2)) : Work.Spaces.K θ = 0 := by
  have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
    rw [Set.mem_Ioo, not_and_or] at h
    rcases h with h | h
    · left; exact le_antisymm (not_lt.mp h) hθ.1
    · right; exact le_antisymm hθ.2 (not_lt.mp h)
  rcases hcases with rfl | rfl
  · rw [Work.Spaces.K, Real.sin_zero]; ring
  · rw [Work.Spaces.K, Real.cos_pi_div_two]; ring

/-- `-cos³` is a primitive of `K`. -/
theorem hasDerivAt_neg_cos_cube (x : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.cos t) ^ 3) (Work.Spaces.K x) x := by
  have h1 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
      (3 * Real.cos x ^ 2 * -Real.sin x) x :=
    (Real.hasDerivAt_cos x).pow 3
  convert h1.neg using 1
  rw [Work.Spaces.K]; ring

/-- `∫_{Iθ} K θ = 1` (fundamental theorem of calculus with primitive `-cos³`). -/
theorem integral_K_Iθ : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ) = 1 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  have hInt : (∫ θ in (0 : ℝ)..(Real.pi / 2), Work.Spaces.K θ)
      = (fun t : ℝ => -(Real.cos t) ^ 3) (Real.pi / 2)
        - (fun t : ℝ => -(Real.cos t) ^ 3) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => -(Real.cos t) ^ 3)
      (fun x _ => hasDerivAt_neg_cos_cube x) (continuous_K.intervalIntegrable _ _)
  rw [hInt]
  norm_num [Real.cos_pi_div_two, Real.cos_zero]

/-- `∫_{Iθ} |K θ| = 1`. -/
theorem integral_abs_K_Iθ : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|) = 1 := by
  have hms : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  rw [MeasureTheory.setIntegral_congr_fun hms
    (fun θ hθ => abs_of_nonneg (K_nonneg_of_mem_Iθ hθ)), integral_K_Iθ]

/-! ## The main theorem -/

theorem integrableOn_L12dens_of_majorant {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ}
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hMaj : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K h) (Set.Ioi 0) := by
  -- the angular comparison function is integrable on the compact interval `Iθ`
  have hIntMaj : ∀ s ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Work.Spaces.K θ| * Maj s / s) Work.Spaces.Iθ := by
    intro s _
    have hc : Continuous fun θ : ℝ => |Work.Spaces.K θ| * Maj s / s :=
      (continuous_K.abs.mul continuous_const).div_const s
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  -- the pointwise domination `|L12dens K h s| ≤ Maj s / s` for `s > 0`
  have hle : ∀ s ∈ Set.Ioi (0 : ℝ),
      |Work.FM.L12dens Work.Spaces.K h s| ≤ Maj s / s := by
    intro s hs
    have hs0 : 0 < s := hs
    show |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s| ≤ Maj s / s
    calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s|
        = ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ * h s θ / s‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ| * Maj s / s := by
          refine MeasureTheory.setIntegral_mono_of_nonneg (fun θ _ => norm_nonneg _)
            (fun θ hθ => ?_) (hIntMaj s hs)
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hs0]
          by_cases hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
          · exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hbd s hs θ hmem) (abs_nonneg _)) hs0.le
          · rw [K_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hmem]; simp
      _ = (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ|) * (Maj s / s) := by
          rw [show (fun θ => |Work.Spaces.K θ| * Maj s / s)
              = (fun θ => |Work.Spaces.K θ| * (Maj s / s)) from by funext θ; ring]
          exact MeasureTheory.integral_mul_const _ _
      _ = Maj s / s := by rw [integral_abs_K_Iθ, one_mul]
  refine MeasureTheory.Integrable.mono' hMaj
    (Work.FTS.StrongEps.E5Aux2.aesm_L12dens_of_contOn hh) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall (fun s hs => ?_)
  rw [Real.norm_eq_abs]
  exact hle s hs

end Work.FTS.StrongEps.E5Aux2.L12FtauAux
