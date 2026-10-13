import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.eigenFTCAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/eigenFTCPoleDefs` — the left-half companions of `Gd`, `Ki`

The file `WeakPureAux/eigenFTCAux` carries the *right-half* running quantities of the
`(Dfun, Rfun)` system of `Lzero1 u = mu * u`:

* `Gd u θ = ∫_{π/4}^{θ} |Rfun u s| · ew s ds` (the running `σ|u|`-mass) and
* `Ki θ = ∫_{π/4}^{θ} ek s ds` (the running kernel of the `Rfun` equation),

together with the running bounds `Dfun_run_bound`, `Rfun_run_bound` for `θ ∈ [π/4, π/2)`.

This file adds the two mirror definitions for the *left* half `θ ∈ (0, π/4]`,
`GdL u θ = ∫_{θ}^{π/4} |Rfun u s| · ew s ds` and `Kl θ = ∫_{θ}^{π/4} ek s ds`, and the
elementary bounds (`ew ≤ 1`, `ew = O(t³)` near `π/2`, `ew = O(θ²)` near `0`, and hence
`ew · Ki`, `ew · Kl` bounded) that turn the running bounds of the two halves into
constant-coefficient Grönwall inequalities.
-/

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-- The *left-half* running `σ|u|`-mass: `GdL u θ = ∫_θ^{π/4} |Rfun u s| · ew s ds`. -/
def GdL (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in θ..(Real.pi / 4), |LzeroGrowth.Rfun u s| * ew s

/-- The *left-half* running kernel: `Kl θ = ∫_θ^{π/4} ek s ds`. -/
def Kl (θ : ℝ) : ℝ := ∫ s in θ..(Real.pi / 4), ek s

/-- The weight `ew` is bounded by `1`. -/
theorem ew_le_one (θ : ℝ) : ew θ ≤ 1 := by
  have hab : |Real.sin (2 * θ)| * |Real.sin θ| ≤ 1 := by
    have ha : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one (2 * θ)
    have hb : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hd : 0 ≤ |Real.sin θ| := abs_nonneg _
    calc |Real.sin (2 * θ)| * |Real.sin θ| ≤ 1 * |Real.sin θ| :=
          mul_le_mul_of_nonneg_right ha hd
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 1 := by ring
  have hc : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have h : |ew θ| ≤ 1 := by
    rw [ew, Work.Elliptic.sinCos2, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    calc |Real.sin (2 * θ)| * (|Real.sin θ| * Real.cos θ ^ 2)
        = (|Real.sin (2 * θ)| * |Real.sin θ|) * Real.cos θ ^ 2 := by ring
      _ ≤ 1 * 1 := mul_le_mul hab hc (sq_nonneg _) (by norm_num)
      _ = 1 := by ring
  linarith [le_abs_self (ew θ), h]

/-- On the right half, `ew θ ≤ 2 (π/2 - θ)³`. -/
theorem ew_le_two_mul_cube_of_right {θ : ℝ}
    (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) : ew θ ≤ 2 * (Real.pi / 2 - θ) ^ 3 := by
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hsin2 : 0 < Real.sin (2 * θ) :=
    LzeroGrowth.sin_two_pos ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hcos0 : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le
  have hcos2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have h1 : ew θ ≤ Real.sin (2 * θ) * Real.cos θ ^ 2 := by
    rw [ew, Work.Elliptic.sinCos2]
    have hsin : Real.sin θ ≤ 1 := Real.sin_le_one θ
    calc Real.sin (2 * θ) * (Real.sin θ * Real.cos θ ^ 2)
        ≤ Real.sin (2 * θ) * (1 * Real.cos θ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsin hcos2) hsin2.le
      _ = Real.sin (2 * θ) * Real.cos θ ^ 2 := by ring
  have hsin2le : Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
    have h2θ : 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) := by ring
    rw [h2θ, Real.sin_pi_sub]
    exact Real.sin_le (by linarith [ht0])
  have hcosle : Real.cos θ ≤ Real.pi / 2 - θ := by
    rw [← Real.sin_pi_div_two_sub θ]
    exact Real.sin_le ht0.le
  calc ew θ ≤ Real.sin (2 * θ) * Real.cos θ ^ 2 := h1
    _ ≤ (2 * (Real.pi / 2 - θ)) * (Real.pi / 2 - θ) ^ 2 :=
        mul_le_mul hsin2le (pow_le_pow_left₀ hcos0 hcosle 2) hcos2 (by linarith [ht0])
    _ = 2 * (Real.pi / 2 - θ) ^ 3 := by ring

/-- On the left half, `ew θ ≤ 2 θ²`. -/
theorem ew_le_two_mul_sq_of_left {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) : ew θ ≤ 2 * θ ^ 2 := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    LzeroGrowth.sin_two_pos ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hsinθle : Real.sin θ ≤ θ := Real.sin_le hθ.1.le
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hsin2le : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith [hθ.1])
  calc ew θ = Real.sin (2 * θ) * (Real.sin θ * Real.cos θ ^ 2) := by
        rw [ew, Work.Elliptic.sinCos2]
    _ ≤ Real.sin (2 * θ) * (θ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hsinθle hcos2 (sq_nonneg _) hθ.1.le) hsin2.le
    _ = Real.sin (2 * θ) * θ := by ring
    _ ≤ (2 * θ) * θ := mul_le_mul_of_nonneg_right hsin2le hθ.1.le
    _ = 2 * θ ^ 2 := by ring

/-- `Kl θ ≥ 0` on `(0, π/4]`. -/
theorem Kl_nonneg {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) : 0 ≤ Kl θ := by
  have h := intervalIntegral.integral_mono_on hθ.2
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume θ (Real.pi / 4))
    ((continuousOn_ek hθ.1 (by linarith [Real.pi_pos, hθ.2])).intervalIntegrable_of_Icc hθ.2)
    (fun s hs => ek_nonneg ⟨by linarith [hθ.1, hs.1],
      by linarith [hθ.2, hs.2, Real.pi_pos]⟩)
  simpa [Kl] using h

/-- `GdL u θ ≥ 0` on `(0, π/4]`. -/
theorem GdL_nonneg {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) : 0 ≤ GdL u θ := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have h := intervalIntegral.integral_mono_on hθ.2
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume θ (Real.pi / 4))
    ((continuousOn_absRfun_mul_ew hu ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      ⟨hq0, by linarith [Real.pi_pos]⟩).intervalIntegrable_of_Icc hθ.2)
    (fun s hs => mul_nonneg (abs_nonneg _) (ew_nonneg ⟨by linarith [hθ.1, hs.1],
      by linarith [hθ.2, hs.2, Real.pi_pos]⟩))
  simpa [GdL] using h

/-- `GdL u (π/4) = 0`. -/
theorem GdL_self (u : ℝ → ℝ) : GdL u (Real.pi / 4) = 0 := by
  simp [GdL]

/-- `Kl (π/4) = 0`. -/
theorem Kl_self : Kl (Real.pi / 4) = 0 := by
  simp [Kl]

/-- `ew · Ki` is bounded on the right half. -/
theorem ew_mul_Ki_le {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    ew θ * Ki θ ≤ Real.pi ^ 4 / 128 := by
  have ht : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hKi : Ki θ ≤ (Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2 := by
    simpa only [Ki, ek] using lzeroGrowthKernelRight hθ
  have hKi0 : 0 ≤ Ki θ := Ki_nonneg hθ.1 hθ.2
  have hew : ew θ ≤ 2 * (Real.pi / 2 - θ) ^ 3 := ew_le_two_mul_cube_of_right hθ
  have hstep : ew θ * Ki θ
      ≤ 2 * (Real.pi / 2 - θ) ^ 3 * ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2) :=
    mul_le_mul hew hKi hKi0 (by positivity)
  have hsimp : 2 * (Real.pi / 2 - θ) ^ 3 * ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2)
      = (Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) := by
    field_simp
    ring
  have htle : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith [hθ.1]
  have hfinal : (Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ≤ Real.pi ^ 4 / 128 := by
    have h := mul_le_mul_of_nonneg_left htle (show (0 : ℝ) ≤ Real.pi ^ 3 / 32 by positivity)
    linarith [h]
  rw [hsimp] at hstep
  linarith [hstep, hfinal]

/-- `ew · Kl` is bounded on the left half. -/
theorem ew_mul_Kl_le {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) :
    ew θ * Kl θ ≤ Real.pi ^ 3 / 16 := by
  have hKl : Kl θ ≤ (Real.pi ^ 2 / 8) / θ := by
    simpa only [Kl, ek] using lzeroGrowthKernelLeft hθ
  have hKl0 : 0 ≤ Kl θ := Kl_nonneg hθ
  have hew : ew θ ≤ 2 * θ ^ 2 := ew_le_two_mul_sq_of_left hθ
  have hstep : ew θ * Kl θ ≤ 2 * θ ^ 2 * ((Real.pi ^ 2 / 8) / θ) :=
    mul_le_mul hew hKl hKl0 (by positivity)
  have hsimp : 2 * θ ^ 2 * ((Real.pi ^ 2 / 8) / θ) = (Real.pi ^ 2 / 4) * θ := by
    field_simp
    ring
  have hθle : θ ≤ Real.pi / 4 := hθ.2
  have hfinal : (Real.pi ^ 2 / 4) * θ ≤ Real.pi ^ 3 / 16 := by
    have h := mul_le_mul_of_nonneg_left hθle (show (0 : ℝ) ≤ Real.pi ^ 2 / 4 by positivity)
    linarith [h]
  rw [hsimp] at hstep
  linarith [hstep, hfinal]

end

end Work.FTS.EllipticEst.H2W.WeakPureAux
