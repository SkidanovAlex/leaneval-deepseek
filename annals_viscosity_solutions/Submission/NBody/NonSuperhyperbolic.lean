import Submission.NBody.Minimizer
import Submission.NBody.HolderEstimate
import Mathlib

/-!
# `h`-minimisers are not superhyperbolic

The first step in the proof of `thm-calib.direct.horo` of Maderna–Venturelli: an `h`-minimiser
grows at most linearly in time.  Combining the Cauchy–Schwarz lower bound of `lema-time.estim`
(`IsHMinimizer.ofReal_tau_le`) with the Hölder estimate for `φ_h`
(`thm-phih.estim`) shows that a minimiser which travelled a distance `r` in time `T` must satisfy
`r ≤ 2√(α + hβ)·T/c`, where `c` is a positive lower bound for the masses.

Everything here is fully proved (the Hölder estimate enters as an explicit hypothesis).
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **An `h`-minimiser is not superhyperbolic.**  If `φ_h` satisfies the Hölder estimate with
constants `α, β`, the masses are bounded below by `c > 0` and `0 ≤ h`, then over a time `T > 0`
an `h`-minimiser travels a distance at most `max 1 (2√(α + hβ)·T/c)`. -/
theorem norm_sub_le_of_isHMinimizer {m : Fin N → ℝ} {h α β : ℝ} (hh : 0 ≤ h) (hα : 0 ≤ α) (hβ : 0 < β)
    (hest : ∀ x y : EN E N,
      actionPot m h x y ≤ ENNReal.ofReal (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2)))
    {c : ℝ} (hc : 0 < c) (hmc : ∀ i, c ≤ m i)
    {γ : ℝ → EN E N} {T : ℝ} (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 T) (hmin : IsHMinimizer m h γ 0 T) :
    ‖γ T - γ 0‖ ≤ max 1 (2 * Real.sqrt (α + h * β) * T / c) := by
  have hlow := IsHMinimizer.ofReal_tau_le (m := m) (h := h) (x := γ 0) (y := γ T) (τ := T)
    (γ := γ) hac rfl rfl hmin hc hmc hh hT
  have hhi := hest (γ 0) (γ T)
  have hchain : (1 / 2) * c * ‖γ 0 - γ T‖ ^ 2 / T + h * T
      ≤ Real.sqrt (α * ‖γ 0 - γ T‖ + h * β * ‖γ 0 - γ T‖ ^ 2) := by
    have h2 : (0:ℝ) ≤ Real.sqrt (α * ‖γ 0 - γ T‖ + h * β * ‖γ 0 - γ T‖ ^ 2) := Real.sqrt_nonneg _
    have h1 : (0:ℝ) ≤ (1 / 2) * c * ‖γ 0 - γ T‖ ^ 2 / T + h * T := by positivity
    have h3 : ENNReal.ofReal ((1 / 2) * c * ‖γ 0 - γ T‖ ^ 2 / T + h * T)
        ≤ ENNReal.ofReal (Real.sqrt (α * ‖γ 0 - γ T‖ + h * β * ‖γ 0 - γ T‖ ^ 2)) :=
      hlow.trans hhi
    exact (ENNReal.ofReal_le_ofReal_iff h2).mp h3
  have hmain : ∀ r : ℝ, 0 ≤ r →
      (1 / 2) * c * r ^ 2 / T + h * T ≤ Real.sqrt (α * r + h * β * r ^ 2) →
      r ≤ max 1 (2 * Real.sqrt (α + h * β) * T / c) := by
    intro r hr0 hineq
    rcases le_total r 1 with hr1 | hr1
    · exact hr1.trans (le_max_left 1 _)
    · refine le_trans ?_ (le_max_right 1 _)
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
      have hstep : Real.sqrt (α * r + h * β * r ^ 2) ≤ Real.sqrt (α + h * β) * r := by
        have hβ0 : 0 ≤ h * β := mul_nonneg hh hβ.le
        have hle : α * r + h * β * r ^ 2 ≤ (α + h * β) * r ^ 2 := by
          nlinarith [mul_nonneg hα hr0, sub_nonneg.mpr hr1, sq_nonneg r, hr0]
        calc Real.sqrt (α * r + h * β * r ^ 2)
            ≤ Real.sqrt ((α + h * β) * r ^ 2) := Real.sqrt_le_sqrt hle
          _ = Real.sqrt (α + h * β) * r := by
              rw [Real.sqrt_mul (by linarith : (0:ℝ) ≤ α + h * β), Real.sqrt_sq hr0]
      have hkey : (1 / 2) * c * r ^ 2 / T ≤ Real.sqrt (α + h * β) * r := by
        have h4 : 0 ≤ h * T := mul_nonneg hh hT.le
        have h5 := hineq.trans hstep
        linarith
      have hdiv : (1 / 2) * c * r / T ≤ Real.sqrt (α + h * β) := by
        have h3 : (1 / 2) * c * r ^ 2 / T = ((1 / 2) * c * r / T) * r := by ring
        rw [h3] at hkey
        exact le_of_mul_le_mul_right hkey hrpos
      rw [le_div_iff₀ hc]
      have h2 : (1 / 2) * c * r ≤ Real.sqrt (α + h * β) * T := by
        rw [div_le_iff₀ hT] at hdiv
        linarith
      linarith
  rw [norm_sub_rev] at hchain
  exact hmain _ (norm_nonneg _) hchain

end Submission.NBody
