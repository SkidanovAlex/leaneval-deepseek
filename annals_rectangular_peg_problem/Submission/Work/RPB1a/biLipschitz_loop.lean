import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPA3.periodic_mem_Icc
import Submission.Work.RPB.B5.periodic_norm_min_pos
import Submission.Work.RPB1a.periodic_reduce
import Submission.Work.RPB1a.deriv_min_pos
import Submission.Work.RPB1a.uniform_small_step
import Submission.Work.RPB1a.uniform_large_step

set_option autoImplicit false

open Complex Set Metric
open scoped ContDiff Real

noncomputable section

namespace Work.RPB1a

/-- **Uniform bi-Lipschitz lower bound for a smooth embedded loop.**

If `u : ℝ → ℂ` is `C^∞`, `2π`-periodic, injective modulo `2π` and immersed, then the chord lengths
of `u` control the parameter distance: there is `c > 0` with `c * |h| ≤ ‖u (t + h) - u t‖` for all
`t` and all `|h| ≤ π`.

The proof combines four independent estimates.

* `Work.RPB1a.deriv_min_pos`: the derivative is continuous and nowhere zero, so on the compact
  period `[0, 2π]` its norm has a strictly positive minimum `m`.
* `Work.RPB1a.uniform_small_step`: for `|h|` below a uniform threshold `δ` (chosen from the modulus
  of uniform continuity of `deriv u` on the compact window `[-π, 3π]`), the mean value estimate
  `‖u (t + h) - u t - h • deriv u t‖ ≤ (m / 2) |h|` together with `m ≤ ‖deriv u t‖` gives
  `(m / 2) |h| ≤ ‖u (t + h) - u t‖` for `t ∈ [0, 2π]`.
* `Work.RPB1a.uniform_large_step`: on the compact set `[0, 2π] × {δ ≤ |h| ≤ π}` the continuous,
  nowhere zero function `(t, h) ↦ ‖u (t + h) - u t‖` attains a strictly positive minimum `μ`; there
  `(μ / π) |h| ≤ ‖u (t + h) - u t‖`.
* `Work.RPB1a.periodic_reduce`: an arbitrary `t` is shifted by an integer multiple of `2π` into
  `[0, 2π]` without changing any of the chords through it.

Taking `c := min (m / 2) (μ / π) > 0` and doing the case distinction `|h| ≤ δ` / `δ ≤ |h|` gives the
claim. -/
theorem biLipschitz_loop (u : ℝ → ℂ) (hu : Work.RPB1a.IsSmoothLoop u) :
    ∃ c > 0, ∀ t h : ℝ, |h| ≤ Real.pi → c * |h| ≤ ‖u (t + h) - u t‖ := by
  have hcd : ContDiff ℝ ∞ u := hu.1
  have hper : ∀ t : ℝ, u (t + 2 * Real.pi) = u t := hu.2.1
  have hinj : ∀ t t' : ℝ, u t = u t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m := hu.2.2.1
  have hreg : ∀ t : ℝ, deriv u t ≠ 0 := hu.2.2.2
  have hcont : Continuous u := hcd.continuous
  have hdiff : Differentiable ℝ u := hcd.differentiable (by norm_num)
  have hcderiv : Continuous (deriv u) := hcd.continuous_deriv (by norm_num)
  obtain ⟨m, hmpos, hmle⟩ := deriv_min_pos u hcderiv hreg
  obtain ⟨δ, hδpos, hδπ, hsmall⟩ := uniform_small_step u hdiff hcderiv hmpos hmle
  obtain ⟨μ, hμpos, hlarge⟩ := uniform_large_step u hcont hinj hδpos
  refine ⟨min (m / 2) (μ / Real.pi), lt_min (by linarith) (div_pos hμpos Real.pi_pos), ?_⟩
  intro t h hh
  obtain ⟨t₀, ht₀, hred⟩ := periodic_reduce u hper t
  rw [hred h]
  by_cases hcase : |h| ≤ δ
  · calc min (m / 2) (μ / Real.pi) * |h| ≤ (m / 2) * |h| :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg h)
      _ ≤ ‖u (t₀ + h) - u t₀‖ := hsmall t₀ ht₀ h hcase
  · have h2 : δ ≤ |h| := le_of_lt (not_le.mp hcase)
    have hμ := hlarge t₀ ht₀ h h2 hh
    calc min (m / 2) (μ / Real.pi) * |h| ≤ (μ / Real.pi) * |h| :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg h)
      _ ≤ (μ / Real.pi) * Real.pi :=
          mul_le_mul_of_nonneg_left hh (div_nonneg hμpos.le Real.pi_pos.le)
      _ = μ := div_mul_cancel₀ μ (ne_of_gt Real.pi_pos)
      _ ≤ ‖u (t₀ + h) - u t₀‖ := hμ

end Work.RPB1a
