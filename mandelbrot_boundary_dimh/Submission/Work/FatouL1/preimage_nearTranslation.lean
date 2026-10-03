import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouL1.preimage_of_re_ge

/-!
# Unique preimage of `z₀` for a near-translation `F` on `U`

Let `F` be holomorphic on an open set `U` containing the closed ball `B̄(z₀ - 1, 1/32)`, with
`‖F z - (z + 1)‖ ≤ 1/32` and `‖F' z - 1‖ ≤ 1/32` on `U`.  Then `F` attains the value `z₀` at
exactly one point of that ball.

* **Existence** is the quantitative inverse-function step `exists_preimage_in_closedBall`
  (Shishikura A.2.1(i)): the map `𝒯 w = z₀ - F w + w` is a `1/32`-contraction of the ball into
  itself, so it has a fixed point there, and a fixed point is exactly a solution of `F w = z₀`.
* **Uniqueness** is the mean value inequality applied to `H z = F z - z`, whose derivative
  `F' - 1` has norm `≤ 1/32`: two solutions in the ball satisfy
  `‖w - y‖ = ‖H w - H y‖ ≤ (1/32) · ‖w - y‖`, forcing `w = y`.
-/

set_option linter.unusedVariables false

namespace Work.FatouL1

/-- **Uniqueness of the preimage.**  If `F` is holomorphic on `U`, `‖deriv F - 1‖ ≤ 1/32` on
`U`, and the closed ball `B̄(z₀ - 1, 1/32)` is contained in `U`, then `F` takes the value `z₀` at
most once on that ball.

The map `H z = F z - z` has derivative `deriv F z - 1`, of norm `≤ 1/32`, hence is
`1/32`-Lipschitz on the (convex) ball by the mean value inequality.  Two points `w, y` of the ball
with `F w = F y = z₀` therefore satisfy `w - y = -(H w - H y)` with
`‖H w - H y‖ ≤ (1/32) ‖w - y‖`, so `‖w - y‖ ≤ (1/32) ‖w - y‖` and `w = y`. -/
theorem preimage_nearTranslation_unique {F : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hd : DifferentiableOn ℂ F U)
    (h2 : ∀ z ∈ U, ‖deriv F z - 1‖ ≤ 1 / 32)
    (hball : Metric.closedBall (z₀ - 1) (1 / 32) ⊆ U)
    {w y : ℂ} (hw : w ∈ Metric.closedBall (z₀ - 1) (1 / 32))
    (hy : y ∈ Metric.closedBall (z₀ - 1) (1 / 32))
    (hFw : F w = z₀) (hFy : F y = z₀) : w = y := by
  -- `F` is differentiable at every point of the ball (the ball lies in the open set `U`)
  have hFdat : ∀ t ∈ Metric.closedBall (z₀ - 1) (1 / 32), DifferentiableAt ℂ F t :=
    fun t ht => (hd t (hball ht)).differentiableAt (hU.mem_nhds (hball ht))
  -- differentiability of `H z = F z - z` on the ball
  have hHdat : ∀ t ∈ Metric.closedBall (z₀ - 1) (1 / 32),
      DifferentiableAt ℂ (fun z : ℂ => F z - z) t :=
    fun t ht => (hFdat t ht).sub differentiableAt_id
  -- its derivative is `deriv F - 1`
  have hHderiv : ∀ t ∈ Metric.closedBall (z₀ - 1) (1 / 32),
      deriv (fun z : ℂ => F z - z) t = deriv F t - 1 := by
    intro t ht
    have hsub : (fun z : ℂ => F z - z) = F - (fun z : ℂ => z) := by funext z; rfl
    rw [hsub, deriv_sub (f := F) (g := fun z : ℂ => z) (hFdat t ht) differentiableAt_id,
      show deriv (fun z : ℂ => z) t = 1 from deriv_id t]
  -- hence `‖deriv H‖ ≤ 1/32` on the ball
  have hbound : ∀ t ∈ Metric.closedBall (z₀ - 1) (1 / 32),
      ‖deriv (fun z : ℂ => F z - z) t‖₊ ≤ (1 / 32 : NNReal) := by
    intro t ht
    have h' : ‖deriv (fun z : ℂ => F z - z) t‖ ≤ 1 / 32 := by
      rw [hHderiv t ht]; exact h2 t (hball ht)
    exact_mod_cast h'
  -- mean value inequality: `H` is `1/32`-Lipschitz on the convex ball
  have hlip : LipschitzOnWith (1 / 32 : NNReal) (fun z : ℂ => F z - z)
      (Metric.closedBall (z₀ - 1) (1 / 32)) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℂ) (G := ℂ) (f := fun z : ℂ => F z - z)
      (s := Metric.closedBall (z₀ - 1) (1 / 32)) hHdat hbound
      (convex_closedBall (z₀ - 1) (1 / 32))
  have hle : dist w y ≤ (1 / 32 : ℝ) * dist w y := by
    have h1 : dist ((fun z : ℂ => F z - z) w) ((fun z : ℂ => F z - z) y)
        ≤ ((1 / 32 : NNReal) : ℝ) * dist w y := hlip.dist_le_mul w hw y hy
    have hc : ((1 / 32 : NNReal) : ℝ) = 1 / 32 := by norm_num
    rw [hc] at h1
    have hdiff : (fun z : ℂ => F z - z) w - (fun z : ℂ => F z - z) y = y - w := by
      change (F w - w) - (F y - y) = y - w
      rw [hFw, hFy]
      ring
    rw [dist_eq_norm, hdiff, norm_sub_rev, ← dist_eq_norm] at h1
    exact h1
  -- `‖w - y‖ ≤ (1/32) ‖w - y‖` forces `w = y`
  rw [dist_eq_norm] at hle
  have hzero : ‖w - y‖ = 0 := by nlinarith [hle, norm_nonneg (w - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- **Near-translation preimage.**  Let `F` be holomorphic on an open convex set `U` and satisfy
`‖F z - (z + 1)‖ ≤ 1/32` and `‖F' z - 1‖ ≤ 1/32` on `U`, and suppose the closed ball
`B̄(z₀ - 1, 1/32)` is contained in `U`.  Then `F` has exactly one preimage of `z₀` in that ball.

Existence is `exists_preimage_in_closedBall` (Banach fixed point for `𝒯 w = z₀ - F w + w`);
uniqueness is `preimage_nearTranslation_unique`. -/
theorem preimage_nearTranslation {F : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hd : DifferentiableOn ℂ F U)
    (h1 : ∀ z ∈ U, ‖F z - (z + 1)‖ ≤ 1 / 32) (h2 : ∀ z ∈ U, ‖deriv F z - 1‖ ≤ 1 / 32)
    (hball : Metric.closedBall (z₀ - 1) (1 / 32) ⊆ U) :
    ∃! w : ℂ, w ∈ Metric.closedBall (z₀ - 1) (1 / 32) ∧ F w = z₀ := by
  obtain ⟨w, hwball, hFw⟩ := exists_preimage_in_closedBall hU hball hd h1 h2
  exact ⟨w, ⟨hwball, hFw⟩,
    fun y hy => (preimage_nearTranslation_unique hU hd h2 hball hwball hy.1 hFw hy.2).symm⟩

end Work.FatouL1
