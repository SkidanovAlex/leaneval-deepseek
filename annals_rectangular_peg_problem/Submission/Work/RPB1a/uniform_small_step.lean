import Mathlib
import Submission.Work.RPB1a.interval_step_bound

/-!
# RPB1a: the uniform small-step (speed) bound

`Work.RPB1a.uniform_small_step` is the C¹ "speed bound" used by the analytic route to node `B1`
(`RECTPEG_B1_LEAD.md`): a `C¹` loop `u : ℝ → ℂ` whose derivative is bounded below in norm by
`m > 0` on `[0, 2π]` moves by at least `(m/2)|h|` over any step `h` of length below some uniform
threshold `δ ≤ π`.

The proof splits into two independent pieces.

* `Submission.Work.RPB1a.interval_step_bound` (a separate, Mathlib-level lemma): the single-interval
  estimate.  Writing `u(t+h) − u t = ∫_t^{t+h} deriv u`, splitting the integrand as
  `deriv u t + (deriv u y − deriv u t)`, and using the reverse triangle inequality, the constant part
  contributes `≥ |h|·m` and the fluctuation `≤ (m/2)|h|`, whence `(m/2)|h|`.
* `exists_delta_deriv_close` below: the uniform-continuity bookkeeping.  On the compact window
  `[-π, 3π]` the continuous `deriv u` is uniformly continuous, so there is `δ > 0` (with `δ ≤ π`)
  such that for `t ∈ [0, 2π]`, `|h| ≤ δ` and `y ∈ uIcc t (t+h)` one has
  `‖deriv u y − deriv u t‖ ≤ m/2`.

`uniform_small_step` is then the immediate assembly of the two.
-/

set_option autoImplicit false

open Set Metric

namespace Work.RPB1a

/-- Uniform-continuity bookkeeping: because `deriv u` is continuous, it is uniformly continuous on
the compact window `Icc (-π) (3π)` that contains every segment `uIcc t (t+h)` with `t ∈ [0, 2π]`
and `|h| ≤ π`.  Hence there is `δ > 0`, `δ ≤ π`, such that the derivative is within `m/2` of
`deriv u t` all along such a segment. -/
private lemma exists_delta_deriv_close (u : ℝ → ℂ) (hcu : Continuous (deriv u))
    {m : ℝ} (hm : 0 < m) :
    ∃ δ > 0, δ ≤ Real.pi ∧ ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∀ h : ℝ, |h| ≤ δ →
      ∀ y ∈ Set.uIcc t (t + h), ‖deriv u y - deriv u t‖ ≤ m / 2 := by
  have hK : IsCompact (Set.Icc (-Real.pi) (3 * Real.pi)) := isCompact_Icc
  have hUC := hK.uniformContinuousOn_of_continuous hcu.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hUC (m / 2) (by linarith)
  refine ⟨min (δ₀ / 2) Real.pi, lt_min (by linarith) Real.pi_pos, min_le_right _ _, ?_⟩
  intro t ht h hh y hy
  have hδle : min (δ₀ / 2) Real.pi ≤ δ₀ / 2 := min_le_left _ _
  have hδpi : min (δ₀ / 2) Real.pi ≤ Real.pi := min_le_right _ _
  have hhpi : |h| ≤ Real.pi := le_trans hh hδpi
  have htK : t ∈ Set.Icc (-Real.pi) (3 * Real.pi) := by
    refine ⟨by linarith [Real.pi_pos, ht.1], by linarith [Real.pi_pos, ht.2]⟩
  have hyK : y ∈ Set.Icc (-Real.pi) (3 * Real.pi) := by
    rcases (Set.mem_uIcc.mp hy) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [Real.pi_pos, ht.1], by linarith [ht.2, (abs_le.mp hhpi).2]⟩
    · exact ⟨by linarith [Real.pi_pos, ht.1, (abs_le.mp hhpi).1], by linarith [Real.pi_pos, ht.2]⟩
  have hyt : |y - t| ≤ |h| := by
    rcases (Set.mem_uIcc.mp hy) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hh0 : 0 ≤ h := by linarith
      rw [abs_of_nonneg (by linarith : 0 ≤ y - t), abs_of_nonneg hh0]
      linarith
    · have hh0 : h ≤ 0 := by linarith
      rw [abs_of_nonpos (by linarith : y - t ≤ 0), abs_of_nonpos hh0]
      linarith
  have hdist : dist y t < δ₀ := by
    rw [dist_eq_norm, Real.norm_eq_abs]
    calc |y - t| ≤ |h| := hyt
      _ ≤ min (δ₀ / 2) Real.pi := hh
      _ ≤ δ₀ / 2 := hδle
      _ < δ₀ := by linarith
  have hres := hδ₀ y hyK t htK hdist
  rw [dist_eq_norm] at hres
  exact le_of_lt hres

theorem uniform_small_step (u : ℝ → ℂ) (hu : Differentiable ℝ u) (hcu : Continuous (deriv u))
    {m : ℝ} (hm : 0 < m)
    (hmle : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), m ≤ ‖deriv u t‖) :
    ∃ δ > 0, δ ≤ Real.pi ∧ ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∀ h : ℝ, |h| ≤ δ →
      (m / 2) * |h| ≤ ‖u (t + h) - u t‖ := by
  obtain ⟨δ, hδpos, hδle, hδ⟩ := exists_delta_deriv_close u hcu hm
  exact ⟨δ, hδpos, hδle, fun t ht h hh =>
    interval_step_bound u hu hcu (hmle t ht) (hδ t ht h hh)⟩

end Work.RPB1a
