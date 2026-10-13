import Mathlib
import Submission.Work.WilE2.eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_left

open Filter Set Metric

namespace Work.WilE2

/-- **Local vanishing for a Grönwall differential inequality.**

If `z` is differentiable near `t₀` with `z t₀ = 0` and the derivative is eventually bounded by
`‖z' t‖ ≤ C * ‖z t‖`, then `z` vanishes on a neighbourhood of `t₀`.  This is the local form of
Grönwall's lemma with zero initial data: it is applied once forward on `[t₀, t]` (Mathlib's
`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`) and once backward on `[t, t₀]` (the
mirrored `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_left`). -/
lemma eq_zero_of_eventually_hasDerivAt_bound_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z z' : ℝ → E} {C : ℝ} {t₀ : ℝ} (hz0 : z t₀ = 0)
    (hdiff : ∀ᶠ t in nhds t₀, HasDerivAt z (z' t) t)
    (hbound : ∀ᶠ t in nhds t₀, ‖z' t‖ ≤ C * ‖z t‖) :
    ∀ᶠ t in nhds t₀, z t = 0 := by
  -- Extract a ball on which both eventual statements hold simultaneously.
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (hdiff.and hbound)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds t₀ hδpos) ?_
  intro t ht
  have htδ : |t - t₀| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using ht
  -- `[t₀, t] ⊆ ball` (forward interval)
  have hsub_fwd : Icc t₀ t ⊆ Metric.ball t₀ δ := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : 0 ≤ x - t₀ := by linarith [hx.1]
    have h2 : 0 ≤ t - t₀ := by linarith [hx.1, hx.2]
    have : |x - t₀| ≤ |t - t₀| := by
      rw [abs_of_nonneg h1, abs_of_nonneg h2]; linarith [hx.2]
    exact lt_of_le_of_lt this htδ
  -- `[t, t₀] ⊆ ball` (backward interval)
  have hsub_bwd : Icc t t₀ ⊆ Metric.ball t₀ δ := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : x - t₀ ≤ 0 := by linarith [hx.2]
    have h2 : t - t₀ ≤ 0 := by linarith [hx.1, hx.2]
    have : |x - t₀| ≤ |t - t₀| := by
      rw [abs_of_nonpos h1, abs_of_nonpos h2]; linarith [hx.1]
    exact lt_of_le_of_lt this htδ
  rcases lt_or_ge t₀ t with hlt | hge
  · -- forward: Grönwall on `[t₀, t]`, starting from the zero at the left endpoint
    have hcont : ContinuousOn z (Icc t₀ t) :=
      fun x hx => ((hδ (hsub_fwd hx)).1).continuousAt.continuousWithinAt
    have hderiv : ∀ x ∈ Ico t₀ t, HasDerivWithinAt z (z' x) (Ici x) x :=
      fun x hx => ((hδ (hsub_fwd ⟨hx.1, le_of_lt hx.2⟩)).1).hasDerivWithinAt
    have hbd : ∀ x ∈ Ico t₀ t, ‖z' x‖ ≤ C * ‖z x‖ :=
      fun x hx => (hδ (hsub_fwd ⟨hx.1, le_of_lt hx.2⟩)).2
    exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont hderiv hz0 hbd t
      ⟨le_of_lt hlt, le_refl t⟩
  · -- backward: Grönwall on `[t, t₀]`, starting from the zero at the right endpoint
    have hcont : ContinuousOn z (Icc t t₀) :=
      fun x hx => ((hδ (hsub_bwd hx)).1).continuousAt.continuousWithinAt
    have hderiv : ∀ x ∈ Ioc t t₀, HasDerivWithinAt z (z' x) (Iic x) x :=
      fun x hx => ((hδ (hsub_bwd ⟨le_of_lt hx.1, hx.2⟩)).1).hasDerivWithinAt
    have hbd : ∀ x ∈ Ioc t t₀, ‖z' x‖ ≤ C * ‖z x‖ :=
      fun x hx => (hδ (hsub_bwd ⟨le_of_lt hx.1, hx.2⟩)).2
    exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_left hcont hderiv hz0 hbd t
      ⟨le_refl t, hge⟩

end Work.WilE2
