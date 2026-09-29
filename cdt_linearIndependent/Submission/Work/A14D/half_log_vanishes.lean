import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.Dzc_helpers
import Submission.Work.A14D.log_structured_vanishes

/-!
# `half_log_vanishes`

If `g` and `H` are holomorphic on the disc `ball (1/9) δ` and `g z · log (z − 1/9) = H z` on the
*lower* half disc `halfL δ`, then `g` vanishes on the disc.

The mechanism is the branch cut of the principal logarithm along the negative real axis.  Off the
slit ray `(−∞, 1/9]` the function `F z = g z · log (z − 1/9) − H z` is holomorphic (`g` and `H`
are holomorphic on the whole disc, and `z − 1/9` avoids `(−∞,0]` there).  Since `F` vanishes on
the open lower half disc and the slit disc `slitDisk δ` is preconnected, the identity theorem
gives `F ≡ 0` on the *whole* slit disc, hence in particular on the upper half disc: the relation
`g z · log (z − 1/9) = H z` propagates from the lower to the upper side.  From there the two
one-sided limits at a real point `x ∈ (1/9 − δ, 1/9)` (which see the two branch values
`log ‖x − 1/9‖ ± π·I`) force `g x = 0` on that interval, and the identity theorem finishes; this
last step is exactly `Work.A14D.log_structured_vanishes`, which we reuse.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

/-- The lower half disc sits in the disc cut along the ray `(−∞, 1/9]`. -/
lemma half_log_halfL_subset_slitDisk (δ : ℝ) : halfL δ ⊆ slitDisk δ :=
  fun _ hz => ⟨hz.1, Or.inl (ne_of_lt hz.2)⟩

/-- The lower half disc is open. -/
lemma half_log_isOpen_halfL (δ : ℝ) : IsOpen (halfL δ) :=
  Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)

/-- The lower half disc is nonempty for `δ > 0`. -/
lemma half_log_halfL_nonempty {δ : ℝ} (hδ : 0 < δ) : (halfL δ).Nonempty := by
  refine ⟨ninth - ((δ / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    have h : ninth - ((δ / 2 : ℝ) : ℂ) * Complex.I - ninth
        = -(((δ / 2 : ℝ) : ℂ) * Complex.I) := by ring
    rw [h, norm_neg, norm_mul]
    simp only [Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
    linarith
  · simp [ninth]
    linarith

/-- If `g` and `H` are holomorphic on the disc `ball (1/9) δ` and `g z * log (z - 1/9) = H z` for
every `z` in the lower half disc `halfL δ`, then `g` vanishes identically on the disc. -/
theorem half_log_vanishes {δ : ℝ} (hδ : 0 < δ) {g H : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball ninth δ))
    (hH : DifferentiableOn ℂ H (Metric.ball ninth δ))
    (hid : ∀ z ∈ halfL δ, g z * Complex.log (z - ninth) = H z) :
    ∀ z ∈ Metric.ball ninth δ, g z = 0 := by
  -- `F = g · log (· − 1/9) − H` is holomorphic on the slit disc …
  have hd : DifferentiableOn ℂ (fun z => g z * Complex.log (z - ninth) - H z) (slitDisk δ) :=
    (differentiableOn_logTerm hg).sub (hH.mono Set.inter_subset_left)
  -- … and vanishes on the open lower half disc, so it vanishes on the preconnected slit disc.
  have hFzero : ∀ z ∈ slitDisk δ, g z * Complex.log (z - ninth) - H z = 0 := by
    obtain ⟨z₀, hz₀⟩ := half_log_halfL_nonempty hδ
    have hz₀' : z₀ ∈ slitDisk δ := half_log_halfL_subset_slitDisk δ hz₀
    have hev : (fun z => g z * Complex.log (z - ninth) - H z) =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [(half_log_isOpen_halfL δ).mem_nhds hz₀] with w hw
      exact sub_eq_zero.mpr (hid w hw)
    exact (hd.analyticOnNhd (isOpen_slitDisk δ)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_slitDisk hδ) hz₀' hev
  -- Hence the relation `g · log (· − 1/9) = H` holds on both halves of the disc off the real axis,
  -- and the two one-sided limits at the cut finish the job.
  refine log_structured_vanishes hδ hg (hH.neg.mono Set.sdiff_subset) ?_
  intro z hz him
  exact hFzero z ⟨hz, Or.inl him⟩

end Work.A14D
