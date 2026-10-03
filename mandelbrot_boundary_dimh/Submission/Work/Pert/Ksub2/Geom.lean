import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Engine
import Submission.Work.Pert.Ksub2.anchor_scale_deriv
import Submission.Work.Pert.inv_close_of_deriv_close

/-!
# `Work.Pert.Ksub2.Geom` — the fixed-depth geometry of `Ksub_phi_close_v2`

Elementary geometric facts at the fixed anchor scale `M` of `Ksub2.exists_anchor_sharp`:

* `norm_sub_negM_le`: strip points are within `1 + T` of `-M`;
* `Dstrip_sub_anchor_ball`: hence the strip lies in the anchor ball
  `Metric.ball (Xc d (-M)) (M/40)`, provided `Xc d` moves it by at most `M/160`;
* `Phi0_inv_on_Dstrip`: consequently `Φ₀ (Xc d u) = u` on the strip (the datum's curve and the
  anchor coordinate are mutually inverse there, by the reverse-expansion estimate for `Xc d`);
* `dev_le_of_deriv_bound`: the convex mean value inequality turning a bound on `(Φ - Φ₀)'` on the
  anchor ball into `‖Φ z - Φ₀ z‖ ≤ K‖z - Xc d (-M)‖` based at the pinned point.

These are the inputs of the deviation/coverage step of `Ksub_phi_close_v2`; the analytic bound on
`(Φm - Φ₀)'` is `Ksub2.deriv_diff_le`.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric

noncomputable section

/-- Strip points are within `1 + T` of `-M`. -/
theorem norm_sub_negM_le {M T : ℝ} {u : ℂ} (hu : u ∈ Dstrip M T) :
    ‖u - (((-M : ℝ)) : ℂ)‖ ≤ 1 + T := by
  have h1 : -M - 1 ≤ u.re := hu.1
  have h2 : u.re ≤ -M := hu.2.1
  have h3 : |u.im| ≤ T := hu.2.2
  have hre : (u - (((-M : ℝ)) : ℂ)).re = u.re + M := by simp
  have him : (u - (((-M : ℝ)) : ℂ)).im = u.im := by simp
  have hre' : |u.re + M| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc ‖u - (((-M : ℝ)) : ℂ)‖
      ≤ |(u - (((-M : ℝ)) : ℂ)).re| + |(u - (((-M : ℝ)) : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im (u - (((-M : ℝ)) : ℂ))
    _ = |u.re + M| + |u.im| := by rw [hre, him]
    _ ≤ 1 + T := add_le_add hre' h3

/-- The whole strip lies in the anchor ball if `Xc d` does not move strip points much and the
anchor point `Xc d (-M)` is itself within `M/320` of `-M`. -/
theorem Dstrip_sub_anchor_ball {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {M T : ℝ} (hM : 81 ≤ M)
    (hXcM : ‖Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ)‖ ≤ M / 320)
    (hT : T ≤ M / 160) :
    ∀ u ∈ Dstrip M T,
      ‖u - Work.Pert.Xc d (((-M : ℝ)) : ℂ)‖ < M / 40 := by
  intro u hu
  have h2 : ‖u - (((-M : ℝ)) : ℂ)‖ ≤ 1 + T := norm_sub_negM_le hu
  have hsplit : u - Work.Pert.Xc d (((-M : ℝ)) : ℂ)
      = (u - (((-M : ℝ)) : ℂ))
        - (Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ)) := by
    ring
  calc ‖u - Work.Pert.Xc d (((-M : ℝ)) : ℂ)‖
      = ‖(u - (((-M : ℝ)) : ℂ))
          - (Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ))‖ := by rw [hsplit]
    _ ≤ ‖u - (((-M : ℝ)) : ℂ)‖
          + ‖Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ)‖ := norm_sub_le _ _
    _ ≤ (1 + T) + M / 320 := add_le_add h2 hXcM
    _ < M / 40 := by linarith


/-- `deriv` is the junk value `0` where the function is not complex differentiable, so a bound
`‖deriv Φ u - 1‖ ≤ 1/2` forces differentiability at `u`. -/
theorem differentiableAt_of_norm_deriv_sub_one_le {Φ : ℂ → ℂ} {u : ℂ}
    (h : ‖deriv Φ u - 1‖ ≤ 1 / 2) : DifferentiableAt ℂ Φ u := by
  by_contra hd
  have h0 : deriv Φ u = 0 := deriv_zero_of_not_differentiableAt hd
  rw [h0] at h
  norm_num at h

/-- **`Φ₀` inverts the datum's curve on the strip.**  If `Φ₀` satisfies the anchor clause
`Xc d (Φ₀ ζ) = ζ` on `ball (Xc d (-M)) (M/40)`, the strip lies in that ball, and both `u` and
`Φ₀ (Xc d u)` lie in the disc `ball (-M) (M/4)` where `Xc d` has derivative within `1/2` of `1`,
then `Φ₀ (Xc d u) = u`.

(The one-sided inverse `Xc ∘ Φ₀ = id` is upgraded to `Φ₀ ∘ Xc = id` by the reverse-expansion
estimate for `Xc d`: `‖z - z'‖ ≤ 2‖Xc d z - Xc d z'‖` on the convex anchor disc.) -/
theorem Phi0_inv_on_Dstrip {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {M T : ℝ} {Φ₀ : ℂ → ℂ}
    (hder : ∀ u ∈ Metric.ball (((-M : ℝ)) : ℂ) (M / 4),
      ‖deriv (fun v : ℂ => MandelDim.tau0 (d.φ v)) u - 1‖ ≤ 1 / 2)
    (hinv : ∀ ζ ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40),
      Work.Pert.Xc d (Φ₀ ζ) = ζ)
    (hof : ∀ u ∈ Dstrip M T,
      Work.Pert.Xc d u ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40))
    (hb1 : ∀ u ∈ Dstrip M T, u ∈ Metric.ball (((-M : ℝ)) : ℂ) (M / 4))
    (hb2 : ∀ u ∈ Dstrip M T,
      Φ₀ (Work.Pert.Xc d u) ∈ Metric.ball (((-M : ℝ)) : ℂ) (M / 4)) :
    ∀ u ∈ Dstrip M T, Φ₀ (Work.Pert.Xc d u) = u := by
  intro u hu
  have hζ : Work.Pert.Xc d u ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40) :=
    hof u hu
  have hval : MandelDim.tau0 (d.φ (Φ₀ (Work.Pert.Xc d u))) = MandelDim.tau0 (d.φ u) :=
    hinv _ hζ
  have hdiff : DifferentiableOn ℂ (fun v : ℂ => MandelDim.tau0 (d.φ v))
      (Metric.ball (((-M : ℝ)) : ℂ) (M / 4)) :=
    fun z hz => (differentiableAt_of_norm_deriv_sub_one_le (hder z hz)).differentiableWithinAt
  have hexp := inv_close_of_deriv_close Metric.isOpen_ball (convex_ball _ _) hdiff hder
    (Φ₀ (Work.Pert.Xc d u)) (hb2 u hu) u (hb1 u hu)
  rw [hval] at hexp
  have h0 : ‖Φ₀ (Work.Pert.Xc d u) - u‖ = 0 :=
    le_antisymm (by simpa using hexp) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- **The mean value step of the deviation bound.**  If `Φ - Φ₀` is holomorphic on the convex ball
`ball c r` with derivative bounded by `K` there, and `Φ c = Φ₀ c`, then
`‖Φ z - Φ₀ z‖ ≤ K‖z - c‖` for every `z ∈ ball c r`.  (This is the step that turns the *derivative*
comparison `Ksub2.deriv_diff_le` into the deviation bound used by the coverage argument; the base
point `c` is the pinned anchor `Xc d (-M)`, where `Φm` and `Φ₀` agree exactly.) -/
theorem dev_le_of_deriv_bound {Φ Φ₀ : ℂ → ℂ} {c : ℂ} {r K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K)
    (hdiff : ∀ z ∈ Metric.ball c r, DifferentiableAt ℂ (fun z => Φ z - Φ₀ z) z)
    (hbound : ∀ z ∈ Metric.ball c r, ‖deriv (fun z => Φ z - Φ₀ z) z‖ ≤ K)
    (hagree : Φ c = Φ₀ c) :
    ∀ z ∈ Metric.ball c r, ‖Φ z - Φ₀ z‖ ≤ K * ‖z - c‖ := by
  intro z hz
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_ball c r) hz
    (Metric.mem_ball_self hr)
  rw [hagree, sub_self, zero_sub, norm_neg, norm_sub_rev] at h
  simpa [norm_sub_rev] using h

end

end Work.Pert.Ksub2
