import Mathlib
import Submission.Work.Pert.Ksub2.Setup

namespace Work.Pert.Ksub2

open Filter

/-- **Local differentiability of the limit dynamics `F₀ = τ₀ ∘ f₀ ∘ τ₀`.**

If `f₀` agrees on the open ball `ball 0 ρ` with the differentiable germ `z ↦ z + z² · hF z`,
and `τ₀ w = -1/w` lands in that ball, then `F₀ = τ₀ ∘ f₀ ∘ τ₀` is complex differentiable at `w`:
near `w` it agrees with `v ↦ τ₀ (τ₀ v + (τ₀ v)² · hF (τ₀ v))`, a composition of the rational map
`τ₀` (differentiable at `w ≠ 0` and at the image point, which is nonzero exactly because of the
denominator hypothesis `1 + τ₀ w · hF (τ₀ w) ≠ 0`). -/
theorem differentiableAt_F0f_of_local {f₀ hF : ℂ → ℂ} {ρ : ℝ} {w : ℂ}
    (hfe : ∀ z ∈ Metric.ball (0 : ℂ) ρ, f₀ z = z + z ^ 2 * hF z)
    (hhFd : DifferentiableOn ℂ hF (Metric.ball (0 : ℂ) ρ))
    (hw : w ≠ 0) (ht : MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) ρ)
    (hden : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0) :
    DifferentiableAt ℂ (Work.Pert.F0f f₀) w := by
  have htu : MandelDim.tau0 w ≠ 0 := by
    simp only [MandelDim.tau0]
    exact div_ne_zero (by norm_num) hw
  -- `τ₀` is complex differentiable at every nonzero point.
  have htau : ∀ {v : ℂ}, v ≠ 0 → DifferentiableAt ℂ MandelDim.tau0 v := by
    intro v hv
    show DifferentiableAt ℂ (fun z : ℂ => -1 / z) v
    exact (differentiableAt_const (-1)).div differentiableAt_id hv
  -- `hF` is differentiable at `τ₀ w`, which lies in the open ball.
  have hFd : DifferentiableAt ℂ hF (MandelDim.tau0 w) :=
    hhFd.differentiableAt (Metric.isOpen_ball.mem_nhds ht)
  -- the germ `z ↦ z + z² · hF z` is differentiable there.
  have hg_diff : DifferentiableAt ℂ (fun z : ℂ => z + z ^ 2 * hF z) (MandelDim.tau0 w) :=
    differentiableAt_id.add ((differentiableAt_id.pow 2).mul hFd)
  -- the image point `τ₀ w + (τ₀ w)² · hF (τ₀ w) = τ₀ w · (1 + τ₀ w · hF (τ₀ w))` is nonzero.
  have hg0 : MandelDim.tau0 w + (MandelDim.tau0 w) ^ 2 * hF (MandelDim.tau0 w) ≠ 0 := by
    have heq : MandelDim.tau0 w + (MandelDim.tau0 w) ^ 2 * hF (MandelDim.tau0 w)
        = MandelDim.tau0 w * (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) := by ring
    rw [heq]
    exact mul_ne_zero htu hden
  -- `τ₀` maps a neighbourhood of `w` into the ball on which `f₀` is given by the germ.
  have hev : ∀ᶠ v in nhds w, MandelDim.tau0 v ∈ Metric.ball (0 : ℂ) ρ :=
    (htau hw).continuousAt.eventually (Metric.isOpen_ball.mem_nhds ht)
  -- hence `F₀` agrees near `w` with the nice composition.
  have hcongr : Work.Pert.F0f f₀ =ᶠ[nhds w]
      (fun v : ℂ =>
        MandelDim.tau0 (MandelDim.tau0 v + (MandelDim.tau0 v) ^ 2 * hF (MandelDim.tau0 v))) := by
    filter_upwards [hev] with v hv
    show MandelDim.tau0 (f₀ (MandelDim.tau0 v)) = _
    rw [hfe (MandelDim.tau0 v) hv]
  rw [Filter.EventuallyEq.differentiableAt_iff hcongr]
  exact (htau hg0).comp w (hg_diff.comp w (htau hw))

end Work.Pert.Ksub2
