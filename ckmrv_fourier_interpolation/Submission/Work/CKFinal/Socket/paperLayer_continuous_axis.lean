/-
# Continuity of the naive CKMRV layer across the imaginary axis

For a point `τ₀ = i y₀` of the socket region `U₀` lying on the imaginary axis there is a ball
`B(τ₀, ρ) ⊆ U₀` on which the naive CKMRV layer `τ ↦ paperLayer (Gcusp ℓ d) ℓ d τ r` is continuous,
for **every** real `r`.  This is the continuity input of the `removable_vertical_line` argument
that makes `paperLayer` holomorphic across the axis.

WHY THE AXIS IS THE DELICATE CASE.  `paperLayer = layerLow + layerTrunc + highPart`
(`Work.Asymptotics.F2LayerDefs`), and each piece is continuous on the fundamental domain
`𝒟 = Work.Asymptotics.DomainD` (which contains the whole imaginary axis):

* For fixed `t > 0`, `τ ↦ Kaxis (Kfun ℓ d) τ t` is holomorphic at every `τ` with
  `j τ ≠ j (i t)` (`Work.Asymptotics.differentiableAt_Kfun_tau`); for `τ₁ ∈ 𝒟` the exceptional
  `t`'s are at most the two orbit heights `t = Im τ₁` and `t = 1/Im τ₁`
  (`Work.CKFinal.finite_coincidenceSet_imagAxis`), a null set.  So the integrands are a.e.
  continuous in `τ`.
* At those two heights `Kaxis` stays **bounded** — the apparent pole of the kernel is removed by
  the vanishing residue of the crossing (`Work.Asymptotics.Kaxis_local_coincidence`) — so the
  dominated-convergence dominator is a constant on `(0,1]`, and on `[1,∞)` it is the exponential
  cusp dominator.  Hence `layerLow` and `layerTrunc` are continuous on `𝒟`
  (`Work.CKFinal.AxisCont.continuousAt_layerLow_of_mem_DomainD_self`,
  `Work.CKFinal.AxisCont.continuousAt_layerTrunc_of_mem_DomainD`).
* `highPart` is a constant-coefficient combination of the holomorphic cusp coefficients
  `Gcusp ℓ d i j` (`Work.CKFinal.AxisCont.continuous_highPart`), hence continuous.

Finally `U₀` is open and `τ₀ ∈ U₀`, and a small ball around `τ₀` lies in `𝒟` as well
(`Work.CKFinal.ball_imagAxis_subset_DomainD_radius`), so the two conditions can be met at once by
`ρ = min ρ₁ (axisRadius τ₀.im)`.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.Basic
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.CKFinal.AxisCont.Basic
import Submission.Work.CKFinal.AxisCont.Pieces
import Submission.Work.CKFinal.AxisCont.continuousAt_layerTrunc_of_mem_DomainD
import Submission.Work.CKFinal.AxisCont.continuous_highPart

namespace Work.CKFinal.Socket

theorem paperLayer_continuous_axis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ₀ : UpperHalfPlane}
    (hτ₀ : τ₀ ∈ Work.CKFinal.Socket.U0) (haxis : τ₀.re = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball τ₀ ρ ⊆ Work.CKFinal.Socket.U0 ∧
      ContinuousOn (fun τ : UpperHalfPlane =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
        (Metric.ball τ₀ ρ) := by
  -- On the axis, `τ₀ = i y₀` with `y₀ = Im τ₀ > 0`.
  have hy₀ : 0 < τ₀.im := τ₀.im_pos
  have hτ₀eq : τ₀ = Work.Kernels.imagAxis τ₀.im hy₀ :=
    Work.CKFinal.eq_imagAxis_of_re_eq_zero (by rw [UpperHalfPlane.coe_re]; exact haxis)
  -- A ball around `τ₀` inside `U₀`, shrunk so that it also lies in `𝒟`.
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := (Metric.isOpen_iff.mp isOpen_U0 τ₀) hτ₀
  set ρ : ℝ := min ρ₁ (Work.CKFinal.axisRadius τ₀.im) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₁pos (Work.CKFinal.axisRadius_pos hy₀)
  have hρle : ρ ≤ Work.CKFinal.axisRadius τ₀.im := min_le_right _ _
  have hρρ₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hballU0 : Metric.ball τ₀ ρ ⊆ Work.CKFinal.Socket.U0 :=
    fun τ hτ => hρ₁sub (Metric.ball_subset_ball hρρ₁ hτ)
  have hballD : Metric.ball τ₀ ρ ⊆ Work.Asymptotics.DomainD := by
    have h := Work.CKFinal.ball_imagAxis_subset_DomainD_radius hy₀ hρpos hρle
    rwa [← hτ₀eq] at h
  refine ⟨ρ, hρpos, hballU0, ?_⟩
  -- Pointwise: `paperLayer` is the sum of its three pieces, continuous at every `τ₁ ∈ 𝒟`.
  intro τ₁ hτ₁
  have hD : τ₁ ∈ Work.Asymptotics.DomainD := hballD hτ₁
  have hlow := Work.CKFinal.AxisCont.continuousAt_layerLow_of_mem_DomainD_self ℓ d hd r hD
  have htrunc := Work.CKFinal.AxisCont.continuousAt_layerTrunc_of_mem_DomainD ℓ d hd r hD
  have hhigh : ContinuousAt (fun τ : UpperHalfPlane =>
      Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r) τ₁ :=
    (Work.CKFinal.AxisCont.continuous_highPart ℓ d hd r).continuousAt
  have hsum : ContinuousAt (fun τ : UpperHalfPlane =>
      Work.Asymptotics.layerLow ℓ d τ r
        + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
        + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r) τ₁ :=
    (hlow.add htrunc).add hhigh
  exact hsum.continuousWithinAt

end Work.CKFinal.Socket
