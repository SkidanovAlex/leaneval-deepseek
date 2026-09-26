import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.normalFamily_image_mem_nhds

/-!
# The offset neighbourhood of a regular point of a curve

For a `C¹` closed plane curve `c` with `deriv c.γ t₀ ≠ 0` and a continuous `2π`-periodic field `v`
whose **offset map** `offset c v (t,u) = c.γ t + u·v t` is injective in the `u`-variable on the
strip `|u| < δ`, the image `annulus c v δ` of the strip is a neighbourhood of the point `c.γ t₀`.

The proof reduces the statement, by the *linear* change of coordinates `z ↦ z / e` with
`e = deriv c.γ t₀ ≠ 0`, to the statement that the image of the strip under the **normalized
family** `(t,u) ↦ c.γ t / e + u * (v t / e)` is a neighbourhood of `c.γ t₀ / e`.  Indeed
`offset c v (t,u) = e * normalFamily c v e (t,u)`, so a ball of radius `ε` in the normalized
picture corresponds to a ball of radius `‖e‖ * ε` around `c.γ t₀`.

The core estimate for the normalized family is proved in
`Work.Smooth.JordanSeparation.normalFamily_image_mem_nhds`.
-/

open Set

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The **normalized offset family** of the curve `c` along the field `v` with respect to the
direction `e ≠ 0`: `(t,u) ↦ c.γ t / e + u * (v t / e)`.  For `e = deriv c.γ t₀` this is the
offset map expressed in the linear coordinates in which the tangent vector at `t₀` becomes `1`. -/
def normalFamily (c : Work.Smooth.Jordan.SmoothPlaneCurve) (v : ℝ → ℂ) (e : ℂ) (p : ℝ × ℝ) : ℂ :=
  c.γ p.1 / e + p.2 * (v p.1 / e)

theorem normalFamily_apply (c : Work.Smooth.Jordan.SmoothPlaneCurve) (v : ℝ → ℂ) (e : ℂ)
    (p : ℝ × ℝ) : normalFamily c v e p = c.γ p.1 / e + p.2 * (v p.1 / e) := rfl

/-- `offset c v (t,u) = e * normalFamily c v e (t,u)` for `e ≠ 0`. -/
theorem offset_eq_mul_normalFamily (c : Work.Smooth.Jordan.SmoothPlaneCurve) (v : ℝ → ℂ)
    {e : ℂ} (he : e ≠ 0) (t u : ℝ) :
    offset c v (t, u) = e * normalFamily c v e (t, u) := by
  rw [normalFamily_apply, offset_def, mul_add, mul_div_cancel₀ _ he]
  rw [mul_comm e, mul_assoc, div_mul_cancel₀ _ he]

/-- The u-injectivity of the offset map transfers to the normalized family. -/
theorem normalFamily_u_injective (c : Work.Smooth.Jordan.SmoothPlaneCurve) {v : ℝ → ℂ} {δ : ℝ}
    {e : ℂ} (he : e ≠ 0)
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      offset c v (t, u) = offset c v (t', u') → u = u') :
    ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      normalFamily c v e (t, u) = normalFamily c v e (t', u') → u = u' := by
  intro t t' u u' hu hu' h
  refine hinj t t' u u' hu hu' ?_
  simpa only [offset_eq_mul_normalFamily c v he] using congrArg (fun z => e * z) h

/-- **The offset neighbourhood of a regular point.**
If the offset map of a `C¹` closed curve along a continuous field is injective in the normal
coordinate on the strip `|u| < δ`, then the image `annulus c v δ` of the strip is a neighbourhood
of every regular point of the curve. -/
theorem annulus_mem_nhds_of_regular (c : Work.Smooth.Jordan.SmoothPlaneCurve) {v : ℝ → ℂ} {δ : ℝ}
    (hv : Continuous v) (hδ : 0 < δ) (hper : Function.Periodic v (2 * Real.pi))
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      Work.Smooth.JordanSeparation.offset c v (t, u)
        = Work.Smooth.JordanSeparation.offset c v (t', u') → u = u')
    {t₀ : ℝ} (himm : deriv c.γ t₀ ≠ 0) :
    Work.Smooth.JordanSeparation.annulus c v δ ∈ nhds (c.γ t₀) := by
  set e : ℂ := deriv c.γ t₀ with he_def
  have he : e ≠ 0 := by rw [he_def]; exact himm
  have hne : (0 : ℝ) < ‖e‖ := norm_pos_iff.mpr he
  -- the normalized curve has derivative `1` at `t₀`
  have hderiv : deriv (fun t : ℝ => c.γ t / e) t₀ = 1 := by
    have h : (fun s : ℝ => c.γ s / e) = fun s => e⁻¹ * c.γ s := by
      ext s; rw [div_eq_inv_mul]
    rw [h, deriv_const_mul_field]
    rw [he_def, inv_mul_cancel₀ he]
  -- the core estimate, at `t₀`
  obtain ⟨ε, hε, hball⟩ := normalFamily_image_mem_nhds (fun t : ℝ => c.γ t / e)
    (fun t : ℝ => v t / e) δ t₀ (c.contDiff.div_const e) (hv.div_const e) hδ
    (by rw [hderiv]; exact one_ne_zero)
    (fun t t' u u' hu hu' h => normalFamily_u_injective c he hinj t t' u u' hu hu' h)
  refine Metric.mem_nhds_iff.mpr ⟨‖e‖ * ε, mul_pos hne hε, ?_⟩
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  -- `z / e` lies in the normalized ball
  have hmem : z / e ∈ Metric.ball ((fun t : ℝ => c.γ t / e) t₀) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : z / e - c.γ t₀ / e = (z - c.γ t₀) / e := by ring
    rw [h1, norm_div, div_lt_iff₀ hne]
    linarith
  obtain ⟨p, hp, hpe⟩ := hball hmem
  refine ⟨p, hp, ?_⟩
  have hz' : z = e * (z / e) := by rw [mul_div_cancel₀ _ he]
  rw [hz', ← hpe, offset_eq_mul_normalFamily c v he]
  rfl

end

end Work.Smooth.JordanSeparation
