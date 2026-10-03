import Mathlib

/-!
# `Work.Pert.dev_vert_le`

Displacement bound for `Φ - id` along a **vertical** segment `t ↦ x + i t`, `t ∈ [y₁, y₂]`.

If `Φ` is complex differentiable on an open set `Q` containing the whole segment and the deviation
`Φ' - 1` is bounded on the segment by a continuous function `g`, then

  `‖(Φ z₂ - z₂) - (Φ z₁ - z₁)‖ ≤ ∫ t in y₁..y₂, g t`,   `zⱼ = x + i yⱼ`.

The proof is the fundamental estimate "displacement ≤ integral of the speed"
(`norm_sub_le_integral_of_norm_deriv_le_of_le`) applied to the curve
`t ↦ Φ (x + i t) - (x + i t)`, whose derivative `(Φ' (x + i t) - 1) * I` has norm
`‖Φ' (x + i t) - 1‖ ≤ g t` because `‖I‖ = 1`.
-/

namespace Work.Pert

theorem dev_vert_le {Φ : ℂ → ℂ} {Q : Set ℂ} {x y₁ y₂ : ℝ} {g : ℝ → ℝ}
    (hQ : IsOpen Q) (hy : y₁ ≤ y₂)
    (hseg : ∀ t ∈ Set.Icc y₁ y₂, ((x : ℂ) + (t : ℂ) * Complex.I) ∈ Q)
    (hΦ : DifferentiableOn ℂ Φ Q)
    (hg : ∀ t ∈ Set.Icc y₁ y₂, ‖deriv Φ ((x : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ g t)
    (hgcont : ContinuousOn g (Set.Icc y₁ y₂)) :
    ‖(Φ ((x : ℂ) + (y₂ : ℂ) * Complex.I) - ((x : ℂ) + (y₂ : ℂ) * Complex.I))
        - (Φ ((x : ℂ) + (y₁ : ℂ) * Complex.I) - ((x : ℂ) + (y₁ : ℂ) * Complex.I))‖
      ≤ ∫ t in y₁..y₂, g t := by
  -- the vertical parametrisation of the segment and the deviation along it
  let γ : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * Complex.I
  let f : ℝ → ℂ := fun t => Φ (γ t) - γ t
  -- `γ` is the curve `t ↦ x + i t`, with derivative `I`
  have hγ : ∀ t : ℝ, HasDerivAt γ Complex.I t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) (1 * Complex.I) t := h1.mul_const _
    have h3 : HasDerivAt (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) (1 * Complex.I) t :=
      h2.const_add _
    simpa [γ, mul_one] using h3
  -- `f` is differentiable on the interval, with derivative `(Φ' (γ t) - 1) * I`
  have hfd : ∀ t ∈ Set.Icc y₁ y₂, HasDerivAt f ((deriv Φ (γ t) - 1) * Complex.I) t := by
    intro t ht
    have hdt : DifferentiableAt ℂ Φ (γ t) := hΦ.differentiableAt (hQ.mem_nhds (hseg t ht))
    have hcomp : HasDerivAt (fun s : ℝ => Φ (γ s)) (deriv Φ (γ t) * Complex.I) t :=
      hdt.hasDerivAt.comp t (hγ t)
    have hsub : HasDerivAt (fun s : ℝ => Φ (γ s) - γ s)
        (deriv Φ (γ t) * Complex.I - Complex.I) t := hcomp.sub (hγ t)
    have he : deriv Φ (γ t) * Complex.I - Complex.I = (deriv Φ (γ t) - 1) * Complex.I := by ring
    rwa [he] at hsub
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le (f := f) (B := g) (a := y₁) (b := y₂)
    hy
    -- continuity on the closed interval
    (fun t ht => (hfd t ht).continuousAt.continuousWithinAt)
    -- differentiability on the open interval
    (fun t ht => (hfd t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt)
    -- the pointwise bound on the norm of the derivative, a.e.
    (by
      filter_upwards with t ht
      rw [(hfd t (Set.Ioo_subset_Icc_self ht)).deriv, norm_mul, Complex.norm_I, mul_one]
      exact hg t (Set.Ioo_subset_Icc_self ht))
    -- integrability of the majorant
    (by
      have h : ContinuousOn g (Set.uIcc y₁ y₂) := by rwa [Set.uIcc_of_le hy]
      exact h.intervalIntegrable)
  simpa only [f, γ] using hmain

end Work.Pert
