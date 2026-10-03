import Mathlib

/-!
# `Work.Pert.V5.dev_horiz_le`

Displacement bound for `Φ - id` along a **horizontal** segment `t ↦ t + i s`, `t ∈ [a, b]`.

If `Φ` is complex differentiable on an open set `Q` containing the whole segment and the deviation
`Φ' - 1` is bounded on the segment by a continuous function `g`, then

  `‖(Φ (b + i s) - (b + i s)) - (Φ (a + i s) - (a + i s))‖ ≤ ∫ x in a..b, g x`.

The proof is the fundamental estimate "displacement ≤ integral of the speed"
(`norm_sub_le_integral_of_norm_deriv_le_of_le`) applied to the curve
`t ↦ Φ (t + i s) - (t + i s)`, whose derivative is `Φ' (t + i s) - 1`.  It is the exact horizontal
analogue of `Work.Pert.dev_vert_le`.
-/

namespace Work.Pert.V5

theorem dev_horiz_le {Φ : ℂ → ℂ} {Q : Set ℂ} {s a b : ℝ} {g : ℝ → ℝ}
    (hQ : IsOpen Q) (hab : a ≤ b)
    (hseg : ∀ x ∈ Set.Icc a b, ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Q)
    (hΦ : DifferentiableOn ℂ Φ Q)
    (hg : ∀ x ∈ Set.Icc a b, ‖deriv Φ ((x : ℂ) + (s : ℂ) * Complex.I) - 1‖ ≤ g x)
    (hgcont : ContinuousOn g (Set.Icc a b)) :
    ‖(Φ ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
        - (Φ ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))‖
      ≤ ∫ x in a..b, g x := by
  -- the horizontal parametrisation of the segment and the deviation along it
  let γ : ℝ → ℂ := fun t => (t : ℂ) + (s : ℂ) * Complex.I
  let f : ℝ → ℂ := fun t => Φ (γ t) - γ t
  -- `γ` is the curve `t ↦ t + i s`, with derivative `1`
  have hγ : ∀ t : ℝ, HasDerivAt γ (1 : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) + (s : ℂ) * Complex.I) (1 : ℂ) t :=
      h1.add_const ((s : ℂ) * Complex.I)
    simpa [γ] using h2
  -- `f` is differentiable on the interval, with derivative `Φ' (γ t) - 1`
  have hfd : ∀ t ∈ Set.Icc a b, HasDerivAt f (deriv Φ (γ t) - 1) t := by
    intro t ht
    have hzQ : γ t ∈ Q := hseg t ht
    have hdt : DifferentiableAt ℂ Φ (γ t) := hΦ.differentiableAt (hQ.mem_nhds hzQ)
    have hcomp : HasDerivAt (fun u : ℝ => Φ (γ u)) (deriv Φ (γ t) * 1) t :=
      hdt.hasDerivAt.comp t (hγ t)
    have hsub : HasDerivAt (fun u : ℝ => Φ (γ u) - γ u) (deriv Φ (γ t) * 1 - 1) t :=
      hcomp.sub (hγ t)
    have he : deriv Φ (γ t) * 1 - 1 = deriv Φ (γ t) - 1 := by ring
    rw [he] at hsub
    simpa [f] using hsub
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le (f := f) (B := g) (a := a) (b := b)
    hab
    -- continuity on the closed interval
    (fun t ht => (hfd t ht).continuousAt.continuousWithinAt)
    -- differentiability on the open interval
    (fun t ht => (hfd t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt)
    -- the pointwise bound on the norm of the derivative, a.e.
    (by
      filter_upwards with t ht
      rw [(hfd t (Set.Ioo_subset_Icc_self ht)).deriv]
      exact hg t (Set.Ioo_subset_Icc_self ht))
    -- integrability of the majorant
    (by
      have h : ContinuousOn g (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
      exact h.intervalIntegrable)
  simpa only [f, γ] using hmain

end Work.Pert.V5
