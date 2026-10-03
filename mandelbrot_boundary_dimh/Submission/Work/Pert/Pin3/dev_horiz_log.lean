import Mathlib
import Submission.Work.Pert.V5.dev_horiz_le

/-!
# `Work.Pert.Pin3.dev_horiz_log`

Logarithmic bound for the displacement of `Φ - id` along a **horizontal** segment
`t ↦ t + i y`, `t ∈ [y - Ξ - mu, c]`.

If `Φ` is complex differentiable at every point of the segment and
`‖Φ' (x + i y) - 1‖ ≤ C / (y - Ξ - x)` there, then

  `‖(Φ z_c - z_c) - (Φ z_a - z_a)‖ ≤ C log (mu / (y - Ξ - c))`,  `z_s = s + i y`,
  `a = y - Ξ - mu`,

which is the statement "the displacement is at most the integral of the speed",
`∫_a^c C/(y - Ξ - x) dx`, with the integral evaluated in closed form
(`y - Ξ - a = mu`).

This is the exact horizontal analogue of `Work.Pert.Pin3.dev_vert_log`.  The fundamental
estimate is `norm_sub_le_integral_of_norm_deriv_le_of_le` (Mathlib), but that lemma wants
`Φ` to be holomorphic on a *neighbourhood* of the segment (as in `Work.Pert.V5.dev_horiz_le`).
Here only pointwise differentiability on the segment is assumed, so we prove the pointwise
variant `dev_horiz_le_of_diffAt` below (same proof as the vertical case, the
differentiability being taken directly from the hypothesis) and apply it.
-/

namespace Work.Pert.Pin3

open MeasureTheory

/-- Displacement bound along a horizontal segment `t ↦ t + i s`, `t ∈ [a, b]`, from
**pointwise** complex differentiability on the segment: no neighbourhood hypothesis is needed
for the fundamental estimate.  This is `Work.Pert.V5.dev_horiz_le` with
`DifferentiableOn ℂ Φ Q` replaced by
`∀ x ∈ Icc a b, DifferentiableAt ℂ Φ (x + i s)`.

It is the exact horizontal analogue of `Work.Pert.Pin3.dev_vert_le_of_diffAt`. -/
theorem dev_horiz_le_of_diffAt {Φ : ℂ → ℂ} {s a b : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b)
    (hdiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℂ Φ ((x : ℂ) + (s : ℂ) * Complex.I))
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
    have hdt : DifferentiableAt ℂ Φ (γ t) := hdiff t ht
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

theorem dev_horiz_log {Φ : ℂ → ℂ} {Ξ mu y c C : ℝ}
    (hmu : 0 < mu) (hy : 0 < y) (hyXi : Ξ + 1 ≤ y) (hlo : y - Ξ - mu ≤ c) (hhi : c < y - Ξ)
    (hdiff : ∀ x ∈ Set.Icc (y - Ξ - mu) c,
      DifferentiableAt ℂ Φ ((x : ℂ) + (y : ℂ) * Complex.I))
    (hbd : ∀ x ∈ Set.Icc (y - Ξ - mu) c,
      ‖deriv Φ ((x : ℂ) + (y : ℂ) * Complex.I) - 1‖ ≤ C / (y - Ξ - x))
    (hC : 0 ≤ C) :
    ‖(Φ ((c : ℂ) + (y : ℂ) * Complex.I) - ((c : ℂ) + (y : ℂ) * Complex.I))
        - (Φ ((((y - Ξ - mu : ℝ)) : ℂ) + (y : ℂ) * Complex.I)
            - ((((y - Ξ - mu : ℝ)) : ℂ) + (y : ℂ) * Complex.I))‖
      ≤ C * Real.log (mu / (y - Ξ - c)) := by
  -- `hy`, `hyXi`, `hC` are not needed for the estimate, but are kept to match the statement.
  have _ := hy
  have _ := hyXi
  have _ := hC
  have hden : 0 < y - Ξ - c := by linarith
  -- positivity of the denominator all along the segment
  have hpos : ∀ x ∈ Set.Icc (y - Ξ - mu) c, 0 < y - Ξ - x := by
    intro x hx
    have h : y - Ξ - c ≤ y - Ξ - x := by have := hx.2; linarith
    exact lt_of_lt_of_le hden h
  -- continuity of the majorant on the interval
  have hgcont : ContinuousOn (fun x : ℝ => C / (y - Ξ - x)) (Set.Icc (y - Ξ - mu) c) := by
    apply ContinuousOn.div₀ continuousOn_const
    · exact continuousOn_const.sub continuousOn_id
    · intro x hx
      exact ne_of_gt (hpos x hx)
  -- the fundamental estimate
  have hmain : ‖(Φ ((c : ℂ) + (y : ℂ) * Complex.I) - ((c : ℂ) + (y : ℂ) * Complex.I))
        - (Φ (((y - Ξ - mu : ℝ) : ℂ) + (y : ℂ) * Complex.I)
            - (((y - Ξ - mu : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖
      ≤ ∫ x in (y - Ξ - mu)..c, C / (y - Ξ - x) :=
    dev_horiz_le_of_diffAt (s := y) (a := y - Ξ - mu) (b := c)
      (g := fun x : ℝ => C / (y - Ξ - x)) hlo hdiff hbd hgcont
  -- the antiderivative of the majorant
  have hderiv : ∀ x ∈ Set.uIcc (y - Ξ - mu) c,
      HasDerivAt (fun t : ℝ => -C * Real.log (y - Ξ - t)) (C / (y - Ξ - x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hlo] at hx
    have hxden : 0 < y - Ξ - x := hpos x hx
    have h1 : HasDerivAt (fun t : ℝ => y - Ξ - t) (-1) x := by
      have h := (hasDerivAt_id x).const_sub (y - Ξ)
      simpa using h
    have h2 : HasDerivAt (fun t : ℝ => Real.log (y - Ξ - t)) ((-1) / (y - Ξ - x)) x :=
      h1.log (ne_of_gt hxden)
    have h3 : HasDerivAt (fun t : ℝ => -C * Real.log (y - Ξ - t))
        ((-C) * ((-1) / (y - Ξ - x))) x := h2.const_mul (-C)
    have he : (-C) * ((-1) / (y - Ξ - x)) = C / (y - Ξ - x) := by ring
    rwa [he] at h3
  have hint : IntervalIntegrable (fun x : ℝ => C / (y - Ξ - x)) volume (y - Ξ - mu) c := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hlo]
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- the closed form of the integral
  have ha : y - Ξ - (y - Ξ - mu) = mu := by ring
  have key : (-C * Real.log (y - Ξ - c)) - (-C * Real.log (y - Ξ - (y - Ξ - mu)))
      = C * Real.log (mu / (y - Ξ - c)) := by
    rw [ha, Real.log_div (ne_of_gt hmu) (ne_of_gt hden)]
    ring
  calc ‖(Φ ((c : ℂ) + (y : ℂ) * Complex.I) - ((c : ℂ) + (y : ℂ) * Complex.I))
        - (Φ ((((y - Ξ - mu : ℝ)) : ℂ) + (y : ℂ) * Complex.I)
            - ((((y - Ξ - mu : ℝ)) : ℂ) + (y : ℂ) * Complex.I))‖
      ≤ ∫ x in (y - Ξ - mu)..c, C / (y - Ξ - x) := hmain
    _ = (-C * Real.log (y - Ξ - c)) - (-C * Real.log (y - Ξ - (y - Ξ - mu))) := hF
    _ = C * Real.log (mu / (y - Ξ - c)) := key

end Work.Pert.Pin3
