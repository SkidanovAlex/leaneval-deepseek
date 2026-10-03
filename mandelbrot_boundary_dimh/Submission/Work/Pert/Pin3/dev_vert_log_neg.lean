import Mathlib
import Submission.Work.Pert.Pin3.dev_vert_log
import Submission.Work.Pert.dev_vert_le

/-!
# `Work.Pert.Pin3.dev_vert_log_neg`

Mirror of `Work.Pert.Pin3.dev_vert_log` for the vertical segment traversed **downwards**
in the imaginary direction, `t ↦ c - i t`, `t ∈ [T, M]`.

The only change with respect to `dev_vert_log` is the parametrisation: `γ t = c - i t` has
derivative `-I` instead of `I`, but `‖-I‖ = 1`, so the same "displacement ≤ integral of the
speed" estimate (`norm_sub_le_integral_of_norm_deriv_le_of_le`) applies verbatim, and the
closed form of the integral of `C₂/(t - Ξ - 1) + K/t` is the same.  Only pointwise complex
differentiability on the segment is assumed, so we use the `-I` mirror of the pointwise
variant `dev_vert_le_of_diffAt` (from `dev_vert_log`).
-/

namespace Work.Pert.Pin3

open MeasureTheory

/-- Displacement bound along the vertical segment `t ↦ x - i t`, `t ∈ [y₁, y₂]`, from
**pointwise** complex differentiability on the segment.  This is the `-I` mirror of
`Work.Pert.Pin3.dev_vert_le_of_diffAt`. -/
theorem dev_vert_le_of_diffAt_neg {Φ : ℂ → ℂ} {x y₁ y₂ : ℝ} {g : ℝ → ℝ}
    (hy : y₁ ≤ y₂)
    (hdiff : ∀ t ∈ Set.Icc y₁ y₂, DifferentiableAt ℂ Φ ((x : ℂ) - (t : ℂ) * Complex.I))
    (hg : ∀ t ∈ Set.Icc y₁ y₂, ‖deriv Φ ((x : ℂ) - (t : ℂ) * Complex.I) - 1‖ ≤ g t)
    (hgcont : ContinuousOn g (Set.Icc y₁ y₂)) :
    ‖(Φ ((x : ℂ) - (y₂ : ℂ) * Complex.I) - ((x : ℂ) - (y₂ : ℂ) * Complex.I))
        - (Φ ((x : ℂ) - (y₁ : ℂ) * Complex.I) - ((x : ℂ) - (y₁ : ℂ) * Complex.I))‖
      ≤ ∫ t in y₁..y₂, g t := by
  -- the vertical parametrisation of the segment and the deviation along it
  let γ : ℝ → ℂ := fun t => (x : ℂ) - (t : ℂ) * Complex.I
  let f : ℝ → ℂ := fun t => Φ (γ t) - γ t
  -- `γ` is the curve `t ↦ x - i t`, with derivative `-I`
  have hγ : ∀ t : ℝ, HasDerivAt γ (-Complex.I) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) (1 * Complex.I) t := h1.mul_const _
    have h3 : HasDerivAt (fun s : ℝ => (x : ℂ) - (s : ℂ) * Complex.I) (-Complex.I) t := by
      simpa using h2.const_sub (x : ℂ)
    simpa [γ] using h3
  -- `f` is differentiable on the interval, with derivative `(Φ' (γ t) - 1) * (-I)`
  have hfd : ∀ t ∈ Set.Icc y₁ y₂, HasDerivAt f ((deriv Φ (γ t) - 1) * (-Complex.I)) t := by
    intro t ht
    have hdt : DifferentiableAt ℂ Φ (γ t) := hdiff t ht
    have hcomp : HasDerivAt (fun s : ℝ => Φ (γ s)) (deriv Φ (γ t) * (-Complex.I)) t :=
      hdt.hasDerivAt.comp t (hγ t)
    have hsub : HasDerivAt (fun s : ℝ => Φ (γ s) - γ s)
        (deriv Φ (γ t) * (-Complex.I) - (-Complex.I)) t := hcomp.sub (hγ t)
    have he : deriv Φ (γ t) * (-Complex.I) - (-Complex.I)
        = (deriv Φ (γ t) - 1) * (-Complex.I) := by ring
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
      rw [(hfd t (Set.Ioo_subset_Icc_self ht)).deriv, norm_mul, norm_neg, Complex.norm_I, mul_one]
      exact hg t (Set.Ioo_subset_Icc_self ht))
    -- integrability of the majorant
    (by
      have h : ContinuousOn g (Set.uIcc y₁ y₂) := by rwa [Set.uIcc_of_le hy]
      exact h.intervalIntegrable)
  simpa only [f, γ] using hmain

theorem dev_vert_log_neg {Φ : ℂ → ℂ} {c Ξ C₂ K M T : ℝ}
    (hΞ : 0 < Ξ) (hTM : T ≤ M) (hT2 : 2 * (Ξ + 1) ≤ T)
    (hdiff : ∀ t ∈ Set.Icc T M, DifferentiableAt ℂ Φ (c - (t : ℂ) * Complex.I))
    (hbound : ∀ t ∈ Set.Icc T M,
      ‖deriv Φ (c - (t : ℂ) * Complex.I) - 1‖ ≤ C₂ / (t - Ξ - 1) + K / t)
    (hC₂ : 0 ≤ C₂) (hK : 0 ≤ K) :
    ‖(Φ (c - (M : ℂ) * Complex.I) - (c - (M : ℂ) * Complex.I))
        - (Φ (c - (T : ℂ) * Complex.I) - (c - (T : ℂ) * Complex.I))‖
      ≤ C₂ * Real.log ((M - Ξ - 1) / (T - Ξ - 1)) + K * Real.log (M / T) := by
  -- `hC₂` and `hK` are not needed for the estimate, but are kept as hypotheses to match
  -- the requested statement.
  have hC₂_used : 0 ≤ C₂ := hC₂
  have hK_used : 0 ≤ K := hK
  -- positivity of all the quantities involved
  have hTpos : 0 < T := by linarith
  have hTden : 0 < T - Ξ - 1 := by linarith
  have hMden : 0 < M - Ξ - 1 := by linarith
  have hMpos : 0 < M := by linarith
  -- the pointwise bound, rewritten in the `Ξ + 1` shape
  have hg : ∀ t ∈ Set.Icc T M,
      ‖deriv Φ (c - (t : ℂ) * Complex.I) - 1‖ ≤ C₂ / (t - (Ξ + 1)) + K / t := by
    intro t ht
    have h := hbound t ht
    have he : t - Ξ - 1 = t - (Ξ + 1) := by ring
    rw [he] at h
    exact h
  -- continuity of the majorant on the interval
  have hgcont : ContinuousOn (fun t : ℝ => C₂ / (t - (Ξ + 1)) + K / t) (Set.Icc T M) := by
    apply ContinuousOn.add
    · apply ContinuousOn.div₀ continuousOn_const (continuousOn_id.sub continuousOn_const)
      intro t ht
      have h : Ξ + 1 < t := by have := ht.1; linarith
      have hne : t - (Ξ + 1) ≠ 0 := by linarith
      simpa using hne
    · apply ContinuousOn.div₀ continuousOn_const continuousOn_id
      intro t ht
      have h : 0 < t := by have := ht.1; linarith
      have hne : t ≠ 0 := ne_of_gt h
      simpa using hne
  -- the fundamental estimate
  have hmain : ‖(Φ (c - (M : ℂ) * Complex.I) - (c - (M : ℂ) * Complex.I))
        - (Φ (c - (T : ℂ) * Complex.I) - (c - (T : ℂ) * Complex.I))‖
      ≤ ∫ t in T..M, (C₂ / (t - (Ξ + 1)) + K / t) :=
    dev_vert_le_of_diffAt_neg (x := c) (y₁ := T) (y₂ := M)
      (g := fun t : ℝ => C₂ / (t - (Ξ + 1)) + K / t) hTM hdiff hg hgcont
  -- the antiderivative of the majorant
  have hderiv : ∀ t ∈ Set.uIcc T M,
      HasDerivAt (fun s : ℝ => C₂ * Real.log (s - (Ξ + 1)) + K * Real.log s)
        (C₂ / (t - (Ξ + 1)) + K / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hTM] at ht
    have ht1 : 0 < t - (Ξ + 1) := by have := ht.1; linarith
    have ht2 : 0 < t := by have := ht.1; linarith
    have h1 : HasDerivAt (fun s : ℝ => s - (Ξ + 1)) 1 t := (hasDerivAt_id t).sub_const (Ξ + 1)
    have h2 : HasDerivAt (fun s : ℝ => Real.log (s - (Ξ + 1))) (1 / (t - (Ξ + 1))) t :=
      h1.log (ne_of_gt ht1)
    have h3 : HasDerivAt (fun s : ℝ => C₂ * Real.log (s - (Ξ + 1)))
        (C₂ * (1 / (t - (Ξ + 1)))) t := h2.const_mul C₂
    have h4 : HasDerivAt (fun s : ℝ => Real.log s) (1 / t) t := by
      simpa [one_div] using Real.hasDerivAt_log (ne_of_gt ht2)
    have h5 : HasDerivAt (fun s : ℝ => K * Real.log s) (K * (1 / t)) t := h4.const_mul K
    have hsum := h3.add h5
    have e1 : C₂ * (1 / (t - (Ξ + 1))) = C₂ / (t - (Ξ + 1)) := by ring
    have e2 : K * (1 / t) = K / t := by ring
    rw [e1, e2] at hsum
    exact hsum
  have hint : IntervalIntegrable (fun t : ℝ => C₂ / (t - (Ξ + 1)) + K / t) volume T M := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hTM]
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- the closed form of the integral
  have eM : M - (Ξ + 1) = M - Ξ - 1 := by ring
  have eT : T - (Ξ + 1) = T - Ξ - 1 := by ring
  have key : (C₂ * Real.log (M - (Ξ + 1)) + K * Real.log M)
        - (C₂ * Real.log (T - (Ξ + 1)) + K * Real.log T)
      = C₂ * Real.log ((M - Ξ - 1) / (T - Ξ - 1)) + K * Real.log (M / T) := by
    rw [eM, eT, Real.log_div (ne_of_gt hMden) (ne_of_gt hTden),
      Real.log_div (ne_of_gt hMpos) (ne_of_gt hTpos)]
    ring
  calc ‖(Φ (c - (M : ℂ) * Complex.I) - (c - (M : ℂ) * Complex.I))
        - (Φ (c - (T : ℂ) * Complex.I) - (c - (T : ℂ) * Complex.I))‖
      ≤ ∫ t in T..M, (C₂ / (t - (Ξ + 1)) + K / t) := hmain
    _ = (C₂ * Real.log (M - (Ξ + 1)) + K * Real.log M)
        - (C₂ * Real.log (T - (Ξ + 1)) + K * Real.log T) := hF
    _ = C₂ * Real.log ((M - Ξ - 1) / (T - Ξ - 1)) + K * Real.log (M / T) := key

end Work.Pert.Pin3
