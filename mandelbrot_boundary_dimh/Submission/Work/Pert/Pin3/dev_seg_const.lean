import Mathlib
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.dev_vert_le

/-!
# `Work.Pert.Pin3.dev_seg_const`

Displacement bound for `Φ - id` along a **straight segment** `t ↦ p + t • (q - p)`, `t ∈ [0, 1]`.

If `Φ` is complex differentiable on the whole segment and the deviation `Φ' - 1` is bounded on the
segment by the constant `Λ`, then

  `‖(Φ q - q) - (Φ p - p)‖ ≤ Λ * ‖q - p‖`.

The proof is the fundamental estimate "displacement ≤ integral of the speed"
(`norm_sub_le_integral_of_norm_deriv_le_of_le`) applied to the curve
`t ↦ Φ (p + t • (q - p)) - (p + t • (q - p))`, whose derivative is
`(Φ' (p + t • (q - p)) - 1) * (q - p)`, of norm `≤ Λ * ‖q - p‖`.  It is the constant-bound,
arbitrary-direction analogue of `Work.Pert.dev_vert_le` / `Work.Pert.V5.dev_horiz_le`.
-/

set_option linter.unusedVariables false

namespace Work.Pert.Pin3

theorem dev_seg_const {Φ : ℂ → ℂ} {p q : ℂ} {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ Φ (p + t • (q - p)))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv Φ (p + t • (q - p)) - 1‖ ≤ Λ) :
    ‖(Φ q - q) - (Φ p - p)‖ ≤ Λ * ‖q - p‖ := by
  -- the straight parametrisation of the segment and the deviation along it
  let γ : ℝ → ℂ := fun t => p + t • (q - p)
  let f : ℝ → ℂ := fun t => Φ (γ t) - γ t
  -- `γ` is the curve `t ↦ p + t • (q - p)`, with derivative `q - p`
  have hγ : ∀ t : ℝ, HasDerivAt γ (q - p) t := by
    intro t
    have h : HasDerivAt (fun u : ℝ => u • (q - p)) ((1 : ℝ) • (q - p)) t :=
      (hasDerivAt_id t).smul_const (q - p)
    have h2 : HasDerivAt (fun u : ℝ => p + u • (q - p)) ((1 : ℝ) • (q - p)) t :=
      h.const_add p
    simpa [γ, one_smul] using h2
  -- `f` is differentiable on the interval, with derivative `(Φ' (γ t) - 1) * (q - p)`
  have hfd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f ((deriv Φ (γ t) - 1) * (q - p)) t := by
    intro t ht
    have hdt : DifferentiableAt ℂ Φ (γ t) := by
      simpa [γ] using hdiff t ht
    have hcomp : HasDerivAt (fun u : ℝ => Φ (γ u)) (deriv Φ (γ t) * (q - p)) t :=
      hdt.hasDerivAt.comp t (hγ t)
    have hsub : HasDerivAt (fun u : ℝ => Φ (γ u) - γ u)
        (deriv Φ (γ t) * (q - p) - (q - p)) t := hcomp.sub (hγ t)
    have he : deriv Φ (γ t) * (q - p) - (q - p) = (deriv Φ (γ t) - 1) * (q - p) := by ring
    rw [he] at hsub
    simpa [f] using hsub
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le (f := f)
    (B := fun _ => Λ * ‖q - p‖) (a := 0) (b := 1) zero_le_one
    -- continuity on the closed interval
    (fun t ht => (hfd t ht).continuousAt.continuousWithinAt)
    -- differentiability on the open interval
    (fun t ht => (hfd t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt)
    -- the pointwise bound on the norm of the derivative, a.e.
    (by
      filter_upwards with t ht
      rw [(hfd t (Set.Ioo_subset_Icc_self ht)).deriv, norm_mul]
      exact mul_le_mul_of_nonneg_right (hbd t (Set.Ioo_subset_Icc_self ht)) (norm_nonneg _))
    -- integrability of the (constant) majorant
    intervalIntegrable_const
  have h1 : γ (1 : ℝ) = q := by simp [γ]
  have h0 : γ (0 : ℝ) = p := by simp [γ]
  simp only [f, h1, h0] at hmain
  have hint : (∫ t in (0 : ℝ)..1, Λ * ‖q - p‖) = Λ * ‖q - p‖ := by simp
  rw [hint] at hmain
  exact hmain

end Work.Pert.Pin3
