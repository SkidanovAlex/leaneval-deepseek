import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.dbar_representation
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.integral_dbar_eq_zero
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.Defs

/-!
# Setup for Grönwall's area theorem: the auxiliary function `φ` and the winding number `wind`

For `g` holomorphic on the exterior `{1 < ‖z‖}` of the unit disc with `g(w) = w + b/w + O(w⁻²)`
at infinity we define

* `phi g u = g u⁻¹ - u⁻¹` (and `0` at `u = 0`), the "coefficient generating function", which
  extends analytically to the unit disc (`analyticOnNhd_phi`), and
* `wind g r ζ`, the winding number of the curve `z ↦ g z` over `‖z‖ = r` about `ζ`.

The results here are used by the proof of the area theorem; they are collected separately so that
other developments can import them without importing the (long) main file.
-/

open MeasureTheory Filter Topology
open scoped Topology

namespace Work.Repel.Koebe


/-- `φ g u = g u⁻¹ - u⁻¹` for `u ≠ 0`, and `0` at `u = 0`. -/
noncomputable def phi (g : ℂ → ℂ) (u : ℂ) : ℂ := if u = 0 then 0 else g u⁻¹ - u⁻¹

/-- The winding number of the curve `z ↦ g z` along the circle `‖z‖ = r` about `ζ`. -/
noncomputable def wind (g : ℂ → ℂ) (r : ℝ) (ζ : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral (fun z : ℂ => deriv g z / (g z - ζ)) 0 r

variable {g : ℂ → ℂ} {b : ℂ}

lemma phi_apply {u : ℂ} (hu : u ≠ 0) : phi g u = g u⁻¹ - u⁻¹ := by
  simp [phi, hu]

lemma phi_zero : phi g 0 = 0 := by simp [phi]

/-- `φ` is continuous at the origin: the hypothesis says `φ u / u → b`. -/
lemma phi_tendsto_zero
    (hlim : Tendsto (fun u : ℂ => (g u⁻¹ - u⁻¹) / u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds b)) :
    Tendsto (phi g) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds 0) := by
  have hid : Tendsto (fun u : ℂ => u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun u : ℂ => u * ((g u⁻¹ - u⁻¹) / u)) (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds (0 * b)) := hid.mul hlim
  have h2 : (fun u : ℂ => u * ((g u⁻¹ - u⁻¹) / u)) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
      (fun u : ℂ => phi g u) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [phi_apply hu, mul_div_cancel₀ _ hu]
  have h3 : Tendsto (fun u : ℂ => phi g u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (0 * b)) :=
    h1.congr' h2
  simpa using h3

/-- `φ` is continuous at the origin (as a plain `ContinuousAt`). -/
lemma phi_continuousAt_zero
    (hlim : Tendsto (fun u : ℂ => (g u⁻¹ - u⁻¹) / u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds b)) :
    ContinuousAt (phi g) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp (phi_tendsto_zero hlim)) ε hε
  refine ⟨δ, hδ0, fun u hu => ?_⟩
  by_cases h : u = 0
  · subst h; simpa using hε
  · simpa [phi_zero] using hδ (by simpa using h) hu

/-- `φ` is analytic at every nonzero point of the open unit disc. -/
lemma analyticAt_phi_of_ne (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    {u : ℂ} (hu : u ≠ 0) (hu1 : ‖u‖ < 1) : AnalyticAt ℂ (phi g) u := by
  have hnorm : 1 < ‖u⁻¹‖ := by
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hu)).mpr hu1
  have hid : AnalyticAt ℂ (id : ℂ → ℂ) u := analyticAt_id
  have hinv : AnalyticAt ℂ (fun w : ℂ => w⁻¹) u :=
    (hid.inv hu).congr (Filter.Eventually.of_forall fun w => by simp)
  have hcomp : AnalyticAt ℂ (fun w : ℂ => g w⁻¹ - w⁻¹) u := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => g w⁻¹) u := AnalyticAt.comp (hg u⁻¹ hnorm) hinv
    exact (h1.sub hinv).congr (Filter.Eventually.of_forall fun w => by simp)
  refine hcomp.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hu] with w hw
  exact (phi_apply hw).symm

/-- The slope of `φ` at `0` is the function whose limit is `b`. -/
lemma slope_phi_eventuallyEq
    (hlim : Tendsto (fun u : ℂ => (g u⁻¹ - u⁻¹) / u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds b)) :
    Tendsto (slope (phi g) 0) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds b) := by
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [slope_def_field, phi_apply hu, phi_zero, sub_zero]
  ring_nf

/-- `φ` has derivative `b` at the origin. -/
lemma deriv_phi_zero
    (hlim : Tendsto (fun u : ℂ => (g u⁻¹ - u⁻¹) / u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds b)) :
    deriv (phi g) 0 = b :=
  (hasDerivAt_iff_tendsto_slope.mpr (slope_phi_eventuallyEq hlim)).deriv

/-- The analyticity of `φ` on the unit disc (removable singularity at `0`). -/
lemma analyticOnNhd_phi
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hlim : Tendsto (fun u : ℂ => (g u⁻¹ - u⁻¹) / u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds b)) :
    AnalyticOnNhd ℂ (phi g) (Metric.ball (0 : ℂ) 1) := by
  intro u hu
  rcases eq_or_ne u 0 with rfl | hu0
  · have hdiff : ∀ᶠ u in nhdsWithin (0 : ℂ) ({0}ᶜ), DifferentiableAt ℂ (phi g) u := by
      have hball : Metric.ball (0:ℂ) 1 ∈ nhdsWithin (0:ℂ) ({0}ᶜ) :=
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1))
      filter_upwards [self_mem_nhdsWithin, hball] with u hu0 hu1
      exact (analyticAt_phi_of_ne hg hu0 (by simpa [Metric.mem_ball, dist_zero_right] using hu1)).differentiableAt
    exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff
      (phi_continuousAt_zero hlim)
  · exact analyticAt_phi_of_ne hg hu0 (by simpa [Metric.mem_ball, dist_zero_right] using hu)

/-- **Bound at infinity**: for large `‖z‖`, `‖g z - z‖ ≤ 1/2`. -/
lemma exists_bound_sub_id
    (hlim : Tendsto (fun u : ℂ => (g u⁻¹ - u⁻¹) / u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds b)) :
    ∃ R : ℝ, 1 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2 := by
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp (phi_tendsto_zero hlim)) (1 / 2) (by norm_num)
  refine ⟨max 2 (2 / δ), lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun z hz => ?_⟩
  have hRpos : 0 < max 2 (2 / δ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hRpos hz
  have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
  have hdist : dist (z⁻¹) 0 < δ := by
    rw [dist_zero_right, norm_inv]
    have h1 : (max 2 (2 / δ))⁻¹ ≤ δ / 2 := by
      rw [inv_le_comm₀ hRpos (by positivity), inv_div]
      exact le_max_right _ _
    calc ‖z‖⁻¹ ≤ (max 2 (2 / δ))⁻¹ := inv_anti₀ hRpos hz
      _ ≤ δ / 2 := h1
      _ < δ := by linarith
  have hthis : dist (phi g (z⁻¹)) 0 < 1 / 2 := hδ (by simpa using inv_ne_zero hzne) hdist
  have hkey : ‖g z - z‖ < 1 / 2 := by
    simpa [phi_apply (inv_ne_zero hzne), inv_inv, dist_zero_right] using hthis
  exact le_of_lt hkey


end Work.Repel.Koebe
