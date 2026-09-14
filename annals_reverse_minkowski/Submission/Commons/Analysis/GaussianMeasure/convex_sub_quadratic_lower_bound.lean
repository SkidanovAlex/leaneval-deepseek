import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace Commons.Analysis.GaussianMeasure

open Filter
open scoped Topology

/-- A convex function on a convex set lies above its tangent (supporting) hyperplane at any
point where it is Fréchet differentiable. -/
private theorem convexOn_le_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {s : Set E} (hg : ConvexOn ℝ s g) {x : E} (hx : x ∈ s)
    {L : E →L[ℝ] ℝ} (hL : HasFDerivAt g L x) {y : E} (hy : y ∈ s) :
    g x + L (y - x) ≤ g y := by
  set v : E := y - x with hv
  have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id' (x := (0 : ℝ))).smul_const v
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 :=
    (hasDerivAt_const_add_iff (x := (0 : ℝ)) x).2 h1
  have hcomp : HasDerivAt (g ∘ fun t : ℝ => x + t • v) (L v) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hL hline (by simp)
  have htend : Tendsto (fun t : ℝ => t⁻¹ • (g (x + t • v) - g x)) (𝓝[>] (0 : ℝ)) (𝓝 (L v)) := by
    simpa [Function.comp_def] using hcomp.tendsto_slope_zero_right
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (g (x + t • v) - g x) ≤ g y - g x := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio 1 by norm_num)] with t ht1 ht0
    have ht0' : 0 < t := ht0
    have ht1' : t < 1 := ht1
    have hcv := hg.2 hx hy (show (0 : ℝ) ≤ 1 - t by linarith) (show (0 : ℝ) ≤ t by linarith)
      (show (1 - t) + t = 1 by ring)
    have hxy : (1 - t) • x + t • y = x + t • v := by
      rw [hv]; module
    rw [hxy] at hcv
    have hle : g (x + t • v) - g x ≤ t • (g y - g x) := by
      simp only [smul_eq_mul] at hcv ⊢
      linarith
    have hfin := smul_le_smul_of_nonneg_left hle (inv_nonneg.mpr ht0'.le)
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt ht0'), one_smul] at hfin
  have hmain : L v ≤ g y - g x := le_of_tendsto htend hevent
  linarith

theorem convex_sub_quadratic_lower_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (hf : DifferentiableAt ℝ f 0)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) :
    ∃ c : ℝ, ∀ x : E, f x ≥ Real.pi / 2 * ‖x‖ ^ 2 - c := by
  set g : E → ℝ := fun x => f x - Real.pi * ‖x‖ ^ 2 with hg
  have hgconv : ConvexOn ℝ Set.univ g := by rw [hg]; exact hconv
  set L : E →L[ℝ] ℝ := fderiv ℝ f 0 with hLdef
  have hfL : HasFDerivAt f L 0 := by rw [hLdef]; exact hf.hasFDerivAt
  have hns : HasFDerivAt (fun x : E => ‖x‖ ^ 2) (0 : E →L[ℝ] ℝ) 0 := by
    have h := (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
    simpa using h
  have hgL : HasFDerivAt g L 0 := by
    rw [hg]
    have h2 : HasFDerivAt (fun x : E => Real.pi * ‖x‖ ^ 2) (Real.pi • (0 : E →L[ℝ] ℝ)) 0 :=
      hns.const_smul Real.pi
    have h3 : HasFDerivAt (fun x : E => f x - Real.pi * ‖x‖ ^ 2)
        (L - Real.pi • (0 : E →L[ℝ] ℝ)) 0 := hfL.sub h2
    simpa using h3
  refine ⟨‖L‖ ^ 2 / (2 * Real.pi) - f 0, fun x => ?_⟩
  have hsub := convexOn_le_fderiv hgconv (Set.mem_univ (0 : E)) hgL (Set.mem_univ x)
  have hsub' : f 0 + L x ≤ f x - Real.pi * ‖x‖ ^ 2 := by
    simpa [hg, sub_zero] using hsub
  have hLx : -(‖L‖ * ‖x‖) ≤ L x := by
    have h1 : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
    have h2 : ‖L x‖ = |L x| := Real.norm_eq_abs (L x)
    have h3 : -(L x) ≤ |L x| := neg_le_abs (L x)
    linarith
  have hquad : -(‖L‖ ^ 2 / (2 * Real.pi)) ≤ L x + Real.pi / 2 * ‖x‖ ^ 2 := by
    have hsq : 0 ≤ (Real.pi * ‖x‖ - ‖L‖) ^ 2 := sq_nonneg _
    have hkey : -(‖L‖ ^ 2) ≤ (Real.pi / 2 * ‖x‖ ^ 2 - ‖L‖ * ‖x‖) * (2 * Real.pi) := by
      nlinarith [hsq]
    have hkey' : -(‖L‖ ^ 2 / (2 * Real.pi)) ≤ Real.pi / 2 * ‖x‖ ^ 2 - ‖L‖ * ‖x‖ := by
      rw [show -(‖L‖ ^ 2 / (2 * Real.pi)) = -(‖L‖ ^ 2) / (2 * Real.pi) by ring]
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr hkey
    linarith
  linarith [hsub', hquad]

end Commons.Analysis.GaussianMeasure