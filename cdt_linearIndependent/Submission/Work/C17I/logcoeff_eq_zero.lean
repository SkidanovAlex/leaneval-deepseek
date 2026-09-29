import Mathlib
import Submission.Work.C17.acl_log_compare

open Filter Metric
open scoped Topology

namespace Work.C17I

/-- Guidance from the requester (area C17, input for `Work.C17.relation_to_LC`).

# Extraction of the coefficient of `log (s - ·)`

`A · (· - s)^m · log (s - ·) + G` (with `A`, `G` holomorphic on `ball s δ`) is assumed to vanish
on the *lens* `ball s δ ∩ ball 0 s` (one side of the branch point `s`).  The conclusion is that the
coefficient `A` vanishes on the whole ball `ball s δ`.

Route: substitute `u = z - s`; then `z - s = u`, `s - z = -u` and the hypothesis becomes
`A (s+u) · u^m · log (-u) + G (s+u) = 0` on `ball(0,δ) ∩ ball(-s,s)`, i.e.
`(A (s+u) u^m) * log (-u) = -(G (s+u))`, which is exactly the situation of
`Work.C17.log_neg_compare` (proved in `Submission.Work.C17.acl_log_compare`): it gives
`A (s+u) · u^m = 0` for all `‖u‖ < δ`.  For `z ≠ s` this is `A z = 0` (divide by the nonzero
`m`-th power), and `A s = 0` follows from the continuity of `A` at `s` together with
`tendsto_nhds_unique` for the two limits of `A` along `𝓝[≠] s`.

The auxiliary lemmas about moving the centre (`u ↦ s + u` maps `ball 0 δ` to `ball s δ`, and
`ball(-s,s)` to the lens) are the only technical steps. -/
theorem logcoeff_eq_zero {s : ℝ} {δ : ℝ} (hδ : 0 < δ) (hs : 0 < s) {m : ℕ}
    {A G : ℂ → ℂ} (hA : DifferentiableOn ℂ A (Metric.ball (s : ℂ) δ))
    (hG : DifferentiableOn ℂ G (Metric.ball (s : ℂ) δ))
    (hid : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) s,
      A z * (z - s) ^ m * Complex.log (s - z) + G z = 0) :
    ∀ z ∈ Metric.ball (s : ℂ) δ, A z = 0 := by
  -- the translation `u ↦ s + u` carries `ball 0 δ` into `ball s δ`
  have hshift : DifferentiableOn ℂ (fun u : ℂ => (s : ℂ) + u) (Metric.ball (0 : ℂ) δ) :=
    (differentiableOn_const (s : ℂ)).add differentiableOn_id
  have hmaps : Set.MapsTo (fun u : ℂ => (s : ℂ) + u) (Metric.ball (0 : ℂ) δ)
      (Metric.ball (s : ℂ) δ) := by
    intro u hu
    rw [mem_ball, Complex.dist_eq, sub_zero] at hu
    rw [mem_ball, Complex.dist_eq]
    show ‖(s : ℂ) + u - s‖ < δ
    rwa [show (s : ℂ) + u - s = u by ring]
  -- the coefficient of `log (-·)` after the substitution
  have hA' : DifferentiableOn ℂ (fun u : ℂ => A ((s : ℂ) + u) * u ^ m)
      (Metric.ball (0 : ℂ) δ) :=
    (hA.comp hshift hmaps).mul (differentiableOn_id.pow m)
  -- and the holomorphic remainder (with a possible singularity only at `0`)
  have hshift' : DifferentiableOn ℂ (fun u : ℂ => (s : ℂ) + u) (Metric.ball (0 : ℂ) δ \ {0}) :=
    (differentiableOn_const (s : ℂ)).add differentiableOn_id
  have hmaps' : Set.MapsTo (fun u : ℂ => (s : ℂ) + u) (Metric.ball (0 : ℂ) δ \ {0})
      (Metric.ball (s : ℂ) δ) := fun u hu => hmaps hu.1
  have hB' : DifferentiableOn ℂ (fun u : ℂ => -(G ((s : ℂ) + u))) (Metric.ball (0 : ℂ) δ \ {0}) :=
    (hG.comp hshift' hmaps').neg
  -- the two sides agree on the lens `ball 0 δ ∩ ball (-s) s`
  have hid' : ∀ u ∈ Metric.ball (0 : ℂ) δ ∩ Metric.ball (-(s : ℂ)) s,
      (A ((s : ℂ) + u) * u ^ m) * Complex.log (-u) = -(G ((s : ℂ) + u)) := by
    intro u hu
    have hz1 : (s : ℂ) + u ∈ Metric.ball (s : ℂ) δ := hmaps hu.1
    have hz2 : (s : ℂ) + u ∈ Metric.ball (0 : ℂ) s := by
      rw [mem_ball, Complex.dist_eq, sub_zero]
      have h6 := hu.2
      rw [mem_ball, Complex.dist_eq] at h6
      show ‖(s : ℂ) + u‖ < s
      rwa [show (s : ℂ) + u = u - (-(s : ℂ)) by ring]
    have h := hid ((s : ℂ) + u) ⟨hz1, hz2⟩
    rw [show (s : ℂ) + u - s = u by ring, show (s : ℂ) - ((s : ℂ) + u) = -u by ring] at h
    exact eq_neg_of_add_eq_zero_left h
  -- the branch-cut comparison at `0` kills the shifted coefficient
  have hmain := Work.C17.log_neg_compare hδ hs (fun u : ℂ => A ((s : ℂ) + u) * u ^ m)
    (fun u : ℂ => -(G ((s : ℂ) + u))) hA' hB' hid'
  -- off the centre this finishes by dividing by the nonzero power
  have hne : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ s → A z = 0 := by
    intro z hz hzs
    have hzδ : z - s ∈ Metric.ball (0 : ℂ) δ := by
      rw [mem_ball, Complex.dist_eq, sub_zero]
      have h5 := hz
      rwa [mem_ball, Complex.dist_eq] at h5
    have h0 := hmain (z - s) hzδ
    rw [show (s : ℂ) + (z - s) = z by ring] at h0
    exact (mul_eq_zero.mp h0).resolve_right (pow_ne_zero m (sub_ne_zero.mpr hzs))
  intro z hz
  by_cases hzs : z = s
  · -- at the centre use continuity of `A` and uniqueness of limits along `𝓝[≠] s`
    subst hzs
    have hcont : ContinuousAt A (s : ℂ) :=
      hA.continuousOn.continuousAt (Metric.ball_mem_nhds (s : ℂ) hδ)
    have heq0 : (fun z : ℂ => A z) =ᶠ[𝓝[≠] (s : ℂ)] 0 := by
      rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (s : ℂ) hδ] with z hzball hzne
      exact hne z hzball (by simpa using hzne)
    have hlim0 : Tendsto A (𝓝[≠] (s : ℂ)) (𝓝 0) :=
      Filter.Tendsto.congr' heq0.symm tendsto_const_nhds
    have hlimA : Tendsto A (𝓝[≠] (s : ℂ)) (𝓝 (A (s : ℂ))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hlimA hlim0
  · exact hne z hz hzs

end Work.C17I
