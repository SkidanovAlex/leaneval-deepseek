import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Submission.Commons.Analysis.Complex.Harmonic.max_principle_subharmonic_open

namespace Commons.Analysis.Complex.Harmonic

open Set Metric

/-- **Comparison criterion on an arbitrary bounded connected open set**: let `v` be
continuous on an open set `Ω ⊆ ℂ` and satisfy the circle mean-value inequality everywhere
on `Ω`, and let `Ω'` be an open, preconnected, bounded subset of `Ω` with
`closure Ω' ⊆ Ω`. If `h` is harmonic on `Ω'`, continuous on `closure Ω'`, and satisfies
`v ≤ h` on the boundary `closure Ω' \ Ω'`, then `v ≤ h` on `Ω'`.

Proof: apply `max_principle_subharmonic_open` to `v - h` (continuous on `closure Ω'`, circle
mean-value inequality at interior points — from `v` and from the harmonicity of `h` — and
boundary values ≤ 0). -/
theorem subharmonic_le_harmonic_on_open {Ω Ω' : Set ℂ} (hΩopen : IsOpen Ω) {v : ℂ → ℝ}
    (hcont : ContinuousOn v Ω)
    (hMVP : ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
      v p ≤ Real.circleAverage v p r)
    (hΩ'open : IsOpen Ω') (hΩ'conn : IsPreconnected Ω') (hΩ'bdd : Bornology.IsBounded Ω')
    (hclosure : closure Ω' ⊆ Ω)
    {h : ℂ → ℝ} (hharm : InnerProductSpace.HarmonicOnNhd h Ω')
    (hcont_h : ContinuousOn h (closure Ω'))
    (hbd : ∀ z ∈ closure Ω', z ∉ Ω' → v z ≤ h z) :
    ∀ z ∈ Ω', v z ≤ h z := by
  have hcont_v_cl : ContinuousOn v (closure Ω') := hcont.mono hclosure
  have hcont_w : ContinuousOn (fun x : ℂ => v x - h x) (closure Ω') :=
    hcont_v_cl.sub hcont_h
  have hsub_w : ∀ p ∈ Ω', ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω' →
      (fun x : ℂ => v x - h x) p ≤ Real.circleAverage (fun x : ℂ => v x - h x) p r := by
    intro p hp r hr hclsub
    have hclsub_Ω : Metric.closedBall p r ⊆ Ω :=
      fun y hy => hclosure (subset_closure (hclsub hy))
    have hvle : v p ≤ Real.circleAverage v p r := hMVP p (hclosure (subset_closure hp)) r hr hclsub_Ω
    have hharm_ball : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall p |r|) := by
      rw [abs_of_pos hr]; exact hharm.mono hclsub
    have havg_h : Real.circleAverage h p r = h p := hharm_ball.circleAverage_eq
    have hsphereΩ : Metric.sphere p |r| ⊆ Ω := by
      rw [abs_of_pos hr]
      exact fun y hy => hclosure (subset_closure (hclsub (Metric.sphere_subset_closedBall hy)))
    have hsphere_cl : Metric.sphere p |r| ⊆ closure Ω' := by
      rw [abs_of_pos hr]
      exact fun y hy => subset_closure (hclsub (Metric.sphere_subset_closedBall hy))
    have hvint : CircleIntegrable v p r := (hcont.mono hsphereΩ).circleIntegrable'
    have hhint : CircleIntegrable h p r := (hcont_h.mono hsphere_cl).circleIntegrable'
    have havg_w : Real.circleAverage (fun x : ℂ => v x - h x) p r
        = Real.circleAverage v p r - Real.circleAverage h p r :=
      Real.circleAverage_fun_sub hvint hhint
    rw [havg_w, havg_h]
    linarith
  have hbd_w : ∀ z ∈ closure Ω', z ∉ Ω' → (fun x : ℂ => v x - h x) z ≤ 0 := by
    intro z hzcl hzn
    have hz := hbd z hzcl hzn
    show v z - h z ≤ 0
    linarith
  have hres := max_principle_subharmonic_open hΩ'open hΩ'conn hΩ'bdd hcont_w hsub_w hbd_w
  intro z hz
  have hz' := hres z hz
  show v z ≤ h z
  linarith

end Commons.Analysis.Complex.Harmonic