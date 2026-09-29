import Mathlib
import Submission.Work.C17g.segment_deriv
import Submission.Work.C17g.segment_FTC
import Submission.Work.C17g.integrand_lipschitz

/-!
# The segment integral is a primitive

For `S ⊆ ℂ` open and convex, `z₀ ∈ S`, `f : ℂ → E` holomorphic (`E` a complex Banach
space), the "segment integral"

  `g z = (z - z₀) • ∫ t in 0..1, f (z₀ + t • (z - z₀))`

is an antiderivative of `f` on `S`: `g` is complex differentiable on `S` with `g' z = f z`.

The proof differentiates the parameter integral (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip`)
and evaluates the resulting integral by the fundamental theorem of calculus.
-/

namespace Work.C17g

open MeasureTheory Set intervalIntegral
open scoped Topology

theorem segment_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S) {z₀ : ℂ} (hz₀ : z₀ ∈ S)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun z => (z - z₀) • ∫ t in (0:ℝ)..1, f (z₀ + t • (z - z₀))) S ∧
      ∀ z ∈ S, HasDerivAt (fun z => (z - z₀) • ∫ t in (0:ℝ)..1, f (z₀ + t • (z - z₀))) (f z) z := by
  have hmem : ∀ w ∈ S, ∀ t ∈ Set.Icc (0:ℝ) 1, z₀ + t • (w - z₀) ∈ S := by
    intro w hw t ht
    have h1 : (AffineMap.lineMap z₀ w) t ∈ S :=
      hS.segment_subset hz₀ hw (lineMap_mem_segment ℝ z₀ w ht)
    simpa [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, add_comm] using h1
  have hii : ∀ t ∈ Set.uIoc (0:ℝ) 1, t ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
    exact ⟨ht.1.le, ht.2⟩
  have hii2 : ∀ t ∈ Set.uIcc (0:ℝ) 1, t ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht; rwa [Set.uIcc_of_le zero_le_one] at ht
  have key : ∀ z ∈ S, HasDerivAt (fun z => (z - z₀) • ∫ t in (0:ℝ)..1, f (z₀ + t • (z - z₀))) (f z) z := by
    intro z hz
    obtain ⟨ρ, bound, hρ, hball, hlip, hbint⟩ := integrand_lipschitz hS hSo hz₀ hf z hz
    have haff : Continuous (fun t : ℝ => z₀ + t • (z - z₀)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hFmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
        (fun t : ℝ => (x - z₀) • f (z₀ + t • (x - z₀))) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
      filter_upwards [Metric.ball_mem_nhds z hρ] with x hx
      have hcx : Continuous (fun t : ℝ => z₀ + t • (x - z₀)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      exact (hf.continuousOn.comp hcx.continuousOn
        (fun t ht => hmem x (hball hx) t (hii t ht))).const_smul (x - z₀)
    have hFint : IntervalIntegrable (fun t : ℝ => (z - z₀) • f (z₀ + t • (z - z₀))) volume (0:ℝ) 1 := by
      apply ContinuousOn.intervalIntegrable
      exact (hf.continuousOn.comp haff.continuousOn
        (fun t ht => hmem z hz t (hii2 t ht))).const_smul (z - z₀)
    have hdercont : ContinuousOn (fun t : ℝ => deriv f (z₀ + t • (z - z₀))) (Set.uIoc (0:ℝ) 1) :=
      (hf.deriv hSo).continuousOn.comp haff.continuousOn
        (fun t ht => hmem z hz t (hii t ht))
    have hF'meas : AEStronglyMeasurable
        (fun t : ℝ => f (z₀ + t • (z - z₀)) + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀))))
        (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      have hpart : ContinuousOn (fun t : ℝ => t • deriv f (z₀ + t • (z - z₀))) (Set.uIoc (0:ℝ) 1) := by
        have hsm : ContinuousOn (fun t : ℝ => (t : ℂ) • deriv f (z₀ + t • (z - z₀)))
            (Set.uIoc (0:ℝ) 1) := (Complex.continuous_ofReal.continuousOn).smul hdercont
        refine ContinuousOn.congr hsm ?_
        intro t ht; simp
      exact (hf.continuousOn.comp haff.continuousOn
        (fun t ht => hmem z hz t (hii t ht))).add (hpart.const_smul (z - z₀))
    have hlip' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 → LipschitzOnWith (Real.nnabs (bound t))
        (fun x : ℂ => (x - z₀) • f (z₀ + t • (x - z₀))) (Metric.ball z ρ) := by
      filter_upwards with t ht
      exact hlip t (hii t ht)
    have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 → HasDerivAt
        (fun x : ℂ => (x - z₀) • f (z₀ + t • (x - z₀)))
        (f (z₀ + t • (z - z₀)) + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀)))) z := by
      filter_upwards with t ht
      exact segment_deriv (hf.differentiableAt (hSo.mem_nhds (hmem z hz t (hii t ht))))
    obtain ⟨_, hderiv⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
      (𝕜 := ℂ) (μ := volume) (a := (0:ℝ)) (b := 1) (x₀ := z) (s := Metric.ball z ρ)
      (Metric.ball_mem_nhds z hρ) hFmeas hFint hF'meas hlip' hbint hdiff
    have hfun : (fun x : ℂ => ∫ t in (0:ℝ)..1, (x - z₀) • f (z₀ + t • (x - z₀)))
        = fun x : ℂ => (x - z₀) • ∫ t in (0:ℝ)..1, f (z₀ + t • (x - z₀)) := by
      funext x; rw [intervalIntegral.integral_smul]
    have hval : (∫ t in (0:ℝ)..1, f (z₀ + t • (z - z₀)) + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀)))) = f z :=
      segment_FTC hS hSo hz₀ hz hf
    rw [hfun, hval] at hderiv
    exact hderiv
  exact ⟨fun z hz => (key z hz).differentiableAt.differentiableWithinAt, key⟩

end Work.C17g
