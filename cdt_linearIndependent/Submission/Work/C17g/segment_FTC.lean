import Mathlib

namespace Work.C17g

open MeasureTheory intervalIntegral

theorem segment_FTC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S) {z₀ z : ℂ} (hz₀ : z₀ ∈ S) (hz : z ∈ S)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f S) :
    ∫ t in (0:ℝ)..1, (f (z₀ + t • (z - z₀)) + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀)))) = f z := by
  -- The segment from `z₀` to `z` lies in `S`.
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, z₀ + t • (z - z₀) ∈ S := by
    intro t ht
    have h1 : 0 ≤ 1 - t := by linarith [ht.2]
    have h2 : 0 ≤ t := ht.1
    have h3 : (1 - t) + t = 1 := by ring
    have h4 := hS hz₀ hz h1 h2 h3
    have heq : z₀ + t • (z - z₀) = (1 - t) • z₀ + t • z := by
      simp only [Complex.real_smul]; push_cast; ring
    rwa [heq]
  -- `f` is analytic on the open set `S` (this is where completeness of `E` is used).
  have hana : AnalyticOnNhd ℂ f S := hf.analyticOnNhd hSo
  -- Derivative of the antiderivative `t ↦ t • f (z₀ + t • (z - z₀))`.
  have hF : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun s : ℝ => s • f (z₀ + s • (z - z₀)))
      (f (z₀ + t • (z - z₀)) + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀)))) t := by
    intro t ht
    have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hpt := hmem t htI
    have hdiff : DifferentiableAt ℂ f (z₀ + t • (z - z₀)) :=
      hf.differentiableAt (hSo.mem_nhds hpt)
    have hline : HasDerivAt (fun s : ℝ => z₀ + s • (z - z₀)) (z - z₀) t := by
      simpa using ((hasDerivAt_id t).smul_const (z - z₀)).const_add z₀
    have hcomp := (hdiff.hasDerivAt).scomp t hline
    have h := (hasDerivAt_id t).smul hcomp
    have key : id t • ((z - z₀) • deriv f (z₀ + t • (z - z₀))) + (1:ℝ) • f (z₀ + t • (z - z₀))
        = f (z₀ + t • (z - z₀)) + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀))) := by
      have h1 : id t = t := rfl
      rw [h1, one_smul, smul_comm t (z - z₀) (deriv f (z₀ + t • (z - z₀))), add_comm]
    simp only [Function.comp_apply] at h
    rw [key] at h
    exact h
  have hline_c : ContinuousOn (fun s : ℝ => z₀ + s • (z - z₀)) (Set.Icc (0:ℝ) 1) := by fun_prop
  have h1 : ContinuousOn (fun s : ℝ => f (z₀ + s • (z - z₀))) (Set.Icc (0:ℝ) 1) :=
    hana.continuousOn.comp hline_c hmem
  have hcontF : ContinuousOn (fun s : ℝ => s • f (z₀ + s • (z - z₀))) (Set.Icc (0:ℝ) 1) :=
    (continuous_id.continuousOn).smul h1
  -- The integrand is continuous on `[0,1]`, hence interval integrable.
  have hderiv : ContinuousOn (fun t : ℝ => deriv f (z₀ + t • (z - z₀))) (Set.Icc (0:ℝ) 1) :=
    hana.deriv.continuousOn.comp hline_c hmem
  have hcont' : ContinuousOn (fun t : ℝ => f (z₀ + t • (z - z₀))
      + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀)))) (Set.Icc (0:ℝ) 1) := by
    have h2 : ContinuousOn (fun t : ℝ => t • deriv f (z₀ + t • (z - z₀))) (Set.Icc (0:ℝ) 1) :=
      (continuous_id.continuousOn).smul hderiv
    exact h1.add (h2.const_smul (z - z₀))
  have hint : IntervalIntegrable (fun t : ℝ => f (z₀ + t • (z - z₀))
      + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀)))) volume (0:ℝ) 1 :=
    hcont'.intervalIntegrable_of_Icc zero_le_one
  -- Fundamental theorem of calculus along the segment.
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := 1)
    zero_le_one hcontF hF hint
  rw [hftc]
  simp [show z₀ + (z - z₀) = z by ring]

end Work.C17g
