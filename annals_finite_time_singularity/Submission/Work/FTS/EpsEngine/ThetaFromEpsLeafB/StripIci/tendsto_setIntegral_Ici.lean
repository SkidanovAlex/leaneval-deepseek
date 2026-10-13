/-
Copyright: work module for the Elgindi finite-time singularity project.

# `StripIci/tendsto_setIntegral_Ici` — the upper strip integral vanishes

The mirror image of `Work.FTS.EpsEngine.ThetaFromEpsLeafB.tendsto_setIntegral_Iic`
(in `ThetaFromEpsLeafB/StripFacts.lean`).  For an integrand `F` which is integrable on the
quarter plane `Iz ×ˢ Iθ`, the integral over the shrinking sets `{p | π/2 - φ ≤ p.2}`
tends to `0` as `φ → 0⁺`: here the limit set is `{θ = π/2} ∩ (Iz ×ˢ Iθ)` (`Iθ = [0,π/2]`,
so `θ ≥ π/2` forces `θ = π/2`), a null set.

Proof: write the integral as `∫ p, (s.indicator F) p · 1_{π/2 - φ ≤ p.2} p` and apply
dominated convergence with the dominating function `s.indicator (‖F ·‖)`; the pointwise
limit is `0` everywhere off the null set `{θ = π/2}`.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripIci

set_option autoImplicit false

theorem tendsto_setIntegral_Ici {F : ℝ × ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Filter.Tendsto (fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        (if Real.pi / 2 - φ ≤ p.2 then F p else 0)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hs : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  set F' : ℝ × ℝ → ℝ := (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator F with hF'
  have hF'int : MeasureTheory.Integrable F' MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff hs).mpr hF
  have hane : ∀ᵐ p : ℝ × ℝ ∂MeasureTheory.volume, p.2 ≠ Real.pi / 2 :=
    Work.FTS.EpsEngine.ThetaFromEpsLeafB.ae_snd_ne (Real.pi / 2)
  have key : Filter.Tendsto (fun φ : ℝ => ∫ p, (if Real.pi / 2 - φ ≤ p.2 then F' p else 0))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p : ℝ × ℝ, (0 : ℝ))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[>] (0 : ℝ)) (F := fun φ p => if Real.pi / 2 - φ ≤ p.2 then F' p else 0)
      (f := fun _ : ℝ × ℝ => (0 : ℝ)) (fun p : ℝ × ℝ => ‖F' p‖) ?_ ?_ hF'int.norm ?_
    · filter_upwards with φ
      have hset : MeasurableSet {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} :=
        measurableSet_le (measurable_const : Measurable (fun _ : ℝ × ℝ => Real.pi / 2 - φ))
          measurable_snd
      refine ((hF'int.aestronglyMeasurable).indicator hset).congr ?_
      filter_upwards with p
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    · filter_upwards with φ
      filter_upwards with p
      by_cases hp : Real.pi / 2 - φ ≤ p.2 <;> simp [hp]
    · refine hane.mono fun p hp => ?_
      by_cases hlt : p.2 < Real.pi / 2
      · have hpos : 0 < Real.pi / 2 - p.2 := by linarith
        have hmem : Set.Iio (Real.pi / 2 - p.2) ∈ 𝓝[>] (0 : ℝ) :=
          mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds hpos)
        have hcong : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
            (fun φ : ℝ => if Real.pi / 2 - φ ≤ p.2 then F' p else 0) := by
          filter_upwards [hmem] with φ hφ
          have hφ' : φ < Real.pi / 2 - p.2 := Set.mem_Iio.mp hφ
          have hle : ¬ (Real.pi / 2 - φ ≤ p.2) := by linarith
          simp [hle]
        exact Filter.Tendsto.congr' hcong tendsto_const_nhds
      · have hgt : Real.pi / 2 < p.2 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hp)
        have hnotmem : p ∉ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
          intro hp'
          have h2 : p.2 ∈ Work.Spaces.Iθ := hp'.2
          rw [Work.Spaces.Iθ] at h2
          linarith [h2.2]
        have hzero : F' p = 0 := by rw [hF', Set.indicator_of_notMem hnotmem]
        have hcong : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
            (fun φ : ℝ => if Real.pi / 2 - φ ≤ p.2 then F' p else 0) := by
          filter_upwards with φ
          simp [hzero]
        exact Filter.Tendsto.congr' hcong tendsto_const_nhds
  have key' : Filter.Tendsto (fun φ : ℝ => ∫ p, (if Real.pi / 2 - φ ≤ p.2 then F' p else 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using key
  have hrel : (fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        (if Real.pi / 2 - φ ≤ p.2 then F p else 0))
      = fun φ : ℝ => ∫ p, (if Real.pi / 2 - φ ≤ p.2 then F' p else 0) := by
    funext φ
    rw [← MeasureTheory.integral_indicator hs]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have key2 : ∀ q : ℝ × ℝ, (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (fun p => if Real.pi / 2 - φ ≤ p.2 then F p else 0) q
      = (if Real.pi / 2 - φ ≤ q.2 then F' q else 0) := by
      intro q
      by_cases hq : q ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
      · rw [Set.indicator_of_mem hq, hF', Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq, hF', Set.indicator_of_notMem hq]
        simp
    exact key2 p
  rw [hrel]
  exact key'

end Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripIci
