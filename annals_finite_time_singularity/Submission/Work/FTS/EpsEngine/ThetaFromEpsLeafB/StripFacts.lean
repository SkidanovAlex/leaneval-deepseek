import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EpsEngine.ClassCStepEngine
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafB

set_option autoImplicit false

/-- Almost everywhere, the second coordinate of a point of the plane differs from any fixed
value `c`: the vertical line `{p | p.2 = c}` is `univ ×ˢ {c}`, a null set. -/
theorem ae_snd_ne (c : ℝ) :
    ∀ᵐ p : ℝ × ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)), p.2 ≠ c := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hy : ∀ᵐ y : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), y ≠ c := by
    rw [MeasureTheory.ae_iff]
    simpa using Real.volume_singleton (a := c)
  change ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume,
    p ∈ {p : ℝ × ℝ | p.2 ≠ c}
  rw [MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem (by measurability)]
  filter_upwards with x
  filter_upwards [hy] with y hyy
  simpa using hyy

/-- **Fubini for `EpsSq`**: as soon as the integrand `(f · epsW α)²` is integrable on the quarter
plane `Iz ×ˢ Iθ`, the iterated integral defining `EpsSq` equals the integral over that product
set (so in particular `EpsSq` is an honest integral and not the junk value `0`). -/
theorem EpsSq_eq_setIntegral {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hf : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.FTS.StrongEps.EpsSq α f
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := by
  rw [Work.FTS.StrongEps.EpsSq]
  exact (MeasureTheory.setIntegral_prod (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
    (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) hf).symm

/-- **The lower strip integral vanishes.**  For an integrand `F` which is integrable on the
quarter plane `Iz ×ˢ Iθ`, the integral over the shrinking sets `{p | p.2 ≤ φ} ∩ (Iz ×ˢ Iθ)`
tends to `0` as `φ → 0⁺`: the limit set is `{θ = 0} ∩ (Iz ×ˢ Iθ)`, a null set.

Proof: write the integral as `∫ p, (s.indicator F) p · 1_{p.2 ≤ φ} p` and apply dominated
convergence with the dominating function `s.indicator (‖F ·‖)`; the pointwise limit is `0`
everywhere off the null set `{θ = 0}`. -/
theorem tendsto_setIntegral_Iic {F : ℝ × ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Filter.Tendsto (fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        (if p.2 ≤ φ then F p else 0)) (𝓝[>] 0) (𝓝 0) := by
  have hs : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  set F' : ℝ × ℝ → ℝ := (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator F with hF'
  have hF'int : MeasureTheory.Integrable F' MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff hs).mpr hF
  have hane : ∀ᵐ p : ℝ × ℝ ∂MeasureTheory.volume, p.2 ≠ 0 := ae_snd_ne 0
  have key : Filter.Tendsto (fun φ : ℝ => ∫ p, (if p.2 ≤ φ then F' p else 0)) (𝓝[>] 0)
      (𝓝 (∫ p : ℝ × ℝ, (0 : ℝ))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[>] (0 : ℝ)) (F := fun φ p => if p.2 ≤ φ then F' p else 0)
      (f := fun _ : ℝ × ℝ => (0 : ℝ)) (fun p : ℝ × ℝ => ‖F' p‖) ?_ ?_ hF'int.norm ?_
    · filter_upwards with φ
      have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ φ} :=
        measurableSet_le measurable_snd (measurable_const : Measurable (fun _ : ℝ × ℝ => φ))
      have h2 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => if p.2 ≤ φ then (1 : ℝ) else 0) MeasureTheory.volume :=
        (Measurable.indicator measurable_const hset).aestronglyMeasurable
      refine ((hF'int.aestronglyMeasurable).mul h2).congr ?_
      filter_upwards with p
      by_cases hp : p.2 ≤ φ <;> simp [hp, Pi.mul_apply]
    · filter_upwards with φ
      filter_upwards with p
      by_cases hp : p.2 ≤ φ <;> simp [hp]
    · refine hane.mono fun p hp => ?_
      by_cases hpos : 0 < p.2
      · have hmem : Set.Iio p.2 ∈ 𝓝[>] (0 : ℝ) :=
          mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds hpos)
        have hcong : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
            (fun φ : ℝ => if p.2 ≤ φ then F' p else 0) := by
          filter_upwards [hmem] with φ hφ
          have hle : ¬ (p.2 ≤ φ) := not_le.mpr (Set.mem_Iio.mp hφ)
          simp [hle]
        exact Filter.Tendsto.congr' hcong tendsto_const_nhds
      · have hle0 : p.2 ≤ 0 := le_of_not_gt hpos
        have hneg : p.2 < 0 := lt_of_le_of_ne hle0 hp
        have hnotmem : p ∉ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
          intro hp'
          have h2 : p.2 ∈ Work.Spaces.Iθ := hp'.2
          rw [Work.Spaces.Iθ] at h2
          linarith [h2.1]
        have hzero : F' p = 0 := by
          rw [hF', Set.indicator_of_notMem hnotmem]
        have hcong : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
            (fun φ : ℝ => if p.2 ≤ φ then F' p else 0) := by
          filter_upwards [self_mem_nhdsWithin] with φ hφ
          have h2 : p.2 ≤ φ :=
            le_of_lt (lt_of_lt_of_le hneg (le_of_lt (Set.mem_Ioi.mp hφ)))
          simp [h2, hzero]
        exact Filter.Tendsto.congr' hcong tendsto_const_nhds
  have key' : Filter.Tendsto (fun φ : ℝ => ∫ p, (if p.2 ≤ φ then F' p else 0)) (𝓝[>] 0)
      (𝓝 0) := by simpa using key
  have hrel : (fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        (if p.2 ≤ φ then F p else 0))
      = fun φ : ℝ => ∫ p, (if p.2 ≤ φ then F' p else 0) := by
    funext φ
    rw [← MeasureTheory.integral_indicator hs]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have key2 : ∀ q : ℝ × ℝ, (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (fun p => if p.2 ≤ φ then F p else 0) q
      = (if q.2 ≤ φ then F' q else 0) := by
      intro q
      by_cases hq : q ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
      · rw [Set.indicator_of_mem hq, hF', Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq, hF', Set.indicator_of_notMem hq]
        simp
    exact key2 p
  rw [hrel]
  exact key'

end Work.FTS.EpsEngine.ThetaFromEpsLeafB
