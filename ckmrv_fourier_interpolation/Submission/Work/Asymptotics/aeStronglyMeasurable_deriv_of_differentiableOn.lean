import Mathlib
import Submission.Work.Asymptotics.ParamIntegral

namespace Work.Asymptotics

open MeasureTheory Filter Topology
open scoped Topology

/-- If for a.e. `t` the function `z ↦ f z t` is holomorphic on the open set `U`, and `f z` is
a.e. strongly measurable in `t` for every `z ∈ U`, then the `z`-derivative is also a.e. strongly
measurable in `t`.  This discharges the measurability hypothesis `hdmeas` of
`Work.Asymptotics.differentiableOn_integral_Ioi`.  The proof writes the derivative as a
pointwise limit of difference quotients for a.e. `t` and uses that a.e. pointwise limits of a.e.
strongly measurable functions are a.e. strongly measurable. -/
theorem aeStronglyMeasurable_deriv_of_differentiableOn {f : ℂ → ℝ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hmeas : ∀ z ∈ U, MeasureTheory.AEStronglyMeasurable (fun t : ℝ => f z t)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))))
    (hdiff : ∀ᵐ t ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, DifferentiableAt ℂ (fun z' : ℂ => f z' t) z) :
    ∀ z ∈ U, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => deriv (fun z' : ℂ => f z' t) z)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))) := by
  intro z hz
  -- A small ball around `z` contained in `U`, and a fixed sequence `hq n` of non-zero
  -- displacements which stays inside that ball and tends to `0`.
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz)
  let c : ℝ := r / 2
  have hc : 0 < c := by positivity
  let hq : ℕ → ℂ := fun n => ((c / (n + 1) : ℝ) : ℂ)
  have hq_ne : ∀ n, hq n ≠ 0 := by
    intro n
    simp only [hq]
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) (by positivity))
  have hq_tendsto : Tendsto hq atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => (c / (n + 1) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
      simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using h
    have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    simpa [hq, Function.comp_def] using h2
  have hq_tendstoNE : Tendsto hq atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hq_tendsto, eventually_atTop.mpr ⟨0, fun n _ => by simpa using hq_ne n⟩⟩
  have hq_mem : ∀ n, z + hq n ∈ U := by
    intro n
    apply hball
    rw [Metric.mem_ball]
    have hnorm : ‖hq n‖ = c / (n + 1) := by
      have h1 := RCLike.norm_ofReal (K := ℂ) (c / (n + 1))
      rw [abs_of_nonneg (by positivity)] at h1
      simpa [hq] using h1
    have hlt : c / (n + 1) < r := by
      have hle : c / (n + 1) ≤ c := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hc.le, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hcr : c = r / 2 := rfl
      linarith
    calc dist (z + hq n) z = ‖hq n‖ := by rw [dist_eq_norm]; simp
      _ = c / (n + 1) := hnorm
      _ < r := hlt
  -- The difference quotients are a.e. strongly measurable.
  have hFmeas : ∀ n, AEStronglyMeasurable
      (fun t : ℝ => (hq n)⁻¹ * (f (z + hq n) t - f z t))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro n
    exact ((hmeas (z + hq n) (hq_mem n)).sub (hmeas z hz)).const_mul _
  -- For a.e. `t` they converge to the `z`-derivative.
  have hlim : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Tendsto (fun n => (hq n)⁻¹ * (f (z + hq n) t - f z t)) atTop
        (𝓝 (deriv (fun z' : ℂ => f z' t) z)) := by
    filter_upwards [hdiff] with t ht
    have hd := (ht z hz).hasDerivAt
    have hcomp := hd.tendsto_slope_zero.comp hq_tendstoNE
    simpa [Function.comp_def, smul_eq_mul] using hcomp
  exact aestronglyMeasurable_of_tendsto_ae (μ := volume.restrict (Set.Ioi (0:ℝ)))
    atTop hFmeas hlim

end Work.Asymptotics
