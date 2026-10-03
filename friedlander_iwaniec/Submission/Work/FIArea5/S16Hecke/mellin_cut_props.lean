import Mathlib

namespace Work.FIArea5.S16Hecke

open MeasureTheory Set Filter Asymptotics
open scoped Topology

/-- A function which vanishes on `(-∞, c]` for some `c > 0` and decays like `exp (-π u)` at
infinity has a Mellin transform that converges everywhere, and which is entire.

The vanishing on `(-∞, c]` makes `f` identically zero in a right-neighbourhood of `0`, so `f` is
`O(x ^ (-b))` at `0` for every `b`; the exponential decay makes `f` `O(exp (-π u))` at `∞`.  The
Mathlib results `mellinConvergent_of_isBigO_rpow_exp` and `mellin_differentiableAt_of_isBigO_rpow_exp`
then give convergence and differentiability at every complex point. -/
theorem mellin_cut_props (c : ℝ) (hc : 0 < c) (f : ℝ → ℂ)
    (hf : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hli : MeasureTheory.LocallyIntegrableOn f (Set.Ioi 0))
    (h0 : ∀ u : ℝ, u ≤ c → f u = 0)
    (hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ‖f u‖ ≤ C * Real.exp (-Real.pi * u)) :
    (∀ t : ℂ, MellinConvergent f t) ∧ AnalyticOn ℂ (fun t : ℂ => mellin f t) Set.univ := by
  -- ## Exponential decay at `∞`
  obtain ⟨C, u₀, _hu₀, hC⟩ := hdec
  have hf_top : f =O[atTop] (fun t : ℝ => Real.exp (-Real.pi * t)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop u₀] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hC u hu
  -- ## Vanishing near `0`
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), f u = 0 := by
    have hlt : ∀ᶠ u in 𝓝[>] (0 : ℝ), u < c :=
      nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hc)
    filter_upwards [hlt] with u hu
    exact h0 u hu.le
  have hf_bot : ∀ b : ℝ, f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    intro b
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hev] with u hu
    rw [hu, norm_zero, one_mul]
    exact norm_nonneg _
  refine ⟨fun t => ?_, ?_⟩
  · exact mellinConvergent_of_isBigO_rpow_exp (a := Real.pi) Real.pi_pos hli hf_top
      (hf_bot (t.re - 1)) (by linarith)
  · rw [Complex.analyticOn_univ_iff_differentiable]
    intro s
    exact mellin_differentiableAt_of_isBigO_rpow_exp (a := Real.pi) Real.pi_pos hli hf_top
      (hf_bot (s.re - 1)) (by linarith)

end Work.FIArea5.S16Hecke
