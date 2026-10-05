import Mathlib
import Submission.Work.RPB1a.Defs

/-!
# RPB1a: a holomorphic injective map on an open set is open

This file supplies the lemma `Work.RPB1a.isOpen_image_of_differentiableOn_of_injOn`, used in the
analytic route to node `B1` (`RECTPEG_B1_LEAD.md`): the Laurent polynomial `Γ` of the Fourier
reduction is holomorphic and injective on the thin symmetric annulus `ρ < |w| < ρ⁻¹` around the
unit circle, so its image is open — this is what lets the collar around a trigonometric loop be
matched against the Jordan domain bounded by it.

The mathematics is the classical **open mapping theorem** for holomorphic functions, in the local
form proved in `Mathlib.Analysis.Complex.OpenMapping`:
`AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux` says that an analytic `f : ℂ → ℂ` at `z₀`
is either locally constant at `z₀`, or sends every neighbourhood of `z₀` to a neighbourhood of
`f z₀`.

Injectivity on the open set `U` rules out the first alternative: if `f` were equal to `f z₀` on a
neighbourhood of `z₀`, then (using `U ∈ 𝓝 z₀` and the fact that a ball in `ℂ` contains a point
other than its centre) we would find `z ≠ z₀` in `U` with `f z = f z₀`.  So for every `z₀ ∈ U` the
image of `U` — an open neighbourhood of `z₀` — is a neighbourhood of `f z₀`, and `f '' U` is open
by `isOpen_iff_mem_nhds`.

No use is made of `deriv f ≠ 0`; multiplicities of zeros of `f - f z₀` are irrelevant because the
local open mapping theorem is proved by the maximum modulus principle rather than by Rouché's
theorem.
-/

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real Topology

theorem isOpen_image_of_differentiableOn_of_injOn {U : Set ℂ} {f : ℂ → ℂ} (hUo : IsOpen U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) : IsOpen (f '' U) := by
  -- It suffices to see that `f '' U` is a neighbourhood of each of its points.
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z₀, hz₀U, hw⟩
  rw [← hw]
  -- `f` is analytic at `z₀`, so the local open mapping theorem applies.
  have han : AnalyticAt ℂ f z₀ := hfd.analyticOnNhd hUo z₀ hz₀U
  rcases han.eventually_constant_or_nhds_le_map_nhds_aux with hconst | hopen
  · -- The locally constant alternative is impossible: it would produce a second preimage of
    -- `f z₀` inside `U`.
    exfalso
    have hS : {z | f z = f z₀} ∩ U ∈ 𝓝 z₀ :=
      Filter.inter_mem hconst (hUo.mem_nhds hz₀U)
    obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp hS
    have hmem : z₀ + ((ε / 2 : ℝ) : ℂ) ∈ ball z₀ ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (half_pos hε).le]
      linarith
    obtain ⟨hfz, hzU⟩ := hεS hmem
    have hzne : z₀ + ((ε / 2 : ℝ) : ℂ) ≠ z₀ := by
      intro h
      have h2 : ((ε / 2 : ℝ) : ℂ) = 0 := by
        have h' : z₀ + ((ε / 2 : ℝ) : ℂ) = z₀ + 0 := by simpa using h
        exact add_left_cancel h'
      have h3 : (ε / 2 : ℝ) = 0 := Complex.ofReal_eq_zero.mp h2
      linarith
    exact hzne (hfi hzU hz₀U hfz)
  · -- The open alternative: `U` is a neighbourhood of `z₀`, hence so is its image.
    exact hopen (Filter.image_mem_map (hUo.mem_nhds hz₀U))

end Work.RPB1a
