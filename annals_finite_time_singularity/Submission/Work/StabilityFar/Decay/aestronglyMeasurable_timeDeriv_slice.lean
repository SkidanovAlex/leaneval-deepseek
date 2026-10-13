import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.StabilityFar.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open MeasureTheory Filter Topology Set

/-- **The time derivative of a slice is almost everywhere strongly measurable.**

If `ω y ·` is differentiable at every time `s` in a two-sided window around `t` (with derivative
`timeDeriv ω y s`, which is how `∂ₜω` is defined), and every time slice `ω · s` in that window is
almost everywhere strongly measurable, then the slice of the time derivative `∂ₜω(·,t)` is almost
everywhere strongly measurable as well.

The proof is the elementary slope argument: `∂ₜω(y,t) = deriv (ω y) t` is the limit of the slopes
`s ↦ s⁻¹ • (ω y (t+s) - ω y t)` along any sequence in the window converging to `0`, and each of
those slopes is a measurable (in fact strongly measurable) function of `y`.  The null sequence
`τ n = ε/2 · 1/(n+1)` is chosen so that `t + τ n` always lies in the window `(t-ε, t+ε)`. -/
theorem aestronglyMeasurable_timeDeriv_slice {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {t ε : ℝ} (hε : 0 < ε)
    (hdc : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      HasDerivAt (fun s' => ω y s') (FiniteTimeSingularity.timeDeriv ω y s) s)
    (hmeas : ∀ s ∈ Set.Ioo (t - ε) (t + ε),
      MeasureTheory.AEStronglyMeasurable (ω · s) MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable (fun y => FiniteTimeSingularity.timeDeriv ω y t)
      MeasureTheory.volume := by
  -- The null sequence of time steps: `τ n = ε/2 · 1/(n+1)`, so `0 < τ n < ε`.
  let τ : ℕ → ℝ := fun n => (ε / 2) * (1 / ((n : ℝ) + 1))
  have hτpos : ∀ n, 0 < τ n := by
    intro n
    have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      apply div_pos one_pos
      positivity
    have h2 : (0 : ℝ) < ε / 2 := by linarith
    simpa only [τ] using mul_pos h2 h1
  have hτlt : ∀ n, τ n < ε := by
    intro n
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      calc 1 / ((n : ℝ) + 1) ≤ 1 / (1 : ℝ) := one_div_le_one_div_of_le (by norm_num) h1
        _ = 1 := by norm_num
    have h3 : τ n ≤ (ε / 2) * 1 := by
      simp only [τ]
      exact mul_le_mul_of_nonneg_left hle (by linarith)
    linarith
  have hmem : ∀ n, t + τ n ∈ Set.Ioo (t - ε) (t + ε) := by
    intro n
    have hp := hτpos n
    have hl := hτlt n
    exact ⟨by linarith, by linarith⟩
  have ht : t ∈ Set.Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  -- Each slope is strongly measurable in `y`.
  have hf : ∀ n, AEStronglyMeasurable (fun y => (τ n)⁻¹ • (ω y (t + τ n) - ω y t)) volume := by
    intro n
    exact ((hmeas (t + τ n) (hmem n)).sub (hmeas t ht)).const_smul ((τ n)⁻¹)
  -- The slopes converge, for every `y`, to the time derivative at `t`.
  have hlim : ∀ᵐ y ∂volume, Tendsto (fun n => (τ n)⁻¹ • (ω y (t + τ n) - ω y t)) atTop
      (𝓝 (FiniteTimeSingularity.timeDeriv ω y t)) := by
    refine Eventually.of_forall (fun y => ?_)
    have hd := hdc t ht y
    have hτtend : Tendsto τ atTop (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall (fun n => ?_)⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 2)
        simpa only [τ, mul_zero] using h
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (hτpos n)
    exact hd.tendsto_slope_zero.comp hτtend
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hf hlim

end Work.StabilityFar.Decay
