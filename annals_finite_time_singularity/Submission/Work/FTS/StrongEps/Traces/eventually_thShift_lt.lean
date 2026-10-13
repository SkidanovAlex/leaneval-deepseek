import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.Traces

open scoped Real Topology
open Filter

/-- For `|p| ≤ ε` and `θ ∈ [0, π/2]` the shift `thShift θ p` is dominated by the shift at the
extreme value `p = -ε`, which is an explicit function of `θ` alone (tending to `0` as
`θ → 0⁺`). -/
private theorem thShift_le_arctan_exp (ε : ℝ) {θ p : ℝ} (hθ0 : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi / 2) (hp : |p| ≤ ε) :
    Work.FTS.StrongEps.thShift θ p ≤ Real.arctan (Real.tan θ * Real.exp ε) := by
  have htan : 0 ≤ Real.tan θ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0 hθπ
  have hp' : -p ≤ ε := by linarith [(abs_le.mp hp).1]
  have hexp : Real.exp (-p) ≤ Real.exp ε := Real.exp_le_exp.mpr hp'
  exact Real.arctan_le_arctan_iff.mpr (mul_le_mul_of_nonneg_left hexp htan)

theorem eventually_thShift_lt (ε δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → Work.FTS.StrongEps.thShift θ p < δ := by
  -- `arctan (tan θ * e ^ ε) → 0` as `θ → 0⁺`
  have htan0 : Tendsto Real.tan (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : ContinuousAt Real.tan 0 := Real.continuousAt_tan.mpr (by rw [Real.cos_zero]; norm_num)
    have h' : Tendsto Real.tan (𝓝 (0 : ℝ)) (𝓝 (Real.tan 0)) := h.tendsto
    rw [Real.tan_zero] at h'
    exact h'.mono_left inf_le_left
  have hmul : Tendsto (fun θ : ℝ => Real.tan θ * Real.exp ε) (𝓝[>] (0 : ℝ))
      (𝓝 (0 * Real.exp ε)) := htan0.mul tendsto_const_nhds
  have hg : Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp ε)) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    have h := (Real.continuous_arctan.tendsto (0 * Real.exp ε)).comp hmul
    simpa only [Function.comp_def, zero_mul, Real.arctan_zero] using h
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Real.arctan (Real.tan θ * Real.exp ε) < δ :=
    hg.eventually (eventually_lt_nhds hδ)
  have hlt : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < Real.pi / 2 :=
    Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
  filter_upwards [hev, self_mem_nhdsWithin, hlt] with θ hevθ hθpos hθlt
  intro p hp
  exact lt_of_le_of_lt (thShift_le_arctan_exp ε (le_of_lt hθpos) (le_of_lt hθlt) hp) hevθ

end Work.FTS.StrongEps.Traces
