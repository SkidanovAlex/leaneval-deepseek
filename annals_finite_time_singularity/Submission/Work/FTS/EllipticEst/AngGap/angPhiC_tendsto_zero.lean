import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.AngGap.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

/-- `angPhiC h = V · h = (G / sin 2θ) · h` tends to `0` at the two endpoints of `(0, π/2)`.

The bounds `hbdd : |h θ| ≤ C sin 2θ` and `hCg : |G θ| ≤ C sin³2θ` give, on the open
interval where `sin 2θ > 0`,

`|angPhiC h θ| = |G θ| / sin 2θ · |h θ| ≤ (C sin³2θ)/sin 2θ · (C sin 2θ) = C² sin³2θ`,

and `sin (2θ) → 0` at `θ = 0` and at `θ = π/2`, so the squeeze lemma `squeeze_zero_norm'`
finishes both limits.  This is the endpoint-limit component of the integration-by-parts
identity `∫ h² = -∫ V Q` in the angular gap-Wirtinger development. -/
theorem angPhiC_tendsto_zero (h : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    Filter.Tendsto (Work.FTS.EllipticEst.AngGap.angPhiC h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (Work.FTS.EllipticEst.AngGap.angPhiC h)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  have hsub : Set.Ioo (0 : ℝ) (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- ## the pointwise bound on the open interval
  have hphi_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ‖angPhiC h θ‖ ≤ C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hg := hCg θ (hsub hθ)
    have hh := hbdd θ (hsub hθ)
    have habs : |angPhiC h θ| = |angG h θ| / Real.sin (2 * θ) * |h θ| := by
      rw [show angPhiC h θ = (angG h θ / Real.sin (2 * θ)) * h θ from rfl]
      rw [abs_mul, abs_div, abs_of_pos hs]
    rw [Real.norm_eq_abs, habs]
    calc |angG h θ| / Real.sin (2 * θ) * |h θ|
        ≤ (C * (Real.sin (2 * θ)) ^ 3) / Real.sin (2 * θ) * (C * Real.sin (2 * θ)) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_right hg hs.le
          · exact hh
          · exact abs_nonneg _
          · positivity
      _ = C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
          field_simp
  -- ## the two comparison sequences `C² sin³2θ → 0`
  have hsin0 : Tendsto (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1' : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (0 : ℝ))
          (𝓝 (Real.sin (2 * (0 : ℝ)))) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.tendsto
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by simp] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    simpa using (h1'.pow 3).const_mul (C ^ 2)
  have hsinpi : Tendsto (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (𝓝[<] (π / 2)) (𝓝 0) := by
    have h1' : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[<] (π / 2)) (𝓝 0) := by
      have hc : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (π / 2))
          (𝓝 (Real.sin (2 * (π / 2)))) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.tendsto
      rw [show Real.sin (2 * (π / 2)) = 0 by
            rw [show 2 * (π / 2) = π by ring, Real.sin_pi]] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    simpa using (h1'.pow 3).const_mul (C ^ 2)
  -- ## the two squeezed limits
  constructor
  · refine squeeze_zero_norm' ?_ hsin0
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact hphi_le θ hθ
  · refine squeeze_zero_norm' ?_ hsinpi
    filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
    exact hphi_le θ hθ

end Work.FTS.EllipticEst.AngGap
