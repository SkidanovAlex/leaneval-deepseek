import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.PhiStar.PsiDivS2Sup

/-- If `|ψ θ + 2 c cos²θ| ≤ M sin(2θ)` on `(0, 1/2)` and `ψ` is continuous at `0`
within `[0, 1/2]` with `ψ 0 = 0`, then `c = 0`.

Indeed, `sin (2θ) → 0` as `θ → 0⁺`, so the squeezing estimate forces
`ψ θ + 2 c cos²θ → 0`, i.e. `ψ θ → -2c`; continuity on `[0, 1/2]` forces `ψ θ → ψ 0 = 0`. -/
theorem eq_zero_of_bound {ψ : ℝ → ℝ} {c M : ℝ}
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (1 / 2),
      |ψ θ + 2 * c * Real.cos θ ^ 2| ≤ M * Real.sin (2 * θ))
    (hcont : ContinuousWithinAt ψ (Set.Icc 0 (1 / 2)) 0) (h0 : ψ 0 = 0) : c = 0 := by
  have hle : 𝓝[Set.Ioo (0:ℝ) (1/2)] 0 ≤ 𝓝[Set.Icc 0 (1/2)] 0 :=
    nhdsWithin_mono 0 Set.Ioo_subset_Icc_self
  -- continuity of `ψ` transfers to the punctured filter `𝓝[Ioo 0 (1/2)] 0`
  have hψ0 : Tendsto ψ (𝓝[Set.Ioo (0:ℝ) (1/2)] 0) (𝓝 0) := by
    simpa [h0] using hcont.mono_left hle
  -- the upper bound `M * sin (2θ) → 0`
  have hsin : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  have hup : Tendsto (fun θ : ℝ => M * Real.sin (2 * θ))
      (𝓝[Set.Ioo (0:ℝ) (1/2)] 0) (𝓝 0) := by
    have h := (hsin.const_mul M).tendsto (0:ℝ)
    simpa using h.mono_left (nhdsWithin_le_nhds)
  have hdn : Tendsto (fun θ : ℝ => -(M * Real.sin (2 * θ)))
      (𝓝[Set.Ioo (0:ℝ) (1/2)] 0) (𝓝 0) := by
    simpa using hup.neg
  -- squeezing: `ψ θ + 2 c cos²θ → 0`
  have hX : Tendsto (fun θ : ℝ => ψ θ + 2 * c * Real.cos θ ^ 2)
      (𝓝[Set.Ioo (0:ℝ) (1/2)] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hdn hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      have h1 := hb θ hθ
      have h2 := neg_abs_le (ψ θ + 2 * c * Real.cos θ ^ 2)
      linarith
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact le_trans (le_abs_self _) (hb θ hθ)
  -- the second summand tends to `2c`
  have hY : Tendsto (fun θ : ℝ => 2 * c * Real.cos θ ^ 2)
      (𝓝[Set.Ioo (0:ℝ) (1/2)] 0) (𝓝 (2*c)) := by
    have hc : Continuous fun θ : ℝ => 2 * c * Real.cos θ ^ 2 := by fun_prop
    have h : Tendsto (fun θ : ℝ => 2 * c * Real.cos θ ^ 2) (𝓝 (0:ℝ))
        (𝓝 (2 * c * Real.cos 0 ^ 2)) := hc.tendsto 0
    have h2 : (2:ℝ) * c * Real.cos 0 ^ 2 = 2 * c := by norm_num
    rw [h2] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hψ1 : Tendsto ψ (𝓝[Set.Ioo (0:ℝ) (1/2)] 0) (𝓝 (-(2*c))) := by
    have h := hX.sub hY
    simpa only [add_sub_cancel_right, zero_sub] using h
  -- uniqueness of the limit along the non-trivial filter `𝓝[Ioo 0 (1/2)] 0`
  have huniq : -(2*c) = 0 :=
    tendsto_nhds_unique' (left_nhdsWithin_Ioo_neBot (show (0:ℝ) < 1/2 by norm_num)) hψ1 hψ0
  linarith

end Work.FTS.PhiStar.PsiDivS2Sup
