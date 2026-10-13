import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

/-- If `(f θ - c)^2` is controlled by `M * (π/2 - θ)^(1+η)` on the open interval
`(0, π/2)`, then `f θ → c` as `θ → (π/2)⁻` (with `η = 99/100 > 0`). -/
theorem tendstoSqBoundRight {f : ℝ → ℝ} {c M : ℝ} (hM : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - c) ^ 2 ≤ M * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)) :
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) := by
  set l : Filter ℝ := nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) with hl
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  -- near `π/2` from below we land in the open interval `(0, π/2)`
  have hgt : ∀ᶠ θ in l, (0 : ℝ) < θ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hpi)
  have hlt : ∀ᶠ θ in l, θ < Real.pi / 2 := self_mem_nhdsWithin
  have hmem : ∀ᶠ θ in l, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Filter.Eventually.mono (Filter.Eventually.and hgt hlt) fun θ hθ => ⟨hθ.1, hθ.2⟩
  -- `θ ↦ π/2 - θ` tends to `0`
  have ht : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) l (nhds 0) := by
    have h' : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2))
        (nhds (Real.pi / 2 - Real.pi / 2)) :=
      tendsto_const_nhds.sub Filter.tendsto_id
    simpa using h'.mono_left nhdsWithin_le_nhds
  -- hence the upper bound `M * (π/2 - θ)^(1+η)` tends to `0`
  have hg : Filter.Tendsto (fun θ : ℝ => M * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta))
      l (nhds 0) := by
    have hpos : (0 : ℝ) < 1 + Work.Spaces.eta := by
      rw [Work.Spaces.eta]; norm_num
    simpa using (ht.rpow_const_nhds_zero hpos).const_mul M
  -- squeeze `(f θ - c)^2` between `0` and it
  have hsq : Filter.Tendsto (fun θ : ℝ => (f θ - c) ^ 2) l (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (Filter.Eventually.mono hmem fun θ hθ => h θ hθ)
  -- `√((f θ - c)^2) = |f θ - c| → 0`, so `f θ - c → 0`
  have hsub : Filter.Tendsto (fun θ : ℝ => f θ - c) l (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsqrt : Filter.Tendsto (fun θ : ℝ => Real.sqrt ((f θ - c) ^ 2)) l
        (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  simpa using hsub.const_add c

end Work.EllipticEst.Core
