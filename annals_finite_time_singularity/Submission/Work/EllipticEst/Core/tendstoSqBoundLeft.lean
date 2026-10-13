import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

/-- If `(f θ - c)² ≤ M θ^{1+η}` on `(0, π/2)` with `M ≥ 0` and `η > 0`, then `f → c`
as `θ → 0⁺`: the right-hand side tends to `0` (indeed `θ^{1+η} ≤ θ` for `θ ≤ 1`), so the
square of `f θ - c` tends to `0`, hence so does `|f θ - c|`, hence `f θ - c` itself. -/
theorem tendstoSqBoundLeft {f : ℝ → ℝ} {c M : ℝ} (hM : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - c) ^ 2 ≤ M * θ ^ (1 + Work.Spaces.eta)) :
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) := by
  have heta : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  have hIoi : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < θ := self_mem_nhdsWithin
  have hIio : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), θ < Real.pi / 2 :=
    Filter.le_def.mp nhdsWithin_le_nhds _ (Iio_mem_nhds (by linarith [Real.pi_pos]))
  have hI1 : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), θ < 1 :=
    Filter.le_def.mp nhdsWithin_le_nhds _ (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  -- Pointwise domination of the square by the linear function `M * θ`.
  have hU : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), (f θ - c) ^ 2 ≤ M * θ := by
    filter_upwards [hIoi, hIio, hI1] with θ h1 h2 h3
    have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
    have hh := h θ hmem
    have hrpow : θ ^ (1 + Work.Spaces.eta) ≤ θ := by
      rw [Real.rpow_add h1 1 Work.Spaces.eta, Real.rpow_one]
      exact mul_le_of_le_one_right (le_of_lt h1)
        (Real.rpow_le_one (le_of_lt h1) (le_of_lt h3) (le_of_lt heta))
    calc (f θ - c) ^ 2 ≤ M * θ ^ (1 + Work.Spaces.eta) := hh
      _ ≤ M * θ := mul_le_mul_of_nonneg_left hrpow hM
  -- `M * θ → 0` along `θ → 0⁺`.
  have hMθ : Filter.Tendsto (fun θ : ℝ => M * θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun θ : ℝ => M * θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (M * 0)) :=
      Filter.Tendsto.const_mul M ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
    simpa using h0
  -- Squeeze: the square of `f θ - c` tends to `0`.
  have hsq : Filter.Tendsto (fun θ : ℝ => (f θ - c) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hU hMθ
  -- Hence the square root, i.e. `|f θ - c|`, tends to `0`.
  have hsqrt : Filter.Tendsto (fun θ : ℝ => Real.sqrt ((f θ - c) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun θ : ℝ => Real.sqrt ((f θ - c) ^ 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
    simpa using h0
  have habs : Filter.Tendsto (fun θ : ℝ => |f θ - c|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  have hsub : Filter.Tendsto (fun θ : ℝ => f θ - c)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs)
  simpa [sub_add_cancel] using hsub.add_const c

end Work.EllipticEst.Core
