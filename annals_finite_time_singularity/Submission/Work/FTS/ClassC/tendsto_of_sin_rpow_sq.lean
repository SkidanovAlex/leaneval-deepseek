import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

theorem tendsto_of_sin_rpow_sq {γ : ℝ} {l : Filter ℝ} {φ : ℝ → ℝ} (hγ : 1 < γ)
    (hl : ∀ᶠ θ in l, θ ∈ Set.Ioo 0 (Real.pi / 2))
    (h : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - γ) * (φ θ) ^ 2) l (nhds 0)) :
    Filter.Tendsto φ l (nhds 0) := by
  -- On `(0, π/2)` we have `0 < sin (2θ) ≤ 1`, hence `1 ≤ sin (2θ) ^ (1 - γ)` (the exponent
  -- `1 - γ` is negative), so that `(φ θ)^2 ≤ |sin (2θ)^(1-γ) * (φ θ)^2|`: the squares are
  -- squeezed to `0`.
  have hle : ∀ᶠ θ in l, (φ θ) ^ 2 ≤ |(Real.sin (2 * θ)) ^ (1 - γ) * (φ θ) ^ 2| := by
    filter_upwards [hl] with θ hθ
    obtain ⟨h0, h1⟩ := hθ
    have hs_pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hmul : Real.sin (2 * θ) ^ (γ - 1) * Real.sin (2 * θ) ^ (1 - γ) = 1 := by
      rw [← Real.rpow_add hs_pos]
      norm_num
    have hle1 : Real.sin (2 * θ) ^ (γ - 1) ≤ 1 :=
      Real.rpow_le_one hs_pos.le hs_le (by linarith)
    have hpos2 : 0 ≤ (φ θ) ^ 2 := sq_nonneg _
    have hpos1 : 0 ≤ Real.sin (2 * θ) ^ (1 - γ) :=
      (Real.rpow_pos_of_pos hs_pos (1 - γ)).le
    rw [abs_of_nonneg (mul_nonneg hpos1 hpos2)]
    calc (φ θ) ^ 2
        = Real.sin (2 * θ) ^ (γ - 1) * Real.sin (2 * θ) ^ (1 - γ) * (φ θ) ^ 2 := by
          rw [hmul, one_mul]
      _ = Real.sin (2 * θ) ^ (γ - 1) * (Real.sin (2 * θ) ^ (1 - γ) * (φ θ) ^ 2) := by ring
      _ ≤ 1 * (Real.sin (2 * θ) ^ (1 - γ) * (φ θ) ^ 2) :=
          mul_le_mul_of_nonneg_right hle1 (mul_nonneg hpos1 hpos2)
      _ = Real.sin (2 * θ) ^ (1 - γ) * (φ θ) ^ 2 := by ring
  have hsq : Filter.Tendsto (fun θ => (φ θ) ^ 2) l (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun θ => sq_nonneg _) hle (by simpa using h.abs)
  -- `φ → 0` because `|φ θ| = √((φ θ)^2)` and `√` is continuous with `√0 = 0`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Filter.Tendsto (fun θ => Real.sqrt ((φ θ) ^ 2)) l (nhds 0) := by
    have hthis := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero] using hthis
  simpa [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, sub_zero] using hs

end Work.FTS.ClassC
