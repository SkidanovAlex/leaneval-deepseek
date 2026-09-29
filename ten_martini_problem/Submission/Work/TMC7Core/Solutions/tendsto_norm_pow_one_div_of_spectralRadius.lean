import Mathlib

/-!
# Gelfand's formula in the "norm root" form

For an element `a` of a complex Banach algebra, the spectral radius is the limit of the
sequence `‖a ^ n‖ ^ (1 / n)`.  This is exactly Gelfand's formula
(`spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`), transported from its natural
home `ℝ≥0∞` back to `ℝ` using `ENNReal.tendsto_toReal_iff`: the hypothesis that the spectral
radius equals `ENNReal.ofReal ρ` with `ρ ≥ 0` says precisely that `ρ` is the (finite)
`ℝ`-valued representative of the spectral radius.
-/

namespace Work.TMC7Core.Solutions

theorem tendsto_norm_pow_one_div_of_spectralRadius {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (a : A) (ρ : ℝ) (h : spectralRadius ℂ a = ENNReal.ofReal ρ) (hρ : 0 ≤ ρ) :
    Filter.Tendsto (fun n : ℕ => ‖a ^ n‖ ^ (1 / (n : ℝ))) Filter.atTop (nhds ρ) := by
  -- Gelfand's formula in `ℝ≥0∞`, then rewrite the limit as `ENNReal.ofReal ρ` via `h`.
  have h1 := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  rw [h] at h1
  -- `ENNReal.toReal` is continuous at every finite point, and both the sequence and the limit
  -- are finite (they are `ENNReal.ofReal` of something), so we may apply it.
  have h2 :=
    (ENNReal.tendsto_toReal_iff (fun _ => ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top).mpr h1
  rw [ENNReal.toReal_ofReal hρ] at h2
  -- Finally `(ENNReal.ofReal x).toReal = x` because `x = ‖a ^ n‖ ^ (1 / n)` is nonnegative.
  have h3 : (fun n : ℕ => (ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ)))).toReal)
      = (fun n : ℕ => ‖a ^ n‖ ^ (1 / (n : ℝ))) := by
    funext n
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)
  rwa [h3] at h2

end Work.TMC7Core.Solutions
