import Mathlib

namespace Work.KMTContract

open MeasureTheory

/-- The counting measure on `ℤ` dominates the Dirac mass at every point. -/
private lemma dirac_le_count_int (x : ℤ) : Measure.dirac x ≤ Measure.count := by
  rw [Measure.count]
  exact Measure.le_sum Measure.dirac x

/-- **A function in `ℓ^p(ℤ)` (`1 < p ≤ ∞`) is bounded.**

This is the `ℓ^p ⊆ ℓ^∞` inclusion for the counting measure on `ℤ`: the norm of a
single value never exceeds the `ℓ^p`-norm, because the Dirac mass at a point is
dominated by the counting measure. -/
theorem bound_of_memLp_count {p : ENNReal} (hp : 1 < p) {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f p MeasureTheory.Measure.count) :
    ∃ M : NNReal, ∀ x : ℤ, ‖f x‖ ≤ M := by
  -- `1 < p` rules out the degenerate exponent `p = 0`
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hp
    exact absurd hp (by norm_num)
  refine ⟨(eLpNorm f p Measure.count).toNNReal, fun x => ?_⟩
  -- `eLpNorm · p (Measure.dirac x) = ‖· x‖ₑ`, and `dirac x ≤ count`, so
  -- monotonicity of `eLpNorm` in the measure bounds every value by the `ℓ^p`-norm.
  have h1 : ‖f x‖ₑ ≤ eLpNorm f p Measure.count := by
    rw [← eLpNorm_dirac f x hp0]
    exact eLpNorm_mono_measure f (dirac_le_count_int x)
  -- the `ℓ^p`-norm is finite, so we may pass to `ℝ≥0`
  have h2 := ENNReal.toNNReal_mono hf.eLpNorm_lt_top.ne h1
  exact_mod_cast h2

end Work.KMTContract
