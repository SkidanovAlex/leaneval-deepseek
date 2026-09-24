import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.norm_Fhat_ge_cos_mul_integral

/-!
# The support of `f` has width `≳ 1/T` given the Fourier decay of GM §9

GM §9 uses the following consequence of the Fourier-decay hypothesis
`‖Fhat f ξ‖ ≤ c j ε · T^ε · (T/|ξ|)^j · Λ` for the test function `f` (see the sentence
"Crudely, the rapid decay of `f̂` implies ..." and the "effective width `≳ 1/T`" remark):
if `f ≥ 0` is supported in an interval `[a, a+L]`, then the decay bounds the mass of `f` by
`(L T)^j` times the decay scale `Λ`:

  `cos (π/4) · ∫ f ≤ c j ε · T^ε · (8 L T)^j · Λ`.

With `j = 1` this reads `∫ f ≲ c 1 ε T^ε · L T · Λ`, i.e. a mass of order `Λ/T` forces
`L ≳ 1/T`.

## Proof

Take `ξ := 1/(8L)`, so that `|ξ| = 1/(8L)` and `T/|ξ| = 8 L T`; in particular the decay bound
at this single frequency is `‖Fhat f ξ‖ ≤ c j ε T^ε (8 L T)^j Λ`.  On the support of `f` the
phase `2 π ξ u` varies by at most `2 π L |ξ| = π/4`, so `norm_Fhat_ge_cos_mul_integral` gives

  `cos (π/4) · ∫ f = cos (2 π L |ξ|) · ∫ f ≤ ‖Fhat f ξ‖`.

Combining the two inequalities gives the claim.  (Note `T` need only satisfy `T > 0` here; the
hypothesis `1 ≤ T` is part of the ambient setting of GM §9 and is not used.)
-/

set_option linter.unusedVariables false

namespace Work.GM.Affine

open MeasureTheory

theorem support_width_ge_of_decay {c : ℕ → ℝ → ℝ} {T Λ a L : ℝ} (hT : 1 ≤ T) (hL : 0 < L)
    (hΛ : 0 < Λ) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (hfnn : ∀ u, 0 ≤ f u) (hsupp : ∀ u, f u ≠ 0 → u ∈ Set.Icc a (a + L))
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Real.cos (Real.pi / 4) * (∫ u, f u) ≤ c j ε * T ^ ε * (8 * L * T) ^ j * Λ := by
  -- the frequency at which the phase varies by exactly `π/4` across the support
  set ξ : ℝ := 1 / (8 * L) with hξdef
  have hξpos : 0 < ξ := by rw [hξdef]; exact one_div_pos.mpr (by linarith)
  have hξne : ξ ≠ 0 := ne_of_gt hξpos
  have hξabs : |ξ| = ξ := abs_of_pos hξpos
  -- `2 π L |ξ| = π/4`
  have hangle : 2 * Real.pi * L * |ξ| = Real.pi / 4 := by
    rw [hξabs, hξdef]
    field_simp
    ring
  -- lower bound for `‖Fhat f ξ‖` coming from the support of `f`
  have hlow := norm_Fhat_ge_cos_mul_integral hf hcs hfnn (le_of_lt hL) hsupp
    (ξ := ξ) (by rw [hξabs, hξdef])
  -- upper bound for `‖Fhat f ξ‖` coming from the decay hypothesis
  have hdec' := hdec j ε hε ξ hξne
  have hTxi : T / |ξ| = 8 * L * T := by
    rw [hξabs, hξdef]
    field_simp
  calc Real.cos (Real.pi / 4) * (∫ u, f u)
      = Real.cos (2 * Real.pi * L * |ξ|) * (∫ u, f u) := by rw [hangle]
    _ ≤ ‖Fhat f ξ‖ := hlow
    _ ≤ c j ε * T ^ ε * (8 * L * T) ^ j * Λ := by rw [hTxi] at hdec'; exact hdec'

end Work.GM.Affine
