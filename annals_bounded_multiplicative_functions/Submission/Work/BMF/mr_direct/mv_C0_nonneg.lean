import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators Interval

/-- If the Montgomery–Vaughan-type large-sieve bound
`∫_A^B ‖∑ n, b n * exp(I * μ n * t)‖² ≤ (B - A + C₀/δ) * ∑ n, ‖b n‖²`
holds for every `δ`-separated family of frequencies, then necessarily `0 ≤ C₀`.

Indeed, taking `N = 1`, the single frequency `μ 0 = 0`, the single coefficient
`b 0 = 1`, and the degenerate interval `A = B = 0`, both sides evaluate: the
left side is `0` while the right side is `C₀/δ`, so `0 ≤ C₀/δ` for every `δ > 0`,
hence `0 ≤ C₀`. -/
theorem mv_C0_nonneg (C₀ : ℝ)
    (hC₀ : ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
      (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2) :
    0 ≤ C₀ := by
  -- Apply the hypothesis to the trivial one-point configuration on `[0,0]`.
  have h := hC₀ 1 one_pos 1 (fun _ => (0 : ℝ)) (fun _ => (1 : ℂ))
    (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim) 0 0 le_rfl
  simp at h
  linarith

end Work.BMF.mr_direct
