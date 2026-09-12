import Mathlib
import Submission.Commons.Analysis.InnerProduct.side_sum_ge_of_perp

namespace Commons.Analysis.InnerProduct

/-- **Geometric Lemma A1 (point form)**: three points `p₁ p₂ w` of a real
inner product space, an apex decomposition `w − (p₁+p₂)/2 = c • (p₂−p₁) + n`
with `n ⊥ (p₂ − p₁)` and `‖n‖ = h`; then the sum of the two side lengths
from `w` to `p₁` and `p₂` is at least `√(‖p₂−p₁‖² + 4h²)`.

Proof: put `u := p₂ − p₁` and `m := (1/2) • (p₁ + p₂)`.  Then
`w − p₁ = (c • u + n) + (1/2) • u` and `w − p₂ = (c • u + n) − (1/2) • u`
(vector algebra in a module over ℝ), so the reflection lemma
`Commons.Analysis.InnerProduct.side_sum_ge_of_perp u n c hperp` gives
`√(‖u‖² + 4‖n‖²) ≤ ‖(c•u+n) + (1/2)•u‖ + ‖(c•u+n) − (1/2)•u‖`, and
`‖n‖ = h`. -/
theorem A1_of_decomp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p₁ p₂ w : E} {c h : ℝ} {n : E}
    (hdecomp : w - (1 / 2 : ℝ) • (p₁ + p₂) = c • (p₂ - p₁) + n)
    (hperp : inner ℝ n (p₂ - p₁) = 0) (hn : ‖n‖ = h) :
    Real.sqrt (‖p₂ - p₁‖ ^ 2 + 4 * h ^ 2) ≤ ‖w - p₁‖ + ‖w - p₂‖ := by
  set u : E := p₂ - p₁ with hu
  have h1 : w - p₁ = (c • u + n) + (1 / 2 : ℝ) • u := by
    rw [hu, ← hdecomp]
    module
  have h2 : w - p₂ = (c • u + n) - (1 / 2 : ℝ) • u := by
    rw [hu, ← hdecomp]
    module
  have hmain := side_sum_ge_of_perp u n c (by rw [hu]; exact hperp)
  rw [← h1, ← h2, hu, hn] at hmain
  exact hmain

end Commons.Analysis.InnerProduct
