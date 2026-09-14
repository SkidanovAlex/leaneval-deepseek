import Mathlib
import Submission.Commons.Analysis.Convex.prekopa_leindler_inequality

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Prékopa–Leindler, marginal (log-concavity) form.**
If `H : ℝ × ℝⁿ → [0,∞)` is jointly log-concave — meaning
`H (t • p + (1-t) • q) ≥ H p ^ t * H q ^ (1-t)` for all `p q` and `t ∈ [0,1]` — and all slices
`y ↦ H (y, ·)` are integrable, then the marginal `y ↦ ∫ z, H (y, z) dz` is log-concave:
`(∫ z, H (t*y₁ + (1-t)*y₂, z)) ≥ (∫ z, H (y₁, z)) ^ t * (∫ z, H (y₂, z)) ^ (1-t)`.

This is the special case `f = g = h = H` of the Prékopa–Leindler inequality (already in the
commons as `Commons.Analysis.Convex.prekopa_leindler_inequality`).  Proof: for fixed `y₁ y₂ t`,
apply Prékopa–Leindler with the three functions `F z = H (y₁, z)`, `G z = H (y₂, z)`,
`h z = H (t*y₁ + (1-t)*y₂, z)`; the hypothesis `h (t • z₁ + (1-t) • z₂) ≥ F z₁ ^ t * G z₂ ^ (1-t)`
is exactly `hHlog` at `p = (y₁, z₁)`, `q = (y₂, z₂)`. -/
theorem logconcave_marginal_prod {n : ℕ} (H : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (hHnn : ∀ p, 0 ≤ H p)
    (hHlog : ∀ (t : ℝ) (p q : ℝ × EuclideanSpace ℝ (Fin n)), 0 ≤ t → t ≤ 1 →
      H (t • p + (1 - t) • q) ≥ H p ^ t * H q ^ (1 - t))
    (hint : ∀ y : ℝ, Integrable (fun z : EuclideanSpace ℝ (Fin n) => H (y, z))) :
    ∀ (y₁ y₂ : ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      (∫ z, H (t * y₁ + (1 - t) * y₂, z))
        ≥ (∫ z, H (y₁, z)) ^ t * (∫ z, H (y₂, z)) ^ (1 - t) := by
  intro y₁ y₂ t ht0 ht1
  have hmain := prekopa_leindler_inequality (n := n)
    (fun z => H (y₁, z)) (fun z => H (y₂, z))
    (fun z => H (t * y₁ + (1 - t) * y₂, z))
    (1 - t) (by linarith) (by linarith)
    (fun z => hHnn _) (fun z => hHnn _) (fun z => hHnn _)
    (hint y₁) (hint y₂) (hint (t * y₁ + (1 - t) * y₂))
    (fun x y => ?_)
  · simpa using hmain
  · have h1 := hHlog t (y₁, x) (y₂, y) ht0 ht1
    have hp : t • (y₁, x) + (1 - t) • (y₂, y)
        = (t * y₁ + (1 - t) * y₂, t • x + (1 - t) • y) := by
      ext <;> simp
    rw [hp] at h1
    have hsub : (1 : ℝ) - (1 - t) = t := by ring
    rw [hsub]
    exact h1

end Commons.Analysis.Convex
