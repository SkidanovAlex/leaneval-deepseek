import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.irrat_blk_nr

namespace Work.TMC16Core.Assembly

/-- **Block product estimate at scale `q n` (AJ §9 Lemma 9.6, `irrat-1`, with `Lsh ≡ 0`).**

For continued-fraction data `(q, Δ)` of the frequency `α` and an arbitrary block
`B = Icc p (p + q n - 1)` of `q n` consecutive integers, if `k₀ ∈ B` minimises
`|sin (π (ξ + k α))|` over `B`, then the block product with that minimal factor removed is
`2^{-(q n - 1)}` up to a factor `(q n)^{32}`.

This is the specialisation `Lsh ≡ 0` of the shifted block estimate; it is exactly
`Work.TMC16Core.Core.irrat_blk_nr` applied with the index `n + 1`, since
`(n + 1) - 1` reduces to `n`. -/
theorem s0qn_blk0 {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {p : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 1 ≤ n)
    {ξ : ℝ} {k₀ : ℤ} (hk₀ : k₀ ∈ Finset.Icc p (p + (q n : ℤ) - 1))
    (hmin : ∀ k ∈ Finset.Icc p (p + (q n : ℤ) - 1),
      |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
        |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) :
    |∑ k ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
      + ((q n : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q n : ℝ) := by
  exact Work.TMC16Core.Core.irrat_blk_nr (n := n + 1) hqpos hmono hΔpos hΔeq hΔup hΔlo
    hbest (by omega) hk₀ hmin

end Work.TMC16Core.Assembly
