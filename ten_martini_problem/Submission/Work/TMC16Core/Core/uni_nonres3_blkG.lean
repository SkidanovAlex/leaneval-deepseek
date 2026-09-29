import Mathlib

namespace Work.TMC16Core.Core

/-- **Full block from erased block.**  `hblk` bounds the sum of `log |sin|` over a block with the
argmin `k₀` removed, two-sidedly, by `32 log L`.  The requested conclusion is the *one-sided*
bound for the sum of `-log |sin|` over the full block: the two-sided estimate supplies
`∑_{block.erase k₀} log|sin| ≥ -(L-1) log 2 - 32 log L`, i.e. `∑_{block.erase k₀} -log|sin| ≤
(L-1) log 2 + 32 log L`, and adding the (negated) term at `k₀` gives the claim. -/
theorem uni_nonres3_blkG {L : ℕ} {α ξ : ℝ} {p : ℤ} (hL : 1 ≤ L)
    (hblk : ∀ (p : ℤ) (k₀ : ℤ), k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ))
    {k₀ : ℤ} (hk₀ : k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1))
    (hmin : ∀ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) :
    ∑ k ∈ Finset.Icc p (p + (L : ℤ) - 1), -Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
      ≤ ((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ)
        - Real.log |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))| := by
  have _ := hL
  -- The two-sided block bound at `(p, k₀)`; take its lower half.
  have hb := hblk p k₀ hk₀ hmin
  have hle : -(32 * Real.log (L : ℝ)) ≤
      ∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((L : ℝ) - 1) * Real.log 2 := (abs_le.mp hb).1
  -- Peel the `k₀` term off the full block sum.
  have hsplit : ∑ k ∈ Finset.Icc p (p + (L : ℤ) - 1),
        Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
      = ∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + Real.log |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))| :=
    (Finset.sum_erase_add (Finset.Icc p (p + (L : ℤ) - 1))
      (fun k => Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|) hk₀).symm
  rw [Finset.sum_neg_distrib, hsplit]
  linarith

end Work.TMC16Core.Core
