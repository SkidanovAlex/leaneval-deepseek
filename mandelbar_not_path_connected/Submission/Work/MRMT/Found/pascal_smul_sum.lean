import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- Pascal-type smul sum: the binomial identity `∑ⱼ C(N,j)·(f j + f (j+1)) = ∑ᵢ C(N+1,i)·f i`
for the coefficients of `(1+x)^{N+1} = (1+x)^N (1+x)`. -/
theorem pascal_smul_sum {E : Type*} [AddCommMonoid E] [Module ℂ E] (f : ℕ → E) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), (N.choose j : ℂ) • (f j + f (j+1))
      = ∑ i ∈ Finset.range (N+2), ((N+1).choose i : ℂ) • f i := by
  -- Split the left-hand side into the sum over `f j` and the sum over `f (j+1)`.
  have hsplit : (∑ j ∈ Finset.range (N+1), (N.choose j : ℂ) • (f j + f (j+1)))
      = (∑ j ∈ Finset.range (N+1), (N.choose j : ℂ) • f j)
        + (∑ j ∈ Finset.range (N+1), (N.choose j : ℂ) • f (j+1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_add]
  -- Peeling off the `j = 0` term of the first piece.
  have hA : (∑ j ∈ Finset.range (N+1), (N.choose j : ℂ) • f j)
      = (∑ j ∈ Finset.range N, (N.choose (j+1) : ℂ) • f (j+1)) + f 0 := by
    rw [Finset.sum_range_succ']
    simp [Nat.choose_zero_right]
  -- Peeling off the `j = N` term of the second piece.
  have hB : (∑ j ∈ Finset.range (N+1), (N.choose j : ℂ) • f (j+1))
      = (∑ j ∈ Finset.range N, (N.choose j : ℂ) • f (j+1)) + f (N+1) := by
    rw [Finset.sum_range_succ]
    simp [Nat.choose_self]
  -- Pascal's rule combines the two shifted sums.
  have hM : (∑ j ∈ Finset.range N, (N.choose (j+1) : ℂ) • f (j+1))
          + (∑ j ∈ Finset.range N, (N.choose j : ℂ) • f (j+1))
        = ∑ j ∈ Finset.range N, ((N+1).choose (j+1) : ℂ) • f (j+1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hc : (N.choose (j+1) : ℂ) + (N.choose j : ℂ) = ((N+1).choose (j+1) : ℂ) := by
      rw [Nat.choose_succ_succ']; push_cast; ring
    rw [← add_smul, hc]
  -- Normal form of the left-hand side.
  have hL : (∑ j ∈ Finset.range (N+1), (N.choose j : ℂ) • (f j + f (j+1)))
      = (∑ j ∈ Finset.range N, ((N+1).choose (j+1) : ℂ) • f (j+1)) + (f 0 + f (N+1)) := by
    rw [hsplit, hA, hB, ← hM]
    abel
  -- Normal form of the right-hand side.
  have hR : (∑ i ∈ Finset.range (N+2), ((N+1).choose i : ℂ) • f i)
      = (∑ j ∈ Finset.range N, ((N+1).choose (j+1) : ℂ) • f (j+1)) + (f 0 + f (N+1)) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, one_smul]
    abel
  rw [hL, hR]

end Work.MRMT.Found
