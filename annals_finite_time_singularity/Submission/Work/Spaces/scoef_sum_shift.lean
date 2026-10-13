/-
Copyright: work module for the Elgindi finite-time singularity project.

# The reindexing identity for the Stirling coefficients of `D_z = z ∂_z`

`scoef n k = S(n,k)` is the Stirling number of the second kind, defined in
`Submission.Work.Spaces.scoef` by the Pascal-type recursion
`S(n+1,k+1) = (k+1) S(n,k+1) + S(n,k)`, `S(n+1,0) = 0`.  This file proves the
reindexing identity `scoef_sum_shift` used by one step of the induction in
`Submission.Work.Spaces.DzIter_le_of_pzIter`.

Concretely, for an arbitrary coefficient sequence `A` and scalar `z` the two
sides

`∑_{k≤n} S(n,k) (k z^k A_k + z^{k+1} A_{k+1})`  and  `∑_{j≤n+1} S(n+1,j) z^j A_j`

both equal `∑_{k≤n} (k S(n,k) z^k A_k) + ∑_{k≤n} S(n,k) z^{k+1} A_{k+1}` : the
first sum is rewritten with the index shift `k → k+1` (the top term drops out
because `S(n,n+1) = 0`) and the second arises from the `D_z`-recursion
`S(n+1,j+1) = (j+1) S(n,j+1) + S(n,j)` together with `S(n+1,0) = 0`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.Spaces.scoef

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- The defining recursion of the Stirling numbers of the second kind, in the
form needed for the reindexing step. -/
private lemma scoef_succ_succ_aux (n k : ℕ) :
    scoef (n + 1) (k + 1) = (k + 1) * scoef n (k + 1) + scoef n k := by
  simp [scoef]

/-- Index shift in a sum: if `g (n+1) = 0` then
`∑_{k≤n} k g(k) = ∑_{j≤n} (j+1) g(j+1)`.  The hypothesis makes the top term of
the right-hand side vanish, so that the shift does not overshoot the range. -/
private lemma sum_range_mul_shift (n : ℕ) (g : ℕ → ℝ) (h : g (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 1), (k : ℝ) * g k)
      = ∑ j ∈ Finset.range (n + 1), ((j : ℝ) + 1) * g (j + 1) := by
  rw [Finset.sum_range_succ' (f := fun k => (k : ℝ) * g k) n,
      Finset.sum_range_succ (f := fun j => ((j : ℝ) + 1) * g (j + 1)) n]
  simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one, h, add_zero, mul_zero]

/-- The reindexing identity relating the `n`-th and `(n+1)`-st rows of Stirling
numbers of the second kind, as used in the induction step of the operator
expansion of `D_z = z ∂_z`. -/
theorem scoef_sum_shift (n : ℕ) (A : ℕ → ℝ) (z : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
        (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ k * A k + z ^ (k + 1) * A (k + 1)))
      = ∑ j ∈ Finset.range (n + 2), (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * A j) := by
  let g : ℕ → ℝ := fun k => (scoef n k : ℝ) * (z ^ k * A k)
  let w : ℕ → ℝ := fun k => (scoef n k : ℝ) * (z ^ (k + 1) * A (k + 1))
  let h : ℕ → ℝ := fun j => (scoef (n + 1) j : ℝ) * (z ^ j * A j)
  have hg0 : g (n + 1) = 0 := by
    simp only [g, scoef_succ_self_eq_zero n, Nat.cast_zero, zero_mul]
  -- split each summand of the left-hand side
  have hL : (∑ k ∈ Finset.range (n + 1),
        (scoef n k : ℝ) * ((k : ℝ) * z ^ k * A k + z ^ (k + 1) * A (k + 1)))
      = (∑ k ∈ Finset.range (n + 1), ((k : ℝ) * g k + w k)) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [g, w]
    ring
  -- shift the index in the `k`-weighted piece
  have hsum : (∑ k ∈ Finset.range (n + 1), ((k : ℝ) * g k + w k))
      = (∑ j ∈ Finset.range (n + 1), (((j : ℝ) + 1) * g (j + 1) + w j)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [sum_range_mul_shift n g hg0]
  -- the right-hand side, with the `j = 0` term dropped (it vanishes)
  have h0 : h 0 = 0 := by
    show (scoef (n + 1) 0 : ℝ) * (z ^ 0 * A 0) = 0
    simp [scoef]
  have hR1 : (∑ j ∈ Finset.range (n + 2), h j)
      = (∑ j ∈ Finset.range (n + 1), h (j + 1)) := by
    rw [Finset.sum_range_succ']
    rw [h0, add_zero]
  -- and the `D_z`-recursion applied to the remaining terms
  have hR2 : (∑ j ∈ Finset.range (n + 1), (((j : ℝ) + 1) * g (j + 1) + w j))
      = (∑ j ∈ Finset.range (n + 1), h (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j _
    show (((j : ℝ) + 1) * ((scoef n (j + 1) : ℝ) * (z ^ (j + 1) * A (j + 1)))
        + (scoef n j : ℝ) * (z ^ (j + 1) * A (j + 1)))
      = ((scoef (n + 1) (j + 1) : ℝ) * (z ^ (j + 1) * A (j + 1)))
    rw [scoef_succ_succ_aux]
    push_cast
    ring
  calc (∑ k ∈ Finset.range (n + 1),
        (scoef n k : ℝ) * ((k : ℝ) * z ^ k * A k + z ^ (k + 1) * A (k + 1)))
      = (∑ k ∈ Finset.range (n + 1), ((k : ℝ) * g k + w k)) := hL
    _ = (∑ j ∈ Finset.range (n + 1), (((j : ℝ) + 1) * g (j + 1) + w j)) := hsum
    _ = (∑ j ∈ Finset.range (n + 1), h (j + 1)) := hR2
    _ = (∑ j ∈ Finset.range (n + 2), h j) := hR1.symm
    _ = ∑ j ∈ Finset.range (n + 2), (scoef (n + 1) j : ℝ) * (z ^ j * A j) := rfl

end Work.Spaces
