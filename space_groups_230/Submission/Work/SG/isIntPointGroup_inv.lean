import Mathlib
import Submission.Work.SG.Defs

namespace Work.SG

/-! # A finite integer point group is closed under inverses

`Work.SG.IsIntPointGroup H` (`Defs.lean`) says: `H` is finite, `1 ∈ H`, `H` is closed under
matrix multiplication, and every `A ∈ H` has `IsUnit A.det` (i.e. `det A = ±1`).  The claim is
that such an `H` is closed under two-sided inverses, stated in the "no `⁻¹` symbol" form that is
easiest to use later.

Route: the powers `A ^ n` (`n : ℕ`) all lie in `H` by closure and `A ^ 0 = 1`, so by the
pigeonhole principle (e.g. `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` applied to
`n ↦ A ^ n` on `Finset.range (|H| + 1)`, mapping into `H.toFinset`) there are `i < j` with
`A ^ i = A ^ j`.  Since `det (A ^ i)` is a unit of `ℤ`, cancelling `A ^ i` on the left
(`Matrix.mul_nonsing_inv_cancel_right`/`_left` with `IsUnit` determinant, over the commutative
ring `ℤ`) gives `A ^ (j - i) = 1`, and then `B := A ^ (j - i - 1) ∈ H` is a two-sided inverse of
`A` (using `j - i ≥ 1`). -/

/-- The powers of a member of a finite multiplicative set containing `1` and closed under
multiplication stay in the set. -/
theorem pow_mem_of_isIntPointGroup {H : Set IMat} (hH : IsIntPointGroup H)
    {A : IMat} (hA : A ∈ H) : ∀ k : ℕ, A ^ k ∈ H := by
  intro k
  induction k with
  | zero => simpa using hH.2.1
  | succ k ih => rw [pow_succ]; exact hH.2.2.1 _ ih _ hA

theorem isIntPointGroup_inv {H : Set Work.SG.IMat} (hH : Work.SG.IsIntPointGroup H)
    {A : Work.SG.IMat} (hA : A ∈ H) :
    ∃ B ∈ H, B * A = 1 ∧ A * B = 1 := by
  classical
  -- `A` is a unit of the matrix ring `M₃(ℤ)`, because `det A` is a unit of `ℤ`.
  have hAunit : IsUnit A :=
    (Matrix.isUnit_iff_isUnit_det A).mpr (hH.2.2.2 A hA)
  have hpow : ∀ k : ℕ, A ^ k ∈ H := pow_mem_of_isIntPointGroup hH hA
  -- Pigeonhole: among `|H| + 1` powers, two coincide.
  obtain ⟨x, -, y, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (hH.1.toFinset.card + 1)) (t := hH.1.toFinset)
      (by simp) (fun k _ => by
        simpa using hH.1.mem_toFinset.mpr (hpow k))
  -- From `A ^ i = A ^ j` with `i < j` we get a two-sided inverse `A ^ (j - i - 1)`.
  have key : ∀ i j : ℕ, i < j → A ^ i = A ^ j → ∃ B ∈ H, B * A = 1 ∧ A * B = 1 := by
    intro i j hij heq
    have hdpos : 0 < j - i := Nat.sub_pos_of_lt hij
    -- cancel `A ^ i` on the left (it is a unit) to obtain `A ^ (j - i) = 1`
    have hc : A ^ (j - i) = 1 := by
      refine (hAunit.pow i).mul_left_cancel ?_
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hij.le]
      exact heq.symm
    refine ⟨A ^ (j - i - 1), hpow _, ?_, ?_⟩
    · rw [← pow_succ, Nat.sub_add_cancel hdpos, hc]
    · rw [← pow_succ', Nat.sub_add_cancel hdpos, hc]
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y h heq
  · exact key y x h heq.symm

end Work.SG
