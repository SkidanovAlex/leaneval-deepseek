/-
# The "mixed" (neither `a`-side nor `b`-side) indices are exactly the "conditional" ones

For `k : Fin (N+2)` with `k.val = q.val + 1` (`q : Fin N`), the deleted letter of the `k`-th face
is `delIdx k = q.succ` and the letter preceding it is `q.castSucc`.  Hence

* `IsA N A k` holds iff both `q.succ` and `q.castSucc` lie in `A`;
* `IsB N A k` holds iff neither of them does.

So the "mixed" predicate `IsD N A k = ¬ IsA N A k ∧ ¬ IsB N A k` says precisely that *exactly one*
of the two adjacent positions `q.castSucc`, `q.succ` is in `A`, i.e. `q.castSucc ∈ A ↔ q.succ ∉ A`.

This is the reverse of `Work.Cohomology.EZG.isD_dcond`, and together they identify the set of
mixed indices `sD` of the expanded boundary with the set of `k` that swap the state of the pair
`(q.castSucc, q.succ)`.
-/
import Mathlib
import Submission.Work.Cohomology.EZG.dAux

namespace Work.Cohomology.EZG

open Work.Cohomology

theorem isD_iff_dcond {N : ℕ} (A : Finset (Fin (N+1))) (k : Fin (N+2)) (q : Fin N) (hk : k.val = q.val + 1) : Work.Cohomology.EZG.IsD N A k ↔ (q.castSucc ∈ A ↔ q.succ ∉ A) := by
  -- the deleted letter is `q.succ`
  have hdel : delIdx k = q.succ := by
    ext
    simp only [delIdx_val, Fin.val_succ]
    rw [hk, Nat.min_eq_left (Nat.succ_le_of_lt q.isLt)]
  -- the letter preceding the deleted one is `q.castSucc`
  have hprev : (⟨k.val - 1, by omega⟩ : Fin (N+1)) = q.castSucc := by
    ext
    simp only [Fin.val_castSucc]
    omega
  -- `k.val = q.val + 1` is never an endpoint, so the endpoint disjuncts are vacuous
  have hk0 : k.val ≠ 0 := by omega
  have hkl : k.val ≠ N + 1 := by omega
  -- `IsA` says both adjacent positions are in `A`
  have hA : IsA N A k ↔ (q.succ ∈ A ∧ q.castSucc ∈ A) := by
    unfold IsA
    rw [hdel, hprev]
    constructor
    · rintro ⟨h1, h2 | h2 | h2⟩
      · exact absurd h2 hk0
      · exact absurd h2 hkl
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inr (Or.inr h2)⟩
  -- `IsB` says neither of them is
  have hB : IsB N A k ↔ (q.succ ∉ A ∧ q.castSucc ∉ A) := by
    unfold IsB
    rw [hdel, hprev]
    constructor
    · rintro ⟨h1, h2 | h2 | h2⟩
      · exact absurd h2 hk0
      · exact absurd h2 hkl
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inr (Or.inr h2)⟩
  unfold IsD
  rw [hA, hB]
  tauto

end Work.Cohomology.EZG
