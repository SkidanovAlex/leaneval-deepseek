import Submission.Work.Item3.CoverBound
import Submission.Work.Item3.NoReappearance

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# Item 3, WitnessCover: the covering bound instantiated on witness coordinates

`CoverBound` gives the word-level covering bound (every genuinely-new letter
of an affected word lies in `newLetterSet A`, `|newLetterSet A| ≤ 2·|A|`).
This module instantiates it on a coordinate of a hypothetical surviving
witness: for a coordinate `k` that the item-2 pass combined because its word
ends with `B` (the sharp ends-with-`B` case, driven by
`NoReappearance.item2Pass_apply_ends`), the new basis image is
`w_k · w_c⁻¹`, whose word is `reduce (Y ++ invRev A)` (the `B`-suffix and the
`invRev B` half of `w_c⁻¹` cancel, `rebalance_join_reduce`), so every letter
of the new word is old or in `newLetterSet A` —

    pass_ends_coord_new_letters : l ∈ toWord((α·pass)(a_k))
        ⟹ l ∈ toWord(α(a_k)) ∨ l ∈ newLetterSet A

The begins-with-`B⁻¹` mirror and the inert coordinates (`item2Pass_fix`:
`k ∉ Q` or `item2`-identity, purely old letters) are the symmetric cases; the
three-coordinate covering of a witness (`w'_{row i}`, predecessor, successor)
is their union, feeding the `NoReappearance` contradiction.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **Covering bound, single coordinate (ends-with-`B` case).**  A coordinate
`k` that the item-2 pass combined because its word ends with `B` (the second
half of the balanced word `w_c = A ++ B`) has, after the pass, a word whose
every letter is old (a letter of `w_k`) or lies in the new-letter set
`newLetterSet A` (size ≤ `2·|A|`, from the balanced first half and its
inverses). -/
theorem pass_ends_coord_new_letters {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c k : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) (hkQ : k ∈ Q) (hkc : k ≠ c) (hcQ : c ∉ Q)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B)
    (hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of k)).toWord = Y ++ B) :
    ∀ l ∈ ((α * item2Pass α c A B Q) (FreeGroup.of k)).toWord,
      l ∈ (α (FreeGroup.of k)).toWord ∨ l ∈ newLetterSet A := by
  rcases hE with ⟨Y, hk⟩
  have happ := item2Pass_apply_ends α c A B Q hnd hkQ hkc hcQ (by exact ⟨Y, hk⟩)
  -- happ : (α·pass)(a_k) = w_k · w_c⁻¹
  have hw : ((α * item2Pass α c A B Q) (FreeGroup.of k)).toWord =
      FreeGroup.reduce (Y ++ FreeGroup.invRev A) := by
    rw [happ]
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv]
    rw [hk, hmid]
    rw [FreeGroup.invRev_append]
    exact rebalance_join_reduce A B Y
  intro l hl
  rw [hw] at hl
  rcases replace_suffix_new_letters Y A l hl with hY | hNew
  · left
    rw [hk]
    exact List.mem_append.mpr (Or.inl hY)
  · right
    exact hNew

/-- **Covering bound, single coordinate (begins-with-`B⁻¹` case).**  The
mirror of `pass_ends_coord_new_letters`: a coordinate `k` that the pass
combined because its word begins with `B⁻¹` has, after the pass, a word
whose every letter is old or in `newLetterSet A`. -/
theorem pass_begins_coord_new_letters {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c k : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) (hkQ : k ∈ Q) (hkc : k ≠ c) (hcQ : c ∉ Q)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B)
    (hnoE : ¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of k)).toWord = Y ++ B)
    (hB : ∃ Y : List (Fin n × Bool),
      (α (FreeGroup.of k)).toWord = FreeGroup.invRev B ++ Y) :
    ∀ l ∈ ((α * item2Pass α c A B Q) (FreeGroup.of k)).toWord,
      l ∈ (α (FreeGroup.of k)).toWord ∨ l ∈ newLetterSet A := by
  rcases hB with ⟨Y, hk⟩
  have happ := item2Pass_apply_begins α c A B Q hnd hkQ hkc hcQ hnoE (by exact ⟨Y, hk⟩)
  have hw : ((α * item2Pass α c A B Q) (FreeGroup.of k)).toWord =
      FreeGroup.reduce (A ++ Y) := by
    rw [happ]
    rw [FreeGroup.toWord_mul]
    rw [hmid, hk]
    rw [show (A ++ B) ++ (FreeGroup.invRev B ++ Y) =
        A ++ ((B ++ FreeGroup.invRev B) ++ Y) by simp [List.append_assoc]]
    rw [reduce_middle_empty (X := A) (M := B ++ FreeGroup.invRev B) (Z := Y)
      (reduce_append_invRev_self B)]
  intro l hl
  rw [hw] at hl
  rcases replace_prefix_new_letters A Y l hl with hY | hNew
  · left
    rw [hk]
    exact List.mem_append.mpr (Or.inr hY)
  · right
    exact hNew

/-- **Inert coordinates are purely old.**  A coordinate not in `Q` keeps its
word under the pass (`item2Pass_fix`), so its letters are all old. -/
theorem pass_inert_coord_old_letters {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c k : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hk : k ∉ Q) :
    ((α * item2Pass α c A B Q) (FreeGroup.of k)).toWord =
      (α (FreeGroup.of k)).toWord := by
  exact congrArg (fun g : FreeGroup (Fin n) => g.toWord)
    (item2Pass_fix α c A B Q hk)

end Submission.Nielsen
