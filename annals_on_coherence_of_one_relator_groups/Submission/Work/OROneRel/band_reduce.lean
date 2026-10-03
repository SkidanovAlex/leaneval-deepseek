/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The `band` predicate is invariant under free reduction

`band c lo hi L` says that every level visited by the walk of the word `L` -- that is, every value
`lsig c (L.take k)` with `0 ≤ k ≤ L.length` -- lies in the window `[lo,hi]`.

Free reduction (`FreeGroup.reduce`) proceeds by repeatedly deleting an adjacent cancelling pair of
letters `(x,b) (x,!b)` (`FreeGroup.Red.Step`).  Such a pair carries the two opposite weights
`letterW c (x,b)` and `letterW c (x,!b) = -letterW c (x,b)`, so *the level after the pair is the
level before it*: cancelling the pair deletes the single intermediate level of the walk and returns
to the same level.  Hence reduction only ever deletes levels from the walk, never creates one:

* `exists_take_lsig_cancel` is the combinatorial core at the level of `List.take`/`lsig`: every
  prefix level of `A ++ B` is a prefix level of the unreduced word `A ++ (x,b) :: (x,!b) :: B`;
* `band_step` is the same statement for `band`, along one `FreeGroup.Red.Step`;
* `band_red` iterates it along a chain of steps `FreeGroup.Red`;
* `band_reduce` is the instance `M = FreeGroup.reduce L` (`FreeGroup.reduce.red`).

The converse direction (`band` of the reduced word implies `band` of the word) is false in general
for the levels: reduction can only delete levels, not add them.
-/
import Mathlib
import Submission.Work.OROneRel.winBandDefs

namespace Work.OROneRel

universe u

/-! ## Prefix levels and the cancellation of an adjacent inverse pair -/

/-- The weight of a word that begins with a letter. -/
theorem lsig_cons_band {α : Type u} (c : α → ℤ) (p : α × Bool) (M : List (α × Bool)) :
    lsig c (p :: M) = letterW c p + lsig c M := rfl

/-- A cancelling pair of letters has vanishing weight: deleting it from a word does not change the
total weight of the word. -/
theorem lsig_pair_cancel_band {α : Type u} (c : α → ℤ) (x : α) (b : Bool) (M : List (α × Bool)) :
    lsig c ((x, b) :: (x, !b) :: M) = lsig c M := by
  cases b <;> simp [lsig, List.map_cons, List.sum_cons]

/-- **Cancelling an adjacent inverse pair does not remove a prefix level of the walk.**  Every level
`lsig c ((A ++ B).take k)` reached by the word `A ++ B` is also a level reached, at some prefix
length `k'`, by the unreduced word `A ++ (x,b) :: (x,!b) :: B`: before the pair the two walks agree
prefix by prefix, and after the pair they agree again because the pair carries the opposite weights
`letterW c (x,b)` and `letterW c (x,!b)`. -/
theorem exists_take_lsig_cancel {α : Type u} (c : α → ℤ) (x : α) (b : Bool)
    (A B : List (α × Bool)) (k : ℕ) (hk : k ≤ (A ++ B).length) :
    ∃ k' ≤ (A ++ (x, b) :: (x, !b) :: B).length,
      lsig c ((A ++ B).take k) = lsig c ((A ++ (x, b) :: (x, !b) :: B).take k') := by
  induction A generalizing k with
  | nil =>
    -- the level `lsig c (B.take k)` is the level of the unreduced word after `k + 2` letters
    rw [List.nil_append] at hk
    refine ⟨k + 2, by simp only [List.nil_append, List.length_cons]; omega, ?_⟩
    simp only [List.nil_append]
    have htake : ((x, b) :: (x, !b) :: B).take (k + 2) = (x, b) :: (x, !b) :: B.take k := by
      rw [show k + 2 = (k + 1) + 1 from rfl, List.take_succ_cons, List.take_succ_cons]
    rw [htake, lsig_pair_cancel_band]
  | cons a A' ih =>
    cases k with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ j =>
      -- strip the common first letter `a` of both words
      have hkj : j ≤ (A' ++ B).length := by
        simp only [List.length_append, List.length_cons] at hk ⊢
        omega
      obtain ⟨k', hk'le, hk'eq⟩ := ih j hkj
      refine ⟨k' + 1, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons] at hk'le ⊢
        omega
      · simp only [List.cons_append, List.take_succ_cons]
        rw [lsig_cons_band, lsig_cons_band, hk'eq]

/-! ## The band is preserved by free reduction -/

/-- **One reduction step preserves the band.**  This is `exists_take_lsig_cancel` read backwards:
every level of the reduced word `M = A ++ B` is a level of `L = A ++ (x,b) :: (x,!b) :: B`. -/
theorem band_step {α : Type u} {c : α → ℤ} {lo hi : ℤ} {L M : List (α × Bool)}
    (h : FreeGroup.Red.Step L M) (hb : band c lo hi L) : band c lo hi M := by
  cases h with
  | not =>
    intro k hk
    obtain ⟨k', hk'le, hk'eq⟩ := exists_take_lsig_cancel c _ _ _ _ k hk
    rw [hk'eq]
    exact hb k' hk'le

/-- **A chain of reduction steps preserves the band.** -/
theorem band_red {α : Type u} {c : α → ℤ} {lo hi : ℤ} {L M : List (α × Bool)}
    (h : FreeGroup.Red L M) (hb : band c lo hi L) : band c lo hi M := by
  induction h with
  | refl => exact hb
  | tail _ h2 ih => exact band_step h2 ih

/-- **The band predicate is invariant under free reduction.** -/
theorem band_reduce {α : Type u} [DecidableEq α] (c : α → ℤ) (lo hi : ℤ) (L : List (α × Bool))
    (h : Work.OROneRel.band c lo hi L) :
    Work.OROneRel.band c lo hi (FreeGroup.reduce L) :=
  band_red FreeGroup.reduce.red h

end Work.OROneRel
