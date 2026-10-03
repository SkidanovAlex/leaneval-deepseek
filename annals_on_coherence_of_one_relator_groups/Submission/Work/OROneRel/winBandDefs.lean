/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The `band` predicate: a word whose walk stays in a window

`decor c 0 L` is the walk of the word `L` in the `ℤ`-cover of the rose at the levels `ℤ`: the
letter read at running level `i` is the *edge* from `i` to `i + c x` (traversed forwards for a
positive letter, backwards for a negative one).  The window `winE c lo hi`
(`Submission.Work.OROneRel.winBasisDefs`) is the set of edges both of whose endpoints lie in
`[lo,hi]`.

This file introduces the equivalent, level-indexed description: `band c lo hi L` says that *every
level visited by the walk of `L`* (i.e. `lsig c (L.take k)` for `0 ≤ k ≤ L.length`) lies in
`[lo,hi]`.  The two descriptions agree:

* `band_of_winE_decor`: a nonempty word whose edges are all in the window has all its levels in the
  window;
* `winE_decor_of_band`: a word whose levels all lie in the window has all its edges in the window.

The level-indexed form is the one that behaves well under free reduction: cancelling an adjacent
inverse pair removes a level from the walk, never adds one, so `band` is invariant under
`FreeGroup.reduce` (`band_reduce`).
-/
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.gauge_walk_defs
import Submission.Work.OROneRel.interval_defs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The band predicate.**  The walk of the word `L`, started at level `0`, stays inside the
window `[lo,hi]`: every level `lsig c (L.take k)` visited by it lies in `[lo,hi]`. -/
def band (c : α → ℤ) (lo hi : ℤ) (L : List (α × Bool)) : Prop :=
  ∀ k : ℕ, k ≤ L.length → lo ≤ lsig c (L.take k) ∧ lsig c (L.take k) ≤ hi

/-- Unfolding of `band`. -/
theorem band_iff (c : α → ℤ) (lo hi : ℤ) (L : List (α × Bool)) :
    band c lo hi L ↔
      ∀ k : ℕ, k ≤ L.length → lo ≤ lsig c (L.take k) ∧ lsig c (L.take k) ≤ hi :=
  Iff.rfl

/-- The empty word is in the band as soon as `0` is. -/
theorem band_nil (c : α → ℤ) (lo hi : ℤ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    band c lo hi [] := by
  intro k hk
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
  subst hk0
  simpa [lsig] using ⟨hlo, hhi⟩

/-- Weakening the window. -/
theorem band_mono {c : α → ℤ} {lo hi lo' hi' : ℤ} (h1 : lo' ≤ lo) (h2 : hi ≤ hi')
    {L : List (α × Bool)} (h : band c lo hi L) : band c lo' hi' L :=
  fun k hk => ⟨le_trans h1 (h k hk).1, le_trans (h k hk).2 h2⟩

/-- Every level of the walk is in the window, at the index of the prefix. -/
theorem band.mem {c : α → ℤ} {lo hi : ℤ} {L : List (α × Bool)} (h : band c lo hi L)
    {k : ℕ} (hk : k ≤ L.length) : lo ≤ lsig c (L.take k) ∧ lsig c (L.take k) ≤ hi :=
  h k hk

/-- The level `0`, where the walk starts, is in the window. -/
theorem band.zero {c : α → ℤ} {lo hi : ℤ} {L : List (α × Bool)} (h : band c lo hi L) :
    lo ≤ 0 ∧ 0 ≤ hi := by
  simpa [lsig] using h 0 (Nat.zero_le _)

/-- Appending a letter to a word in the band, when the level it reaches is in the window. -/
theorem band_append_singleton {c : α → ℤ} {lo hi : ℤ} {L : List (α × Bool)} (h : band c lo hi L)
    {g : α × Bool} {y : ℤ} (hg : lsig c L + (if g.2 then c g.1 else -c g.1) = y)
    (hy : lo ≤ y ∧ y ≤ hi) : band c lo hi (L ++ [g]) := by
  intro k hk
  by_cases hkL : k ≤ L.length
  · rw [List.take_append_of_le_length hkL]
    exact h k hkL
  · have hk1 : k = L.length + 1 := by
      simp only [List.length_append, List.length_singleton] at hk
      omega
    subst hk1
    rw [List.take_of_length_le (by simp)]
    have hls : lsig c (L ++ [g]) = y := by
      rw [show lsig c (L ++ [g]) = lsig c L + lsig c [g] from by
        simp only [lsig, List.map_append]
        rw [List.sum_append, List.map_singleton]]
      simp only [lsig, List.map_singleton, List.sum_singleton]
      exact hg
    rw [hls]
    exact hy

/-- **The endpoints of a decorated letter lie in the window exactly when its edge does.** -/
theorem coverEdge_mem_winE_iff (c : α → ℤ) (lo hi : ℤ) (q : (α × ℤ) × Bool) :
    coverEdge q ∈ winE c lo hi ↔
      lo ≤ coverSrc c q ∧ coverSrc c q ≤ hi ∧ lo ≤ coverTgt c q ∧ coverTgt c q ≤ hi := by
  obtain ⟨⟨x, i⟩, b⟩ := q
  cases b
  · simp only [coverEdge, coverSrc, coverTgt, winE, Set.mem_ofPred_eq, Bool.false_eq_true,
      if_false]
    constructor <;> intro h <;> exact ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩
  · simp only [coverEdge, coverSrc, coverTgt, winE, Set.mem_ofPred_eq, if_true]

end Work.OROneRel
