import Mathlib
import Submission.Work.OROneRel.gauge_walk_defs

/-!
# A word with a letter of non-zero weight visits at least two levels

Let `c : α → ℤ` be a weight function and `L` a word.  Reading the letters of `L` from the left while
keeping track of the running weight gives the level list `running c i L` (`i` is the starting
level), whose `j`-th entry is the level reached after reading the first `j` letters.  Reading a
letter of non-zero weight strictly changes the level: if a letter `(a, b)` has `c a ≠ 0`, then its
weight `if b then c a else -c a` is non-zero, so the level just before and the level just after
that letter are distinct and both occur in the level list.

Consequently, if some letter of `L` has non-zero weight then the level list contains at least two
distinct levels, i.e. `2 ≤ (running c 0 L).toFinset.card`.  This is the auxiliary lemma
`c_eq_zero_of_running_toFinset_card_le_one` below, stated in contrapositive form.
-/

namespace Work.OROneRel

universe u

/-- **A walk visiting at most one level reads only letters of weight zero.**  If the level list of
`L` started at the level `i` has at most one distinct entry, then it is constant equal to `i` and
every letter of `L` has weight `c p.1 = 0`.  (A letter of non-zero weight would move the level, so
the level just after it would be a second, distinct, entry of the list.) -/
theorem c_eq_zero_of_running_toFinset_card_le_one {α : Type u} (c : α → ℤ)
    (L : List (α × Bool)) :
    ∀ i : ℤ, (running c i L).toFinset.card ≤ 1 → ∀ p ∈ L, c p.1 = 0 := by
  induction L with
  | nil => intro i h p hp; exact absurd hp List.not_mem_nil
  | cons q L ih =>
    intro i h p hp
    obtain ⟨a, b⟩ := q
    rw [List.mem_cons] at hp
    rcases hp with hp | hp
    · -- the letter under consideration is the first letter `(a, b)`
      subst hp
      cases b
      · -- negative letter: the level moves from `i` down to `i - c a`
        change c a = 0
        have h1 : i ∈ (running c i ((a, false) :: L)).toFinset := by
          rw [List.mem_toFinset]; simp only [running]; exact List.mem_cons_self
        have h2 : i - c a ∈ (running c i ((a, false) :: L)).toFinset := by
          rw [List.mem_toFinset]; simp only [running]
          rw [← running_eq_cons_tail c (i - c a) L]
          simp
        have hc := (Finset.card_le_one.mp h) i h1 (i - c a) h2
        omega
      · -- positive letter: the level moves from `i` up to `i + c a`
        change c a = 0
        have h1 : i ∈ (running c i ((a, true) :: L)).toFinset := by
          rw [List.mem_toFinset]; simp only [running]; exact List.mem_cons_self
        have h2 : i + c a ∈ (running c i ((a, true) :: L)).toFinset := by
          rw [List.mem_toFinset]; simp only [running]
          rw [← running_eq_cons_tail c (i + c a) L]
          simp
        have hc := (Finset.card_le_one.mp h) i h1 (i + c a) h2
        omega
    · -- the letter under consideration lies in the tail: recurse after the first letter
      cases b
      · have hsub : (running c (i - c a) L).toFinset ⊆
            (running c i ((a, false) :: L)).toFinset := by
          simp only [running, List.toFinset_cons]
          exact Finset.subset_insert _ _
        exact ih (i - c a) (le_trans (Finset.card_le_card hsub) h) p hp
      · have hsub : (running c (i + c a) L).toFinset ⊆
            (running c i ((a, true) :: L)).toFinset := by
          simp only [running, List.toFinset_cons]
          exact Finset.subset_insert _ _
        exact ih (i + c a) (le_trans (Finset.card_le_card hsub) h) p hp

theorem running_ncard_two {α : Type u} (c : α → ℤ) (L : List (α × Bool))
    (hne : ∃ p ∈ L, c p.1 ≠ 0) :
    2 ≤ (Work.OROneRel.running c 0 L).toFinset.card := by
  rcases hne with ⟨p, hp, hc⟩
  by_contra h
  rw [not_le] at h
  have hle : (running c 0 L).toFinset.card ≤ 1 := by omega
  exact hc (c_eq_zero_of_running_toFinset_card_le_one c L 0 hle p hp)

end Work.OROneRel
