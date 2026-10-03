import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Chord

namespace Work.ORDunwoody.ChordWalk

open Work.ORDunwoody.Dunwoody

/-- `pairUp` produces a *matching* of the entries of a list with no repeated entries: an entry is
never the first (resp. second) component of two different pairs, and it is never at the same time
the second component of one pair and the first component of another.

The proof is a direct structural induction following `pairUp`'s two-step recursion. -/
private theorem cwc_pairUp_nodup_aux : ∀ (L : List ℕ), L.Nodup →
    (∀ p q : ℕ, (p, q) ∈ pairUp L → p ∈ L ∧ q ∈ L) ∧
    (∀ p q r : ℕ, (p, q) ∈ pairUp L → (p, r) ∈ pairUp L → q = r) ∧
    (∀ p q r : ℕ, (p, q) ∈ pairUp L → (r, q) ∈ pairUp L → p = r) ∧
    (∀ p q r : ℕ, (p, q) ∈ pairUp L → (q, r) ∈ pairUp L → False)
  | [], _ => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p q h; simp at h
      · intro p q r h; simp at h
      · intro p q r h; simp at h
      · intro p q r h; simp at h
  | [x], _ => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p q h; simp at h
      · intro p q r h; simp at h
      · intro p q r h; simp at h
      · intro p q r h; simp at h
  | x :: y :: rest, hL => by
      rw [List.nodup_cons] at hL
      obtain ⟨hx, hL⟩ := hL
      rw [List.nodup_cons] at hL
      obtain ⟨hy, hrest⟩ := hL
      have hxrest : x ∉ rest := fun h => hx (List.mem_cons_of_mem y h)
      have hxy : x ≠ y := fun h => hx (by rw [h]; exact List.mem_cons_self)
      obtain ⟨hmem, hB, hC, hD⟩ := cwc_pairUp_nodup_aux rest hrest
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- membership
        intro p q h
        rw [pairUp_cons_cons] at h
        rcases List.mem_cons.mp h with h | h
        · rw [Prod.mk.injEq] at h
          rw [h.1, h.2]
          exact ⟨List.mem_cons_self, List.mem_cons_of_mem x List.mem_cons_self⟩
        · obtain ⟨hp, hq⟩ := hmem p q h
          exact ⟨List.mem_cons_of_mem x (List.mem_cons_of_mem y hp),
            List.mem_cons_of_mem x (List.mem_cons_of_mem y hq)⟩
      · -- two pairs with the same first component
        intro p q r h1 h2
        rw [pairUp_cons_cons] at h1 h2
        rcases List.mem_cons.mp h1 with h1 | h1 <;> rcases List.mem_cons.mp h2 with h2 | h2
        · rw [Prod.mk.injEq] at h1 h2
          rw [h1.2, h2.2]
        · rw [Prod.mk.injEq] at h1
          obtain ⟨hpx, hqy⟩ := h1
          rw [hpx] at h2
          rw [hqy]
          exact absurd (List.mem_cons_of_mem y (hmem x r h2).1) hx
        · rw [Prod.mk.injEq] at h2
          obtain ⟨hpx, hry⟩ := h2
          rw [hpx] at h1
          rw [hry]
          exact absurd (List.mem_cons_of_mem y (hmem x q h1).1) hx
        · exact hB p q r h1 h2
      · -- two pairs with the same second component
        intro p q r h1 h2
        rw [pairUp_cons_cons] at h1 h2
        rcases List.mem_cons.mp h1 with h1 | h1 <;> rcases List.mem_cons.mp h2 with h2 | h2
        · rw [Prod.mk.injEq] at h1 h2
          rw [h1.1, h2.1]
        · rw [Prod.mk.injEq] at h1
          obtain ⟨hpx, hqy⟩ := h1
          rw [hqy] at h2
          rw [hpx]
          exact absurd (hmem r y h2).2 hy
        · rw [Prod.mk.injEq] at h2
          obtain ⟨hrx, hqy⟩ := h2
          rw [hqy] at h1
          rw [hrx]
          exact absurd (hmem p y h1).2 hy
        · exact hC p q r h1 h2
      · -- an entry is not both a second and a first component
        intro p q r h1 h2
        rw [pairUp_cons_cons] at h1 h2
        rcases List.mem_cons.mp h1 with h1 | h1 <;> rcases List.mem_cons.mp h2 with h2 | h2
        · rw [Prod.mk.injEq] at h1 h2
          exact hxy (h2.1.symm.trans h1.2)
        · rw [Prod.mk.injEq] at h1
          obtain ⟨hpx, hqy⟩ := h1
          rw [hqy] at h2
          exact absurd (hmem y r h2).1 hy
        · rw [Prod.mk.injEq] at h2
          obtain ⟨hqx, hry⟩ := h2
          rw [hqx] at h1
          exact absurd (hmem p x h1).2 hxrest
        · exact hD p q r h1 h2

theorem cwc_pairUp_matching {L : List ℕ} (hL : L.Pairwise (· < ·)) :
    (∀ p q r : ℕ, (p, q) ∈ Work.ORDunwoody.Dunwoody.pairUp L →
      (p, r) ∈ Work.ORDunwoody.Dunwoody.pairUp L → q = r) ∧
    (∀ p q r : ℕ, (p, q) ∈ Work.ORDunwoody.Dunwoody.pairUp L →
      (r, q) ∈ Work.ORDunwoody.Dunwoody.pairUp L → p = r) ∧
    (∀ p q r : ℕ, (p, q) ∈ Work.ORDunwoody.Dunwoody.pairUp L →
      (q, r) ∈ Work.ORDunwoody.Dunwoody.pairUp L → False) :=
  (cwc_pairUp_nodup_aux L hL.nodup).2

end Work.ORDunwoody.ChordWalk
