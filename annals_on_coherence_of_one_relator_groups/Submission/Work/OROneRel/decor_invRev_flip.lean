import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.decor_pow_flatMap

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The weight of the inverse of a single letter changes sign. -/
lemma lsig_invRev_singleton (c : α → ℤ) (x : α × Bool) :
    lsig c (FreeGroup.invRev [x]) = -lsig c [x] := by
  obtain ⟨a, b⟩ := x
  cases b <;> simp [FreeGroup.invRev, lsig]

/-- The decoration of a single letter, under reversal: reading the letter backwards from level `i`
gives the same as reading it forwards from the complementary level `i - lsig c [x]`, with the
boolean flipped. -/
lemma decor_invRev_singleton (c : α → ℤ) (i : ℤ) (x : α × Bool) :
    decor c i (FreeGroup.invRev [x]) =
      (decor c (i - lsig c [x]) [x]).reverse.map (fun p : (α × ℤ) × Bool => (p.1, !p.2)) := by
  obtain ⟨a, b⟩ := x
  cases b <;> simp [FreeGroup.invRev, decor, lsig]

/-- **The decoration reverses.**  Reading a word `L` backwards from the level `i` decorates the
letters in the reverse order, with the booleans flipped, and visited from the level reached when
the word is read forwards starting at the complementary level `i - lsig c L`. -/
lemma decor_invRev_flip_aux (c : α → ℤ) (L : List (α × Bool)) :
    ∀ i : ℤ, decor c i (FreeGroup.invRev L) =
      (decor c (i - lsig c L) L).reverse.map (fun p : (α × ℤ) × Bool => (p.1, !p.2)) := by
  induction L using List.reverseRecOn with
  | nil =>
    intro i
    simp [FreeGroup.invRev, decor]
  | append_singleton M x ih =>
    intro i
    rw [FreeGroup.invRev_append, decor_append]
    rw [decor_lsig_append]
    rw [ih (i + lsig c (FreeGroup.invRev [x]))]
    rw [decor_append, List.reverse_append, List.map_append]
    have hx1 : i + lsig c (FreeGroup.invRev [x]) - lsig c M =
        i - (lsig c M + lsig c [x]) := by
      rw [lsig_invRev_singleton]; ring
    have hx2 : i - (lsig c M + lsig c [x]) + lsig c M = i - lsig c [x] := by ring
    rw [decor_invRev_singleton, hx1, hx2]

theorem decor_invRev_flip {α : Type*} (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    Work.OROneRel.decor c i (FreeGroup.invRev L) =
      (Work.OROneRel.decor c (i - Work.OROneRel.lsig c L) L).reverse.map
        (fun p : (α × ℤ) × Bool => (p.1, !p.2)) :=
  decor_invRev_flip_aux c L i

end Work.OROneRel
