import Mathlib
import Submission.Work.OROneRel.tlWinCherryDefs

/-!
# The end level of a walk inside a window

`decor c s A` is the walk of the word `A` read from the running level `s`.  A decorated letter whose
edge `coverEdge e` lies in the window `winE c lo hi` contributes both of its endpoints to the window:
for a positive letter the decorated symbol is `((a,s),true)`, so its endpoints are the running level
`s` and the next level `s + c a`; for a negative letter the symbol is `((a,s - c a),false)`, so its
endpoints are `s - c a` (which is the next running level) and `s`.  Hence, if every edge of the walk
lies in the window `[0,m]` and the starting level `s` lies in `[0,m]`, then the *final* running level
`s + lsig c A` lies in `[0,m]` as well.

This is the elementary bookkeeping behind the "old end window" case of the cherry lemma: the
connection paths of a cherry must both start and end in the old window `[0,m]`.
-/

namespace Work.OROneRel

/-- **Bookkeeping of the running levels.**  If the walk `decor c s A` starts at a level `s` of the
window `winE c 0 m` and every edge of the walk lies in the window, then the final running level
`s + lsig c A` lies in the window.  Induction on `A`: the head letter declares the next running level
to be in the window (`winE` names both endpoints of the edge), and the tail is the walk of the tail
word read from that next level. -/
private theorem end_window_aux {α : Type*} (c : α → ℤ) (m : ℤ) :
    ∀ (s : ℤ) (A : List (α × Bool)),
      (∀ e ∈ decor c s A, coverEdge e ∈ winE c 0 m) → 0 ≤ s → s ≤ m →
      0 ≤ s + lsig c A ∧ s + lsig c A ≤ m := by
  intro s A
  induction A generalizing s with
  | nil =>
      intro hA h0 hm
      rw [show lsig c ([] : List (α × Bool)) = 0 from rfl]
      exact ⟨by simpa using h0, by simpa using hm⟩
  | cons p t ih =>
      intro hA h0 hm
      obtain ⟨a, b⟩ := p
      -- the head letter of the decorated walk, and the window conditions on its edge
      have hhead : ((a, if b then s else s - c a), b) ∈ decor c s ((a, b) :: t) := by
        rw [decor_cons_l]
        exact List.mem_cons_self
      have hw := hA ((a, if b then s else s - c a), b) hhead
      simp only [coverEdge] at hw
      rw [mem_winE] at hw
      obtain ⟨h1, h2, h3, h4⟩ := hw
      -- the next running level `s + linc c (a,b)` lies in the window
      have hs' : 0 ≤ s + linc c (a, b) ∧ s + linc c (a, b) ≤ m := by
        cases b
        · -- negative letter: its edge is `(a, s - c a)`, which *is* the next running level
          simp only [Bool.false_eq_true, if_false] at h1 h2
          simp only [linc, Bool.false_eq_true, if_false]
          omega
        · -- positive letter: its edge is `(a, s)`, whose other endpoint is the next running level
          simp only [if_true] at h3 h4
          simp only [linc, if_true]
          omega
      obtain ⟨hs'0, hs'm⟩ := hs'
      -- the tail of the walk is the decoration of the tail word at the next running level
      have htail : ∀ e ∈ decor c (s + linc c (a, b)) t, coverEdge e ∈ winE c 0 m := by
        intro e he
        apply hA e
        rw [decor_cons_l]
        exact List.mem_cons_of_mem _ he
      obtain ⟨h1', h2'⟩ := ih (s + linc c (a, b)) htail hs'0 hs'm
      rw [lsig_cons_l]
      constructor <;> linarith

/-- **The end level of a walk inside the window `[0,m]`.**  If a walk of the word `A` read from the
level `s ∈ [0,m]` only traverses edges of the window `[0,m]`, then its final running level
`s + lsig (tlW p q) A` also lies in `[0,m]`. -/
theorem cherry_old_end_window (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m) {s : ℤ} (h0 : 0 ≤ s) (hm : s ≤ m)
    {A : List (Fin 2 × Bool)}
    (hA : ∀ e ∈ decor (tlW p q) s A, coverEdge e ∈ winE (tlW p q) 0 m) :
    0 ≤ s + lsig (tlW p q) A ∧ s + lsig (tlW p q) A ≤ m :=
  end_window_aux (tlW p q) m s A hA h0 hm

end Work.OROneRel
