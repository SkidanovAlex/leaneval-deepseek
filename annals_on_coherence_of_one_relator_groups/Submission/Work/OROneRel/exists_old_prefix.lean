import Mathlib
import Submission.Work.OROneRel.tlWinCherryDefs

namespace Work.OROneRel

/-- **The combinatorial core of `exists_old_prefix`.**  The statement asks about the window `[0,N]`
of `[0,N+1]`, but the decoration `decor c i L` is a walk on the levels `ℤ` *never mind which* files
the levels have been glued to and *never mind* which weight `c : Fin 2 → ℤ` is used: the only facts
used are

* `decor_cons_decorAt` -- the decoration of a cons is the decoration of its head followed by the
  decoration of the tail at the shifted level, and
* `lsig_cons_l` -- the level shift of a cons is `linc` of the head plus the level shift of the tail.

Reading the word from the left, let `x` be the *first* letter whose edge `coverEdge (decorAt c · x)`
leaves the smaller window `[0,N]`.  Then everything before `x` is decorated inside `[0,N]`, `x`'s
edge lies in `winE c 0 (N+1)` but not in `winE c 0 N`, and the rest is decorated inside `winE c 0
(N+1)` by hypothesis.  If no such letter exists, all edges lie in `winE c 0 N`. -/
theorem exists_old_prefix_gen (c : Fin 2 → ℤ) (N : ℤ) (i : ℤ) (L : List (Fin 2 × Bool))
    (hL : ∀ e ∈ decor c i L, coverEdge e ∈ winE c 0 (N + 1)) :
    (∀ e ∈ decor c i L, coverEdge e ∈ winE c 0 N) ∨
      ∃ (A : List (Fin 2 × Bool)) (x : Fin 2 × Bool) (B : List (Fin 2 × Bool)),
        L = A ++ x :: B ∧
        (∀ e ∈ decor c i A, coverEdge e ∈ winE c 0 N) ∧
        coverEdge (decorAt c (i + lsig c A) x) ∉ winE c 0 N ∧
        coverEdge (decorAt c (i + lsig c A) x) ∈ winE c 0 (N + 1) ∧
        (∀ e ∈ decor c (i + lsig c A) (x :: B), coverEdge e ∈ winE c 0 (N + 1)) := by
  induction L generalizing i with
  | nil =>
    left
    intro e he
    simp [decor] at he
  | cons y L' ih =>
    by_cases hy : coverEdge (decorAt c i y) ∈ winE c 0 N
    · have htail : ∀ e ∈ decor c (i + linc c y) L', coverEdge e ∈ winE c 0 (N + 1) := by
        intro e he
        exact hL e (by rw [decor_cons_decorAt]; exact List.mem_cons_of_mem _ he)
      rcases ih (i + linc c y) htail with hleft | ⟨A', x, B', hAB, hA, hxN, hxN1, hrest⟩
      · left
        intro e he
        rw [decor_cons_decorAt] at he
        rcases List.mem_cons.mp he with h | h
        · rw [h]; exact hy
        · exact hleft e h
      · right
        have hls : i + lsig c (y :: A') = (i + linc c y) + lsig c A' := by
          rw [lsig_cons_l]; ring
        refine ⟨y :: A', x, B', by rw [hAB]; simp, ?_, ?_, ?_, ?_⟩
        · intro e he
          rw [decor_cons_decorAt] at he
          rcases List.mem_cons.mp he with h | h
          · rw [h]; exact hy
          · exact hA e h
        · rw [hls]; exact hxN
        · rw [hls]; exact hxN1
        · rw [hls]; exact hrest
    · right
      have hhead_mem : decorAt c i y ∈ decor c i (y :: L') := by
        rw [decor_cons_decorAt]; simp
      refine ⟨[], y, L', by simp, ?_, ?_, ?_, ?_⟩
      · intro e he
        simp [decor] at he
      · simpa [lsig] using hy
      · have h := hL _ hhead_mem
        simpa [lsig] using h
      · simpa [lsig] using hL

theorem exists_old_prefix (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m) (i : ℤ) (L : List (Fin 2 × Bool))
    (hL : ∀ e ∈ decor (tlW p q) i L, coverEdge e ∈ winE (tlW p q) 0 (m + 1)) :
    (∀ e ∈ decor (tlW p q) i L, coverEdge e ∈ winE (tlW p q) 0 m) ∨
      ∃ (A : List (Fin 2 × Bool)) (x : Fin 2 × Bool) (B : List (Fin 2 × Bool)),
        L = A ++ x :: B ∧
        (∀ e ∈ decor (tlW p q) i A, coverEdge e ∈ winE (tlW p q) 0 m) ∧
        coverEdge (decorAt (tlW p q) (i + lsig (tlW p q) A) x) ∉ winE (tlW p q) 0 m ∧
        coverEdge (decorAt (tlW p q) (i + lsig (tlW p q) A) x) ∈ winE (tlW p q) 0 (m + 1) ∧
        (∀ e ∈ decor (tlW p q) (i + lsig (tlW p q) A) (x :: B),
          coverEdge e ∈ winE (tlW p q) 0 (m + 1)) :=
  exists_old_prefix_gen (tlW p q) m i L hL

end Work.OROneRel
