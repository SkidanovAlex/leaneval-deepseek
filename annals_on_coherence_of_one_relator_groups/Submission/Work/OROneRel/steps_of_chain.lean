import Mathlib

namespace Work.OROneRel

/-- Prepending a single step `d` to a list of steps: the scan of partial sums starting
at `x` is the old scan followed by the new partial sum `x + ss.sum + d`. -/
lemma scanl_append_singleton (ss : List ℤ) (x d : ℤ) :
    (ss ++ [d]).scanl (fun a b => a + b) x
      = ss.scanl (fun a b => a + b) x ++ [x + ss.sum + d] := by
  induction ss generalizing x with
  | nil => simp
  | cons a t ih =>
    simp only [List.cons_append, List.scanl_cons, List.sum_cons, ih]
    congr 1
    ring_nf

/-- A walk in `ℤ` from `x` to `j` whose steps are `±A`, `±B` and which never leaves
`[lo, hi]` can be recorded as a list of signed generators `±A`, `±B` whose partial sums
(starting at `x`) also stay inside `[lo, hi]` and whose total sum is `j - x`. -/
theorem steps_of_chain {A B x j lo hi : ℤ}
    (hchain : Relation.ReflTransGen (fun a b : ℤ => lo ≤ b ∧ b ≤ hi ∧
      (b = a + A ∨ b = a - A ∨ b = a + B ∨ b = a - B)) x j)
    (hx : lo ≤ x ∧ x ≤ hi) :
    ∃ ss : List ℤ, (∀ s ∈ ss, s = A ∨ s = -A ∨ s = B ∨ s = -B) ∧ ss.sum = j - x ∧
      ∀ l ∈ ss.scanl (fun a b => a + b) x, lo ≤ l ∧ l ≤ hi := by
  induction hchain with
  | refl => exact ⟨[], by simp, by simp, by simpa using hx⟩
  | tail hch hstep ih =>
    rename_i b c
    obtain ⟨ss, hmem, hsum, hscan⟩ := ih
    rcases hstep with ⟨hc₁, hc₂, hc⟩
    refine ⟨ss ++ [c - b], ?_, ?_, ?_⟩
    · intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · exact hmem s hs
      · rw [List.mem_singleton] at hs
        rw [hs]
        rcases hc with h | h | h | h <;> omega
    · rw [List.sum_append, List.sum_singleton, hsum]
      ring
    · intro l hl
      have hval : x + ss.sum + (c - b) = c := by rw [hsum]; ring
      have hscanl : (ss ++ [c - b]).scanl (fun a b => a + b) x
          = ss.scanl (fun a b => a + b) x ++ [c] := by
        rw [scanl_append_singleton, hval]
      rw [hscanl] at hl
      rw [List.mem_append] at hl
      rcases hl with hl | hl
      · exact hscan l hl
      · rw [List.mem_singleton] at hl
        rw [hl]
        exact ⟨hc₁, hc₂⟩

end Work.OROneRel
