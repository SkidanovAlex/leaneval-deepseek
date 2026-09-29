import Mathlib
import Submission.Work.SB.P3b.Base

namespace Work.SB.P3b

/-- A list of `A * B` blocks, each of length `n`, flattens to a list of length `A * B * n`. -/
theorem flatLen (A n B : ℕ) (outs : List (List HvdH.Val)) (hlen : outs.length = A * B)
    (hsl : ∀ s, s < A * B → (outs.getD s []).length = n) :
    outs.flatten.length = A * B * n := by
  have h2 : ∀ s, s < outs.length → (outs.getD s []).length = n := by
    intro s hs
    exact hsl s (by omega)
  have key : ∀ (l : List (List HvdH.Val)), (∀ s, s < l.length → (l.getD s []).length = n) →
      l.flatten.length = l.length * n := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons x xs ih =>
      intro h
      have hx : x.length = n := by
        have := h 0 (Nat.succ_pos _)
        simpa using this
      have hxs : ∀ s, s < xs.length → (xs.getD s []).length = n := by
        intro s hs
        have := h (s + 1) (by simp [List.length_cons]; omega)
        simpa using this
      have hrec := ih hxs
      rw [List.flatten_cons, List.length_append, hx, hrec, List.length_cons]
      ring
  rw [key outs h2, hlen]

end Work.SB.P3b
