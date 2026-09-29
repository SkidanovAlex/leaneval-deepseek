import Mathlib
import Submission.Work.TMC16Core.Basic.pd_cheb_cont

namespace Work.TMC16Core.Basic

open Work.TMC16Core.Cheb

/-- The list `List.range (n+2)` is `List.range n` with `n` and `n+1` appended. -/
private lemma range_add_two (n : ℕ) : List.range (n + 2) = List.range n ++ [n, n + 1] := by
  rw [show n + 2 = n + 1 + 1 from rfl, List.range_succ, List.range_succ]
  simp [List.append_assoc]

/-- `contSeq f (n+3)` unfolds as `f (n+1) * contSeq f (n+2) - contSeq f (n+1)`. -/
private lemma contSeq_add_three {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    contSeq f (n + 3) = f (n + 1) * contSeq f (n + 2) - contSeq f (n + 1) := by
  rw [show n + 3 = (n + 1) + 2 from rfl, contSeq]

theorem cont_range_map {R : Type*} [CommRing R] (f : ℕ → R) (k : ℕ) :
    Work.TMC16Core.Cheb.cont ((List.range k).map f) = Work.TMC16Core.Cheb.contSeq f (k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [List.range_zero, cont_nil, contSeq]
  | one =>
      simp only [List.range_one, List.map_cons, List.map_nil, cont_singleton, contSeq]
      ring
  | more n ih ih1 =>
      rw [range_add_two n]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [cont_append_two]
      have h2 : cont ((List.range n).map f ++ [f n]) = cont ((List.range (n + 1)).map f) := by
        conv_rhs => rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil]
      rw [h2, ih, ih1, contSeq_add_three]

end Work.TMC16Core.Basic
