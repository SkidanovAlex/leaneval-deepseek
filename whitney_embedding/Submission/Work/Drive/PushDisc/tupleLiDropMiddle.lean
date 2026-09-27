import Mathlib

namespace Work.Drive.PushDisc

/-- The reindexing embedding used in `tupleLiDropMiddle`: it sends the first `r` coordinates of
`Fin (r + k)` into the `a`-block and the last `k` coordinates into the `c`-block of
`Fin ((r + k) + k)`, i.e. it skips the `b`-block of `Fin.append (Fin.append a b) c`. -/
private def dropMiddleIndex (r k : ℕ) : Fin (r + k) → Fin ((r + k) + k) :=
  Fin.addCases (motive := fun _ => Fin ((r + k) + k))
    (fun i : Fin r => Fin.castAdd k (Fin.castAdd k i))
    (fun j : Fin k => Fin.natAdd (r + k) j)

private lemma dropMiddleIndex_injective (r k : ℕ) : Function.Injective (dropMiddleIndex r k) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i' =>
    induction j using Fin.addCases with
    | left j' =>
      simp only [dropMiddleIndex, Fin.addCases_left] at hij
      exact Fin.ext (by simpa using congrArg Fin.val hij)
    | right j' =>
      simp only [dropMiddleIndex, Fin.addCases_left, Fin.addCases_right] at hij
      have hv : (Fin.castAdd k (Fin.castAdd k i')).val = (Fin.natAdd (r + k) j').val :=
        congrArg Fin.val hij
      simp at hv
      omega
  | right i' =>
    induction j using Fin.addCases with
    | left j' =>
      simp only [dropMiddleIndex, Fin.addCases_left, Fin.addCases_right] at hij
      have hv : (Fin.natAdd (r + k) i').val = (Fin.castAdd k (Fin.castAdd k j')).val :=
        congrArg Fin.val hij
      simp at hv
      omega
    | right j' =>
      simp only [dropMiddleIndex, Fin.addCases_right] at hij
      exact Fin.ext (by simpa using congrArg Fin.val hij)

/-- Dropping the *middle* block of an independent `Fin.append`-built tuple: if
`Fin.append (Fin.append a b) c` is linearly independent then so is `Fin.append a c`.
(This is just "a subfamily of an independent family is independent", stated for `Fin.append`
tuples.) -/
theorem tupleLiDropMiddle {F : Type*} [AddCommGroup F] [Module ℝ F] {r k : ℕ}
    (a : Fin r → F) (b : Fin k → F) (c : Fin k → F)
    (h : LinearIndependent ℝ (Fin.append (Fin.append a b) c)) :
    LinearIndependent ℝ (Fin.append a c) := by
  classical
  have hcomp := h.comp (dropMiddleIndex r k) (dropMiddleIndex_injective r k)
  have heq : (Fin.append (Fin.append a b) c) ∘ dropMiddleIndex r k = Fin.append a c := by
    funext i
    induction i using Fin.addCases with
    | left i' => simp [dropMiddleIndex, Fin.addCases_left, Fin.append_left]
    | right j' => simp [dropMiddleIndex, Fin.addCases_right, Fin.append_right]
  rw [heq] at hcomp
  exact hcomp

end Work.Drive.PushDisc
