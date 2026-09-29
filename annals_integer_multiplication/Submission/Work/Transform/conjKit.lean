import Mathlib
import Submission.HvdH.Interfaces

/-!
# Kit for the conjugation words (`Work.Transform.conjVecWord`, `Work.Transform.conjElemWord`)

Conjugating a fixed-point complex coefficient `z = (x, y)` (represented as the value
`cfxVal z = cons (int x) (int y)`) means negating its **second** component.  This file holds the
pure-data vocabulary shared by the per-coefficient word `Work.Transform.conjElemWord` and the
vector-level assembly `Work.Transform.conjVecWord`: the map `conjPair`, the fact that it preserves
the disc condition `C̃◦`, and the two elementary index/encoding lemmas that turn a
`List.Forall₂`-style pointwise statement back into a statement about `cvecVal (u.map conjPair)`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- Conjugate a fixed-point complex coefficient: negate the imaginary part. -/
def conjPair (z : ℤ × ℤ) : ℤ × ℤ := (z.1, -z.2)

@[simp] theorem conjPair_apply (z : ℤ × ℤ) : conjPair z = (z.1, -z.2) := rfl

theorem conjPair_involutive (z : ℤ × ℤ) : conjPair (conjPair z) = z := by
  simp [conjPair]

/-- Conjugation preserves the disc condition `C̃◦` (`x² + y² = x² + (-y)²`). -/
theorem inDisc_conjPair {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : inDisc p (conjPair z) := by
  simp only [inDisc, conjPair] at h ⊢
  nlinarith [h]

/-- The `i`-th coefficient of `u.map conjPair` is the conjugate of the `i`-th coefficient of `u`. -/
theorem getD_map_conjPair (u : List (ℤ × ℤ)) (i : ℕ) :
    (u.map conjPair).getD i (0, 0) = ((u.getD i (0, 0)).1, -(u.getD i (0, 0)).2) := by
  have h : ((0 : ℤ), (0 : ℤ)) = conjPair ((0 : ℤ), (0 : ℤ)) := rfl
  rw [h, List.getD_map]
  rfl

/-- Conjugation acts coefficientwise on a disc vector. -/
theorem inDiscVec_map_conjPair {p n : ℕ} {u : List (ℤ × ℤ)} (h : InDiscVec p n u) :
    InDiscVec p n (u.map conjPair) := by
  refine ⟨by rw [List.length_map, h.1], ?_⟩
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
  exact inDisc_conjPair (h.2 z₀ hz₀)

/-- The encoding of `u.map conjPair` is the list of conjugated coefficients. -/
theorem ofList_map_cfxVal_conjPair (u : List (ℤ × ℤ)) :
    ofList ((u.map conjPair).map cfxVal) = cvecVal (u.map conjPair) := rfl

/-- The statement of the per-coefficient conjunction word `Work.Transform.conjElemWord`:
one program that replaces `cfxVal z` by `cfxVal (z.1, -z.2)` on top of the value stack, at cost
`O(p)` (the encoding of a coefficient in `C̃◦` has `≤ 2p + 8` glyphs). -/
def ConjElemSpec : Prop :=
  ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p : ℕ) (z : ℤ × ℤ) (rest : List HvdH.Val),
      HvdH.inDisc p z →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cfxVal z :: rest)
        (fun _ out => out = HvdH.cfxVal (z.1, -z.2) :: rest)
        (fun _ => K * (p + 1))

end Work.Transform
