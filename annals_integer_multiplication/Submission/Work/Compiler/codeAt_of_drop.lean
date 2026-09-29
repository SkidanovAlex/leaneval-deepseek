import Mathlib
import Submission.Work.Compiler.CodeAt

/-!
# `CodeAt` from a dropped prefix

If `code` has `compile c pc` as a prefix after dropping the first `pc` instructions, then `code`
satisfies the position predicate `CodeAt` for `c` at `pc`.  This is the "inverse" of the defining
property of `CodeAt` and lets one read off the invariant from an equation on the code list.
-/

set_option autoImplicit false

namespace Work.Compiler

open HvdH

/-- Reading the element at position `pc` from the hypothesis that a cons is dropped. -/
private lemma head_of_drop {α : Type _} {l : List α} {pc : ℕ} {x : α} {r : List α}
    (h : l.drop pc = x :: r) : l[pc]? = some x := by
  have h' : (l.drop pc)[0]? = some x := by rw [h]; rfl
  rwa [List.getElem?_drop, Nat.add_zero] at h'

/-- Dropping a known prefix `a` of `l.drop pc` leaves the known tail `b`. -/
private lemma drop_suffix {α : Type _} {l : List α} {pc : ℕ} {a b : List α}
    (h : l.drop pc = a ++ b) : l.drop (pc + a.length) = b := by
  rw [← List.drop_drop (i := a.length) (j := pc), h, List.drop_left]

/-- The `i`-th element after the dropped prefix, for `i` inside `a`. -/
private lemma getElem?_drop_suffix {α : Type _} {l : List α} {pc : ℕ} {a b : List α}
    (h : l.drop pc = a ++ b) {i : ℕ} (hi : i < a.length) : l[pc + i]? = a[i]? := by
  have h1 : (l.drop pc)[i]? = l[pc + i]? := List.getElem?_drop
  rw [← h1, h, List.getElem?_append]
  simp [hi]

/-- If the block `compile c pc` is a prefix of `code` after dropping the first `pc` instructions,
then `code` satisfies the position predicate `CodeAt` for `c` at `pc`. -/
theorem codeAt_of_drop {code : List Work.Compiler.Instr} {pc : ℕ} {c : HvdH.Cmd}
    {rest : List Work.Compiler.Instr}
    (h : code.drop pc = Work.Compiler.compile c pc ++ rest) :
    Work.Compiler.CodeAt code pc c := by
  induction c generalizing code pc rest with
  | skip => simpa [CodeAt, compile] using head_of_drop h
  | pop k r => simpa [CodeAt, compile] using head_of_drop h
  | peek k r => simpa [CodeAt, compile] using head_of_drop h
  | push k r => simpa [CodeAt, compile] using head_of_drop h
  | set r c => simpa [CodeAt, compile] using head_of_drop h
  | mov d t => simpa [CodeAt, compile] using head_of_drop h
  | self => simpa [CodeAt, compile] using head_of_drop h
  | seq a b iha ihb =>
      have h1 : code.drop pc = compile a pc ++ (compile b (pc + clen a) ++ rest) := by
        simpa only [compile, List.append_assoc] using h
      refine ⟨iha h1, ?_⟩
      have hh := drop_suffix (a := compile a pc) h1
      rw [compile_length] at hh
      exact ihb hh
  | ite r c p q ihp ihq =>
      have h1 : code.drop pc = [Instr.test r c (pc + clen p + 2)] ++
          (compile p (pc + 1) ++ ([Instr.jmp (pc + clen p + 2 + clen q)] ++
            (compile q (pc + clen p + 2) ++ rest))) := by
        simpa only [compile, List.cons_append, List.nil_append, List.append_assoc] using h
      have hh1 : code.drop (pc + 1) = compile p (pc + 1) ++
          ([Instr.jmp (pc + clen p + 2 + clen q)] ++ (compile q (pc + clen p + 2) ++ rest)) :=
        drop_suffix (a := [Instr.test r c (pc + clen p + 2)]) h1
      have hh2 : code.drop (pc + clen p + 1) =
          [Instr.jmp (pc + clen p + 2 + clen q)] ++ (compile q (pc + clen p + 2) ++ rest) := by
        have hh := drop_suffix (a := compile p (pc + 1)) hh1
        rw [compile_length, show (pc + 1) + clen p = pc + clen p + 1 by omega] at hh
        exact hh
      have hh3 : code.drop (pc + clen p + 2) = compile q (pc + clen p + 2) ++ rest := by
        have hh := drop_suffix (a := [Instr.jmp (pc + clen p + 2 + clen q)]) hh2
        rw [show (pc + clen p + 1) + ([Instr.jmp (pc + clen p + 2 + clen q)] : List Instr).length
            = pc + clen p + 2 by simp] at hh
        exact hh
      refine ⟨?_, ihp hh1, ?_, ihq hh3⟩
      · have hh := getElem?_drop_suffix (a := [Instr.test r c (pc + clen p + 2)]) h1 (i := 0) (by simp)
        simpa using hh
      · have hh := getElem?_drop_suffix (a := [Instr.jmp (pc + clen p + 2 + clen q)]) hh2 (i := 0) (by simp)
        simpa using hh
  | loop r c b ihb =>
      have h1 : code.drop pc = [Instr.test r c (pc + clen b + 2)] ++
          (compile b (pc + 1) ++ ([Instr.jmp pc] ++ rest)) := by
        simpa only [compile, List.cons_append, List.nil_append, List.append_assoc] using h
      have hh1 : code.drop (pc + 1) = compile b (pc + 1) ++ ([Instr.jmp pc] ++ rest) :=
        drop_suffix (a := [Instr.test r c (pc + clen b + 2)]) h1
      have hh2 : code.drop (pc + clen b + 1) = [Instr.jmp pc] ++ rest := by
        have hh := drop_suffix (a := compile b (pc + 1)) hh1
        rw [compile_length, show (pc + 1) + clen b = pc + clen b + 1 by omega] at hh
        exact hh
      refine ⟨?_, ihb hh1, ?_⟩
      · have hh := getElem?_drop_suffix (a := [Instr.test r c (pc + clen b + 2)]) h1 (i := 0) (by simp)
        simpa using hh
      · have hh := getElem?_drop_suffix (a := [Instr.jmp pc]) hh2 (i := 0) (by simp)
        simpa using hh

end Work.Compiler
