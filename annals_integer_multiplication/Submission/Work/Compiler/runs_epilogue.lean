import Mathlib
import Submission.Work.Compiler.Steps

namespace Work.Compiler

open HvdH Turing

/-!
# The epilogue of the compiled machine

Starting with `out.map Glyph.bit` on language stack `Sum.inl 1` (first bit on top) and all other
stacks empty, the epilogue moves the bits to the output stack `Sum.inr 1` as `Bool`s in the order
of `out`, in `2 * out.length + 3` steps, resetting the machine state to `initMS`.

The transfer is done in two phases (two reversals):

* phase A (`labE1`): pop from `Sum.inl 1`, push onto `Sum.inl 2` (reversing),
* phase B (`labE2`): pop from `Sum.inl 2`, push `glyphToBool` onto `Sum.inr 1` (reversing back),

followed by one step at the halting label `labH` that clears the label.

We work with explicit iterate equalities `f^[n] (some cfg) = some cfg'` (which live in `Prop`, so
rewriting is unrestricted) and only package the result as an `EvalsToInTime` at the very end.
-/

/-- Stack-vector update of one phase-A step family: stack `Sum.inl 1` becomes empty and the
contents `L` of `Sum.inl 1` (still in order, top first) are pushed onto `Sum.inl 2`. -/
def updA (code : List Instr) (S : (j : KK) → List (Γ code j)) (L : List Glyph) :
    (j : KK) → List (Γ code j) :=
  Function.update (Function.update S (Sum.inl 1) []) (Sum.inl 2) (L.reverse ++ S (Sum.inl 2))

/-- Stack-vector update of one phase-B step family: stack `Sum.inl 2` becomes empty and the
contents `L` of `Sum.inl 2` are pushed (as `Bool`s) onto the output stack `Sum.inr 1`. -/
def updB (code : List Instr) (S : (j : KK) → List (Γ code j)) (L : List Glyph) :
    (j : KK) → List (Γ code j) :=
  Function.update (Function.update S (Sum.inl 2) []) (Sum.inr 1)
    ((L.map glyphToBool).reverse ++ S (Sum.inr 1))

/-- The recursion for the phase-A stack update. -/
theorem updA_cons (code : List Instr) (S : (j : KK) → List (Γ code j)) (g : Glyph)
    (L : List Glyph) :
    updA code (Function.update (Function.update S (Sum.inl 1) L) (Sum.inl 2) (g :: S (Sum.inl 2))) L
      = updA code S (g :: L) := by
  funext j
  by_cases h1 : j = Sum.inl 1
  · subst h1; simp [updA]
  · by_cases h2 : j = Sum.inl 2
    · subst h2; simp [updA, List.reverse_cons, List.append_assoc]
    · simp [updA, h1, h2]

/-- The empty case of the phase-A stack update. -/
theorem updA_nil (code : List Instr) (S : (j : KK) → List (Γ code j)) :
    updA code S [] = Function.update S (Sum.inl 1) [] := by
  funext j
  by_cases h1 : j = Sum.inl 1
  · subst h1; simp [updA]
  · by_cases h2 : j = Sum.inl 2
    · subst h2; simp [updA]
    · simp [updA, h1, h2]

/-- The recursion for the phase-B stack update. -/
theorem updB_cons (code : List Instr) (S : (j : KK) → List (Γ code j)) (g : Glyph)
    (L : List Glyph) :
    updB code (Function.update (Function.update S (Sum.inl 2) L) (Sum.inr 1)
        (glyphToBool g :: S (Sum.inr 1))) L
      = updB code S (g :: L) := by
  funext j
  by_cases h1 : j = Sum.inl 2
  · subst h1; simp [updB]
  · by_cases h2 : j = Sum.inr 1
    · subst h2; simp [updB, List.reverse_cons, List.append_assoc]
    · simp [updB, h1, h2]

/-- The empty case of the phase-B stack update. -/
theorem updB_nil (code : List Instr) (S : (j : KK) → List (Γ code j)) :
    updB code S [] = Function.update S (Sum.inl 2) [] := by
  funext j
  by_cases h1 : j = Sum.inl 2
  · subst h1; simp [updB]
  · by_cases h2 : j = Sum.inr 1
    · subst h2; simp [updB]
    · simp [updB, h1, h2]

/-- One iterate step from a single machine step. -/
theorem iterate_one_eq {σ : Type*} (f : σ → Option σ) {a b : σ} (h : f a = some b) :
    (flip Option.bind f)^[1] (some a) = some b := by
  rw [Function.iterate_one]; exact h

/-- Concatenation of iterate equalities. -/
theorem iterate_add' {σ : Type*} (f : σ → Option σ) {a b c : σ} {m1 m2 : ℕ}
    (h1 : (flip Option.bind f)^[m1] (some a) = some b)
    (h2 : (flip Option.bind f)^[m2] (some b) = some c) :
    (flip Option.bind f)^[m2 + m1] (some a) = some c := by
  rw [Function.iterate_add_apply, h1, h2]

/-- Phase A of the epilogue: from `labE1` with `L` on stack `Sum.inl 1`, in `L.length + 1` steps
the machine reaches `labE2` with `Sum.inl 1` emptied and `L.reverse` pushed onto `Sum.inl 2`. -/
theorem iter_epilogA (code : List Instr) (L : List Glyph) (v : MS code)
    (S : (j : KK) → List (Γ code j)) (h : S (Sum.inl 1) = L) :
    (flip Option.bind (TM2.step (mach code)))^[L.length + 1] (some ⟨some (labE1 code), v, S⟩)
      = some ⟨some (labE2 code), {v with dat := none}, updA code S L⟩ := by
  induction L generalizing v S with
  | nil =>
      have hn : code[(labE1 code : ℕ)]? = none := List.getElem?_eq_none (by simp [labE1])
      have hi : (labE1 code : ℕ) = code.length + 2 := rfl
      have hx : (S (Sum.inl 1)).head? = none := by rw [h]; rfl
      refine iterate_one_eq _ ?_
      rw [step_epilogA_none code (labE1 code) hn hi v S hx, updA_nil, h, List.tail_nil]
  | cons g L ih =>
      have hn : code[(labE1 code : ℕ)]? = none := List.getElem?_eq_none (by simp [labE1])
      have hi : (labE1 code : ℕ) = code.length + 2 := rfl
      have hx : (S (Sum.inl 1)).head? = some g := by rw [h]; rfl
      have h1 : (S (Sum.inl 1)).tail = L := by rw [h]; rfl
      have hS1 : (Function.update (Function.update S (Sum.inl 1) L) (Sum.inl 2)
          (g :: S (Sum.inl 2))) (Sum.inl 1) = L := by simp
      have hfirst : (flip Option.bind (TM2.step (mach code)))^[1] (some ⟨some (labE1 code), v, S⟩)
          = some ⟨some (labE1 code), {v with dat := some g},
              Function.update (Function.update S (Sum.inl 1) L) (Sum.inl 2)
                (g :: S (Sum.inl 2))⟩ :=
        iterate_one_eq _ (by rw [step_epilogA_some code (labE1 code) g hn hi v S hx, h1])
      have hrest := ih ({v with dat := some g})
        (Function.update (Function.update S (Sum.inl 1) L) (Sum.inl 2) (g :: S (Sum.inl 2))) hS1
      rw [updA_cons] at hrest
      exact iterate_add' _ hfirst hrest

/-- Phase B of the epilogue: from `labE2` with `L` on stack `Sum.inl 2`, in `L.length + 1` steps
the machine reaches `labH` with `Sum.inl 2` emptied, `L` moved to the output stack `Sum.inr 1` and
the machine state reset to `initMS`. -/
theorem iter_epilogB (code : List Instr) (L : List Glyph) (v : MS code)
    (S : (j : KK) → List (Γ code j)) (h : S (Sum.inl 2) = L) :
    (flip Option.bind (TM2.step (mach code)))^[L.length + 1] (some ⟨some (labE2 code), v, S⟩)
      = some ⟨some (labH code), initMS code, updB code S L⟩ := by
  induction L generalizing v S with
  | nil =>
      have hn : code[(labE2 code : ℕ)]? = none := List.getElem?_eq_none (by simp [labE2])
      have hi : (labE2 code : ℕ) = code.length + 3 := rfl
      have hx : (S (Sum.inl 2)).head? = none := by rw [h]; rfl
      refine iterate_one_eq _ ?_
      rw [step_epilogB_none code (labE2 code) hn hi v S hx, updB_nil, h, List.tail_nil]
  | cons g L ih =>
      have hn : code[(labE2 code : ℕ)]? = none := List.getElem?_eq_none (by simp [labE2])
      have hi : (labE2 code : ℕ) = code.length + 3 := rfl
      have hx : (S (Sum.inl 2)).head? = some g := by rw [h]; rfl
      have h1 : (S (Sum.inl 2)).tail = L := by rw [h]; rfl
      have hS1 : (Function.update (Function.update S (Sum.inl 2) L) (Sum.inr 1)
          (glyphToBool g :: S (Sum.inr 1))) (Sum.inl 2) = L := by simp
      have hfirst : (flip Option.bind (TM2.step (mach code)))^[1] (some ⟨some (labE2 code), v, S⟩)
          = some ⟨some (labE2 code), {v with dat := some g},
              Function.update (Function.update S (Sum.inl 2) L) (Sum.inr 1)
                (glyphToBool g :: S (Sum.inr 1))⟩ :=
        iterate_one_eq _ (by rw [step_epilogB_some code (labE2 code) g hn hi v S hx, h1])
      have hrest := ih ({v with dat := some g})
        (Function.update (Function.update S (Sum.inl 2) L) (Sum.inr 1)
          (glyphToBool g :: S (Sum.inr 1))) hS1
      rw [updB_cons] at hrest
      exact iterate_add' _ hfirst hrest

/-- The initial state on the empty input. -/
theorem initState_nil : (initState ([] : List InSym) : State) = ⟨fun _ => Glyph.eos, fun _ => []⟩ := by
  unfold initState
  congr 1
  funext k
  split_ifs <;> rfl

/-- The final stack vector of the epilogue is the one produced by `toStk` on the empty input state
and the output word. -/
theorem upd_final (code : List Instr) (out : List Bool) :
    updB code (updA code
        (toStk code ⟨fun _ => Glyph.eos,
          fun k : Fin 16 => if k = 1 then out.map Glyph.bit else []⟩ [] [] [])
        (out.map Glyph.bit)) (out.map Glyph.bit).reverse
      = toStk code (initState []) [] out [] := by
  rw [initState_nil]
  funext j
  rcases j with k | i
  · by_cases hk1 : k = 1
    · subst hk1; simp [updB, updA, toStk]
    · by_cases hk2 : k = 2
      · subst hk2; simp [updB, updA, toStk]
      · simp [updB, updA, toStk, hk1, hk2]
  · fin_cases i <;>
      simp [updB, updA, toStk, List.map_reverse, List.map_map, Function.comp_def, glyphToBool]

/-- The epilogue of the compiled machine: language stack `Sum.inl 1` holds `out.map Glyph.bit`
(first bit on top) and every other stack is empty; the machine moves it to the output stack
`Sum.inr 1` as a list of `Bool`s in the order of `out`, in `2 * out.length + 3` steps, resetting
the machine state to `initMS`.  (Two reversals: `Sum.inl 1 → Sum.inl 2 → Sum.inr 1`.) -/
theorem runs_epilogue (code : List Work.Compiler.Instr) (out : List Bool) (v : Work.Compiler.MS code) :
    Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step (Work.Compiler.mach code))
      ⟨some (Work.Compiler.labE1 code), v,
        Work.Compiler.toStk code ⟨fun _ => HvdH.Glyph.eos,
          (fun k : Fin 16 => if k = 1 then out.map HvdH.Glyph.bit else [])⟩ [] [] []⟩
      (some ⟨none, Work.Compiler.initMS code,
        Work.Compiler.toStk code (HvdH.initState []) [] out []⟩)
      (2 * out.length + 3)) := by
  refine ⟨⟨⟨2 * out.length + 3, ?_⟩, le_refl _⟩⟩
  have h1 : (toStk code ⟨fun _ => Glyph.eos,
      fun k : Fin 16 => if k = 1 then out.map Glyph.bit else []⟩ [] [] [])
      (Sum.inl 1) = out.map Glyph.bit := by simp [toStk]
  have hA := iter_epilogA code (out.map Glyph.bit) v
      (toStk code ⟨fun _ => Glyph.eos,
        fun k : Fin 16 => if k = 1 then out.map Glyph.bit else []⟩ [] [] []) h1
  have hmid : (updA code (toStk code ⟨fun _ => Glyph.eos,
      fun k : Fin 16 => if k = 1 then out.map Glyph.bit else []⟩ [] [] [])
      (out.map Glyph.bit)) (Sum.inl 2) = (out.map Glyph.bit).reverse := by
    simp [updA, toStk]
  have hB := iter_epilogB code (out.map Glyph.bit).reverse ({v with dat := none})
      (updA code (toStk code ⟨fun _ => Glyph.eos,
        fun k : Fin 16 => if k = 1 then out.map Glyph.bit else []⟩ [] [] [])
        (out.map Glyph.bit)) hmid
  have hcn : code[(labH code : ℕ)]? = none := List.getElem?_eq_none (by simp [labH])
  have h0 : (labH code : ℕ) ≠ code.length := by simp [labH]
  have h1' : (labH code : ℕ) ≠ code.length + 1 := by simp [labH]
  have h2' : (labH code : ℕ) ≠ code.length + 2 := by simp [labH]
  have h3' : (labH code : ℕ) ≠ code.length + 3 := by simp [labH]
  have hH : (flip Option.bind (TM2.step (mach code)))^[1]
      (some ⟨some (labH code), initMS code,
        updB code (updA code (toStk code ⟨fun _ => Glyph.eos,
          fun k : Fin 16 => if k = 1 then out.map Glyph.bit else []⟩ [] [] [])
          (out.map Glyph.bit)) (out.map Glyph.bit).reverse⟩)
      = some ⟨none, initMS code,
        updB code (updA code (toStk code ⟨fun _ => Glyph.eos,
          fun k : Fin 16 => if k = 1 then out.map Glyph.bit else []⟩ [] [] [])
          (out.map Glyph.bit)) (out.map Glyph.bit).reverse⟩ :=
    iterate_one_eq _ (by rw [step_halt code (labH code) hcn h0 h1' h2' h3'])
  have hAB := iterate_add' _ hA hB
  have hABH := iterate_add' _ hAB hH
  rw [upd_final] at hABH
  have hexp : 1 + (((out.map Glyph.bit).reverse.length + 1)
      + ((out.map Glyph.bit).length + 1)) = 2 * out.length + 3 := by
    simp [List.length_map, List.length_reverse]
    ring
  rw [hexp] at hABH
  exact hABH

end Work.Compiler
