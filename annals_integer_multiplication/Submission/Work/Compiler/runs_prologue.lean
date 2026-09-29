import Mathlib
import Submission.Work.Compiler.Steps

/-!
# The prologue of the compiled machine

We prove that the prologue of the compiled machine (`Work.Compiler.mach`) moves the input word from
the input stack `Sum.inr 0` to language stack `Sum.inl 0`, preserving the order, in `2 * |w| + 2`
steps, and returns the machine to its initial state.

The prologue has two phases:
* phase A (`labA`): pop from the input stack and push onto language stack `1` (reversing the word);
* phase B (`labB`): pop from language stack `1` and push onto language stack `0` (reversing again).

Each phase takes `|w| + 1` steps (one step per letter plus one step that discovers the stack is
empty), whence the bound.
-/

set_option autoImplicit false

namespace Work.Compiler

open HvdH Turing

/-! ## Update algebra -/

/-- Updating a (dependent) function at `a`, then at `b`, then at `a` again, then at `b` again is the
same as updating at `a` and then at `b`: the later updates win. -/
theorem update_normal (code : List Instr) (S : (j : KK) → List (Γ code j)) (a b : KK) (h : a ≠ b)
    (A R : List (Γ code a)) (L G : List (Γ code b)) :
    Function.update (Function.update (Function.update (Function.update S a A) b L) a R) b G
      = Function.update (Function.update S a R) b G := by
  funext j
  by_cases h1 : j = a
  · subst h1
    simp [Function.update_of_ne h]
  · by_cases h2 : j = b
    · subst h2
      simp
    · simp [Function.update_of_ne h1, Function.update_of_ne h2]

/-! ## One-step lemmas in normal form

The step lemmas of `Submission/Work/Compiler/Steps.lean` are stated in terms of arbitrary stack
functions.  For the induction it is convenient to have them in the "normal form" where the two
stacks that the phase touches are the outermost updates.
-/

/-- Phase A, empty input: one step leads to phase B. -/
theorem step_prologA_nil (code : List Instr) (S : (j : KK) → List (Γ code j)) (l : List Glyph)
    (v : MS code) :
    TM2.step (mach code) ⟨some (labA code), v,
        Function.update (Function.update S (Sum.inr 0) []) (Sum.inl 1) l⟩
      = some ⟨some (labB code), {v with sym := none},
          Function.update (Function.update S (Sum.inr 0) []) (Sum.inl 1) l⟩ := by
  have hx : ((Function.update (Function.update S (Sum.inr 0) []) (Sum.inl 1) l) (Sum.inr 0)).head? = none := by
    simp
  rw [step_prologA_none code (labA code) (List.getElem?_length code) rfl v _ hx]
  have hS : (Function.update (Function.update S (Sum.inr 0) []) (Sum.inl 1) l) (Sum.inr 0) = [] := by
    simp
  refine congrArg (fun S' => (some ⟨some (labB code), {v with sym := none}, S'⟩ :
      Option (TM2.Cfg (Γ code) (Λ code) (MS code)))) ?_
  rw [Function.update_eq_iff]
  refine ⟨?_, fun x _ => rfl⟩
  rw [hS]
  rfl

/-- Phase A, nonempty input: one step moves one letter. -/
theorem step_prologA_cons (code : List Instr) (x : InSym) (rest : List InSym)
    (S : (j : KK) → List (Γ code j)) (l : List Glyph) (v : MS code) :
    TM2.step (mach code) ⟨some (labA code), v,
        Function.update (Function.update S (Sum.inr 0) (x :: rest)) (Sum.inl 1) l⟩
      = some ⟨some (labA code), {v with sym := some x},
          Function.update (Function.update S (Sum.inr 0) rest) (Sum.inl 1) (inpGlyph x :: l)⟩ := by
  have hx : ((Function.update (Function.update S (Sum.inr 0) (x :: rest)) (Sum.inl 1) l) (Sum.inr 0)).head?
      = some x := by simp
  rw [step_prologA_some code (labA code) x (List.getElem?_length code) rfl v _ hx]
  have htail : (Function.update (Function.update S (Sum.inr 0) (x :: rest)) (Sum.inl 1) l) (Sum.inr 0)
      = x :: rest := by simp
  have hl : (Function.update (Function.update S (Sum.inr 0) (x :: rest)) (Sum.inl 1) l) (Sum.inl 1) = l := by
    simp
  rw [htail, hl, List.tail_cons]
  exact congrArg (fun S' => (some ⟨some (labA code), {v with sym := some x}, S'⟩ :
      Option (TM2.Cfg (Γ code) (Λ code) (MS code))))
    (update_normal code S (Sum.inr 0) (Sum.inl 1) (by decide) (x :: rest) rest l (inpGlyph x :: l))

/-- Phase B, empty stack: one step leads to the first instruction. -/
theorem step_prologB_nil (code : List Instr) (S : (j : KK) → List (Γ code j)) (acc : List Glyph)
    (v : MS code) :
    TM2.step (mach code) ⟨some (labB code), v,
        Function.update (Function.update S (Sum.inl 1) []) (Sum.inl 0) acc⟩
      = some ⟨some (lab code 0), {v with dat := none},
          Function.update (Function.update S (Sum.inl 1) []) (Sum.inl 0) acc⟩ := by
  have hx : ((Function.update (Function.update S (Sum.inl 1) []) (Sum.inl 0) acc) (Sum.inl 1)).head? = none := by
    simp
  rw [step_prologB_none code (labB code) (List.getElem?_eq_none (Nat.le_add_right _ 1)) rfl v _ hx]
  have hS : (Function.update (Function.update S (Sum.inl 1) []) (Sum.inl 0) acc) (Sum.inl 1) = [] := by
    simp
  refine congrArg (fun S' => (some ⟨some (lab code 0), {v with dat := none}, S'⟩ :
      Option (TM2.Cfg (Γ code) (Λ code) (MS code)))) ?_
  rw [Function.update_eq_iff]
  refine ⟨?_, fun x _ => rfl⟩
  rw [hS]
  rfl

/-- Phase B, nonempty stack: one step moves one glyph. -/
theorem step_prologB_cons (code : List Instr) (g : Glyph) (rest : List Glyph)
    (S : (j : KK) → List (Γ code j)) (acc : List Glyph) (v : MS code) :
    TM2.step (mach code) ⟨some (labB code), v,
        Function.update (Function.update S (Sum.inl 1) (g :: rest)) (Sum.inl 0) acc⟩
      = some ⟨some (labB code), {v with dat := some g},
          Function.update (Function.update S (Sum.inl 1) rest) (Sum.inl 0) (g :: acc)⟩ := by
  have hx : ((Function.update (Function.update S (Sum.inl 1) (g :: rest)) (Sum.inl 0) acc) (Sum.inl 1)).head?
      = some g := by simp
  rw [step_prologB_some code (labB code) g (List.getElem?_eq_none (Nat.le_add_right _ 1)) rfl v _ hx]
  have htail : (Function.update (Function.update S (Sum.inl 1) (g :: rest)) (Sum.inl 0) acc) (Sum.inl 1)
      = g :: rest := by simp
  have hl : (Function.update (Function.update S (Sum.inl 1) (g :: rest)) (Sum.inl 0) acc) (Sum.inl 0) = acc := by
    simp
  rw [htail, hl, List.tail_cons]
  exact congrArg (fun S' => (some ⟨some (labB code), {v with dat := some g}, S'⟩ :
      Option (TM2.Cfg (Γ code) (Λ code) (MS code))))
    (update_normal code S (Sum.inl 1) (Sum.inl 0) (by decide) (g :: rest) rest acc (g :: acc))

/-! ## The two phases -/

/-- **Phase A.**  From `labA` with input word `w` on the input stack and `l` on language stack `1`,
`|w| + 1` steps bring the machine to `labB`, with the reversed word (`w.map inpGlyph`, reversed)
pushed onto language stack `1` and the input stack emptied. -/
def runs_prologA (code : List Instr) (w : List InSym) (S : (j : KK) → List (Γ code j))
    (l : List Glyph) (v : MS code) :
    StateTransition.EvalsToInTime (TM2.step (mach code))
      ⟨some (labA code), v, Function.update (Function.update S (Sum.inr 0) w) (Sum.inl 1) l⟩
      (some ⟨some (labB code), {v with sym := none},
        Function.update (Function.update S (Sum.inr 0) []) (Sum.inl 1) ((w.map inpGlyph).reverse ++ l)⟩)
      (w.length + 1) := by
  induction w generalizing S l v with
  | nil =>
      exact ⟨⟨1, by rw [Function.iterate_one]; exact step_prologA_nil code S l v⟩, by simp⟩
  | cons x rest ih =>
      have h₁ : StateTransition.EvalsToInTime (TM2.step (mach code))
          ⟨some (labA code), v, Function.update (Function.update S (Sum.inr 0) (x :: rest)) (Sum.inl 1) l⟩
          (some ⟨some (labA code), {v with sym := some x},
            Function.update (Function.update S (Sum.inr 0) rest) (Sum.inl 1) (inpGlyph x :: l)⟩) 1 :=
        ⟨⟨1, by rw [Function.iterate_one]; exact step_prologA_cons code x rest S l v⟩, le_rfl⟩
      have h₂ : StateTransition.EvalsToInTime (TM2.step (mach code))
          ⟨some (labA code), {v with sym := some x},
            Function.update (Function.update S (Sum.inr 0) rest) (Sum.inl 1) (inpGlyph x :: l)⟩
          (some ⟨some (labB code), {v with sym := none},
            Function.update (Function.update S (Sum.inr 0) [])
              (Sum.inl 1) (((x :: rest).map inpGlyph).reverse ++ l)⟩)
          (rest.length + 1) := by
        simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
          using ih S (inpGlyph x :: l) {v with sym := some x}
      exact Work.Compiler.EvalsToInTime.mono'
        (StateTransition.EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ h₁ h₂) (by simp)

/-- **Phase B.**  From `labB` with the word `l` on language stack `1` and `acc` on language stack
`0`, `|l| + 1` steps bring the machine to the first instruction of the program, with the reversed
word pushed onto language stack `0`. -/
def runs_prologB (code : List Instr) (l : List Glyph) (acc : List Glyph)
    (S : (j : KK) → List (Γ code j)) (v : MS code) :
    StateTransition.EvalsToInTime (TM2.step (mach code))
      ⟨some (labB code), v, Function.update (Function.update S (Sum.inl 1) l) (Sum.inl 0) acc⟩
      (some ⟨some (lab code 0), {v with dat := none},
        Function.update (Function.update S (Sum.inl 1) []) (Sum.inl 0) (l.reverse ++ acc)⟩)
      (l.length + 1) := by
  induction l generalizing S acc v with
  | nil =>
      exact ⟨⟨1, by rw [Function.iterate_one]; exact step_prologB_nil code S acc v⟩, by simp⟩
  | cons g rest ih =>
      have h₁ : StateTransition.EvalsToInTime (TM2.step (mach code))
          ⟨some (labB code), v, Function.update (Function.update S (Sum.inl 1) (g :: rest)) (Sum.inl 0) acc⟩
          (some ⟨some (labB code), {v with dat := some g},
            Function.update (Function.update S (Sum.inl 1) rest) (Sum.inl 0) (g :: acc)⟩) 1 :=
        ⟨⟨1, by rw [Function.iterate_one]; exact step_prologB_cons code g rest S acc v⟩, le_rfl⟩
      have h₂ : StateTransition.EvalsToInTime (TM2.step (mach code))
          ⟨some (labB code), {v with dat := some g},
            Function.update (Function.update S (Sum.inl 1) rest) (Sum.inl 0) (g :: acc)⟩
          (some ⟨some (lab code 0), {v with dat := none},
            Function.update (Function.update S (Sum.inl 1) [])
              (Sum.inl 0) (((g :: rest).reverse) ++ acc)⟩)
          (rest.length + 1) := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append]
          using ih (g :: acc) S {v with dat := some g}
      exact Work.Compiler.EvalsToInTime.mono'
        (StateTransition.EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ h₁ h₂) (by simp)

/-! ## Bookkeeping for `toStk` -/

/-- Restricting `toStk` to the input stack. -/
theorem toStk_inr0 (code : List Instr) (s : State) (X : List InSym) (L0 : List InSym)
    (L1 : List Bool) (rs : List (Λ code)) :
    toStk code s X L1 rs = Function.update (toStk code s L0 L1 rs) (Sum.inr 0) X := by
  funext j
  cases j with
  | inl k => simp [toStk, Function.update_of_ne (show (Sum.inl k : KK) ≠ Sum.inr 0 by simp)]
  | inr b => fin_cases b <;> simp [toStk]

/-- Updating language stack `k` of the StackLang state updates the `Sum.inl k` component of `toStk`. -/
theorem toStk_inl (code : List Instr) (s : State) (k0 : Stk) (X : List Glyph) (L0 : List InSym)
    (L1 : List Bool) (rs : List (Λ code)) :
    toStk code ⟨s.reg, Function.update s.stk k0 X⟩ L0 L1 rs
      = Function.update (toStk code s L0 L1 rs) (Sum.inl k0) X := by
  funext j
  cases j with
  | inl k =>
      by_cases hk : k = k0
      · subst hk
        simp [toStk]
      · simp [toStk, Function.update_apply, Function.update_of_ne
          (show (Sum.inl k : KK) ≠ Sum.inl k0 by simp [hk]), hk]
  | inr b => fin_cases b <;> simp [toStk]

/-- The initial StackLang state of word `w` is the empty one with stack `0` set to `w.map inpGlyph`. -/
theorem initState_eq (w : List InSym) :
    initState w = ⟨(initState []).reg, Function.update (initState []).stk 0 (w.map inpGlyph)⟩ := by
  have hstk : (initState w).stk = Function.update (initState []).stk 0 (w.map inpGlyph) := by
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [HvdH.initState, Function.update_apply]
    · simp [HvdH.initState, Function.update_apply, hk]
  have hreg : (initState w).reg = (initState []).reg := rfl
  rw [← hstk, ← hreg]

/-- All language stacks of the empty `toStk` state are empty. -/
theorem zeroStk_inl (code : List Instr) (k : Stk) :
    (toStk code (initState []) [] [] []) (Sum.inl k) = [] := by
  simp [toStk, HvdH.initState]

/-! ## The prologue -/

/-- The prologue of the compiled machine moves the input word from the input stack `Sum.inr 0`
to language stack `Sum.inl 0` (preserving the order, first letter stays on top), in
`2 * w.length + 2` steps, returning the machine to its initial state. -/
theorem runs_prologue (code : List Work.Compiler.Instr) (w : List HvdH.InSym) :
    Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step (Work.Compiler.mach code))
      ⟨some (Work.Compiler.labA code), Work.Compiler.initMS code,
        Work.Compiler.toStk code (HvdH.initState []) w [] []⟩
      (some ⟨some (Work.Compiler.lab code 0), Work.Compiler.initMS code,
        Work.Compiler.toStk code (HvdH.initState w) [] [] []⟩)
      (2 * w.length + 2)) := by
  refine ⟨?_⟩
  have hstart : toStk code (initState []) w [] [] =
      Function.update (Function.update (toStk code (initState []) [] [] []) (Sum.inr 0) w)
        (Sum.inl 1) [] := by
    rw [toStk_inr0 code (initState []) w [] [] []]
    have h1 : Function.update (toStk code (initState []) [] [] []) (Sum.inl 1) [] =
        toStk code (initState []) [] [] [] := by
      rw [← zeroStk_inl code 1]
      exact Function.update_eq_self (Sum.inl 1) (toStk code (initState []) [] [] [])
    symm
    rw [Function.update_comm (α := KK) (β := fun j => List (Γ code j))
      (show (Sum.inr 0 : KK) ≠ Sum.inl 1 by decide), h1]
  have hmid : Function.update (Function.update (toStk code (initState []) [] [] []) (Sum.inr 0) [])
        (Sum.inl 1) ((w.map inpGlyph).reverse ++ []) =
      Function.update (Function.update (toStk code (initState []) [] [] []) (Sum.inl 1)
        ((w.map inpGlyph).reverse)) (Sum.inl 0) [] := by
    have hS0 : (toStk code (initState []) [] [] []) (Sum.inr 0) = [] := rfl
    have h0 : Function.update (toStk code (initState []) [] [] []) (Sum.inr 0) [] =
        toStk code (initState []) [] [] [] := by
      rw [← hS0]
      exact Function.update_eq_self (Sum.inr 0) (toStk code (initState []) [] [] [])
    have h0' : Function.update (toStk code (initState []) [] [] []) (Sum.inl 0) [] =
        toStk code (initState []) [] [] [] := by
      rw [← zeroStk_inl code 0]
      exact Function.update_eq_self (Sum.inl 0) (toStk code (initState []) [] [] [])
    rw [List.append_nil, h0]
    rw [Function.update_comm (α := KK) (β := fun j => List (Γ code j))
      (show (Sum.inl 1 : KK) ≠ Sum.inl 0 by decide), h0']
  have hfin : Function.update (Function.update (toStk code (initState []) [] [] []) (Sum.inl 1) [])
        (Sum.inl 0) (((w.map inpGlyph).reverse).reverse ++ []) =
      toStk code (initState w) [] [] [] := by
    have h1 : Function.update (toStk code (initState []) [] [] []) (Sum.inl 1) [] =
        toStk code (initState []) [] [] [] := by
      rw [← zeroStk_inl code 1]
      exact Function.update_eq_self (Sum.inl 1) (toStk code (initState []) [] [] [])
    rw [h1, List.reverse_reverse, List.append_nil]
    rw [← toStk_inl code (initState []) 0 (w.map inpGlyph) [] [] []]
    rw [initState_eq w]
  have hMS1 : ({initMS code with sym := none} : MS code) = initMS code := rfl
  have hMS2 : ({{initMS code with sym := none} with dat := none} : MS code) = initMS code := rfl
  have hA : StateTransition.EvalsToInTime (TM2.step (mach code))
      ⟨some (labA code), initMS code, toStk code (initState []) w [] []⟩
      (some ⟨some (labB code), {initMS code with sym := none},
        Function.update (Function.update (toStk code (initState []) [] [] []) (Sum.inl 1)
          ((w.map inpGlyph).reverse)) (Sum.inl 0) []⟩)
      (w.length + 1) := by
    simpa only [hstart.symm, hmid] using
      runs_prologA code w (toStk code (initState []) [] [] []) [] (initMS code)
  have hB : StateTransition.EvalsToInTime (TM2.step (mach code))
      ⟨some (labB code), {initMS code with sym := none},
        Function.update (Function.update (toStk code (initState []) [] [] []) (Sum.inl 1)
          ((w.map inpGlyph).reverse)) (Sum.inl 0) []⟩
      (some ⟨some (lab code 0), initMS code,
        toStk code (initState w) [] [] []⟩)
      (w.length + 1) := by
    simpa only [hfin, List.length_reverse, List.length_map, hMS1, hMS2] using
      runs_prologB code ((w.map inpGlyph).reverse) [] (toStk code (initState []) [] [] [])
        {initMS code with sym := none}
  exact Work.Compiler.EvalsToInTime.mono'
    (StateTransition.EvalsToInTime.trans (TM2.step (mach code))
      (w.length + 1) (w.length + 1) _ _ _ hA hB) (by omega)

end Work.Compiler
