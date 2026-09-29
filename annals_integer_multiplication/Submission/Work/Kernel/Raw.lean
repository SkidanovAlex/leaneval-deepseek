import Mathlib
import Submission.HvdH.Interfaces

/-!
# Kernel: raw `Eval`/`WordR` toolkit

Stable shared foundation for the Kernel library area and, more generally, for every area that
builds StackLang programs (`Submission/HvdH/Interfaces.lean`, L1/L2).

What it provides:

* `HvdH.State.updStk` / `HvdH.State.updReg` and `simp` lemmas, to write and normalise states;
* `State.tPush`, `State.tPop`, `State.tPeek`, `State.tSet`, `State.tMov`: the *canonical* result
  states of the primitive commands (definitionally equal to the states produced by `Eval.*`), so
  that a straight-line program is proved by a chain of `Eval.seq` applications;
* `eval_loop_iterate`: unrolling of `Cmd.loop` along an explicit sequence of states;
* `pushGlyphs` (+ its state and cost functions): pushing a literal list of glyphs onto a stack,
  the building block of every "push a constant value" word;
* the four easy laws of `HvdH.KernelLib` (`seq`, `conseq`, `skip`, `selfLaw`);
* `kernelLib_pushVal`: a worked example of the `WordR` assembly pattern.

Everything is `sorry`-free.  Conventions:
* programs are built with `foldr`/`foldl` so that `simp`/`rfl` unfold one step at a time;
* each program `p` comes with a state function `pState : ... → State → State` and an `Eval` lemma
  `eval_p : ∀ s, Eval main p s (pState ... s) (pCost ...)`;
* facts about `pState` are proved separately (typically by induction, using the `simp` lemmas
  below) and the `WordR` statement is then assembled by hand.
-/

set_option autoImplicit false

namespace HvdH

namespace State

/-- `s.updStk k l` is `s` with the content of stack `k` replaced by `l` (head = top of stack). -/
def updStk (s : State) (k : Stk) (l : List Glyph) : State := ⟨s.reg, Function.update s.stk k l⟩

/-- `s.updReg r g` is `s` with register `r` set to `g`. -/
def updReg (s : State) (r : Reg) (g : Glyph) : State := ⟨Function.update s.reg r g, s.stk⟩

@[simp] theorem updStk_reg (s : State) (k : Stk) (l : List Glyph) : (s.updStk k l).reg = s.reg := rfl

@[simp] theorem updStk_apply (s : State) (k k' : Stk) (l : List Glyph) :
    (s.updStk k l).stk k' = if k' = k then l else s.stk k' := Function.update_apply s.stk k l k'

@[simp] theorem updStk_same (s : State) (k : Stk) (l : List Glyph) : (s.updStk k l).stk k = l := by
  rw [updStk_apply]; simp

@[simp] theorem updStk_ne (s : State) {k k' : Stk} (l : List Glyph) (h : k' ≠ k) :
    (s.updStk k l).stk k' = s.stk k' := by rw [updStk_apply]; simp [h]

@[simp] theorem updStk_updStk (s : State) (k : Stk) (l l' : List Glyph) :
    (s.updStk k l).updStk k l' = s.updStk k l' := by
  cases s with | mk reg stk => simp [updStk, Function.update_idem]

@[simp] theorem updStk_self (s : State) (k : Stk) : s.updStk k (s.stk k) = s := by
  cases s with | mk reg stk => simp [updStk, Function.update_eq_self]

@[simp] theorem updReg_apply (s : State) (r r' : Reg) (g : Glyph) :
    (s.updReg r g).reg r' = if r' = r then g else s.reg r' := Function.update_apply s.reg r g r'

@[simp] theorem updReg_stk (s : State) (r : Reg) (g : Glyph) : (s.updReg r g).stk = s.stk := rfl

@[simp] theorem updReg_updReg (s : State) (r : Reg) (g g' : Glyph) :
    (s.updReg r g).updReg r g' = s.updReg r g' := by
  cases s with | mk reg stk => simp [updReg, Function.update_idem]

@[simp] theorem updReg_self (s : State) (r : Reg) : s.updReg r (s.reg r) = s := by
  cases s with | mk reg stk => simp [updReg, Function.update_eq_self]

@[simp] theorem updStk_updReg (s : State) (k : Stk) (r : Reg) (l : List Glyph) (g : Glyph) :
    (s.updStk k l).updReg r g = (s.updReg r g).updStk k l := by
  cases s with | mk reg stk => simp [updStk, updReg]

/-- Canonical result state of `Cmd.push k r`. -/
def tPush (s : State) (k : Stk) (r : Reg) : State := s.updStk k (s.reg r :: s.stk k)

/-- Canonical result state of `Cmd.pop k r`. -/
def tPop (s : State) (k : Stk) (r : Reg) : State :=
  (s.updStk k (s.stk k).tail).updReg r ((s.stk k).headD .eos)

/-- Canonical result state of `Cmd.peek k r`. -/
def tPeek (s : State) (k : Stk) (r : Reg) : State := s.updReg r ((s.stk k).headD .eos)

/-- Canonical result state of `Cmd.set r g`. -/
def tSet (s : State) (r : Reg) (g : Glyph) : State := s.updReg r g

/-- Canonical result state of `Cmd.mov dst src`. -/
def tMov (s : State) (dst src : Reg) : State := s.updReg dst (s.reg src)

end State

end HvdH

namespace Work.Kernel

open HvdH

/-- Sequencing notation for `HvdH.Cmd`. -/
scoped infixr:68 " ;;" => HvdH.Cmd.seq

/-! ## Primitive steps -/

theorem eval_skip (main : Cmd) (s : State) : Eval main .skip s s 1 := Eval.skip s

theorem eval_push (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Eval main (.push k r) s (State.tPush s k r) 1 := Eval.push k r s

theorem eval_pop (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Eval main (.pop k r) s (State.tPop s k r) 1 := Eval.pop k r s

theorem eval_peek (main : Cmd) (k : Stk) (r : Reg) (s : State) :
    Eval main (.peek k r) s (State.tPeek s k r) 1 := Eval.peek k r s

theorem eval_set (main : Cmd) (r : Reg) (g : Glyph) (s : State) :
    Eval main (.set r g) s (State.tSet s r g) 1 := Eval.set r g s

theorem eval_mov (main : Cmd) (dst src : Reg) (s : State) :
    Eval main (.mov dst src) s (State.tMov s dst src) 1 := Eval.mov dst src s

theorem eval_seq {main : Cmd} {c₁ c₂ : Cmd} {s₁ s₂ s₃ : State} {n₁ n₂ : ℕ}
    (h₁ : Eval main c₁ s₁ s₂ n₁) (h₂ : Eval main c₂ s₂ s₃ n₂) :
    Eval main (c₁ ;; c₂) s₁ s₃ (n₁ + n₂) := Eval.seq h₁ h₂

theorem eval_iteT {main : Cmd} {r : Reg} {c : Glyph} {c₁ c₂ : Cmd} {s s' : State} {n : ℕ}
    (h : s.reg r = c) (h₁ : Eval main c₁ s s' n) :
    Eval main (.ite r c c₁ c₂) s s' (n + 1) := Eval.iteT h h₁

theorem eval_iteF {main : Cmd} {r : Reg} {c : Glyph} {c₁ c₂ : Cmd} {s s' : State} {n : ℕ}
    (h : s.reg r ≠ c) (h₂ : Eval main c₂ s s' n) :
    Eval main (.ite r c c₁ c₂) s s' (n + 1) := Eval.iteF h h₂

theorem eval_loopF {main : Cmd} {r : Reg} {c : Glyph} {body : Cmd} {s : State} (h : s.reg r ≠ c) :
    Eval main (.loop r c body) s s 1 := Eval.loopF h

/-- `Cmd.loop` unrolled along an explicit sequence of states: if each of the `n` steps takes one
`body` run of cost `c` from `f i` to `f (i+1)` while the test register still holds `cc`, and the
test fails at `f n`, then the loop reaches `f n` at cost `n * (c+1) + 1`. -/
theorem eval_loop_iterate (main : Cmd) (r : Reg) (cc : Glyph) (body : Cmd) (c : ℕ) :
    ∀ (n : ℕ) (f : ℕ → State),
      (∀ i < n, (f i).reg r = cc ∧ Eval main body (f i) (f (i + 1)) c) →
      (f n).reg r ≠ cc →
      Eval main (.loop r cc body) (f 0) (f n) (n * (c + 1) + 1) := by
  intro n
  induction n with
  | zero => intro f _ hstop; simpa using Eval.loopF (main := main) (s := f 0) hstop
  | succ n ih =>
    intro f hstep hstop
    have h0 := hstep 0 (Nat.zero_lt_succ n)
    have hrest : Eval main (.loop r cc body) (f 1) (f (n + 1)) (n * (c + 1) + 1) :=
      ih (fun i => f (i + 1)) (by intro i hi; exact hstep (i + 1) (by omega)) hstop
    have hT := Eval.loopT (main := main) h0.1 h0.2 hrest
    have hc : c + (n * (c + 1) + 1) + 1 = (n + 1) * (c + 1) + 1 := by ring
    rw [hc] at hT
    exact hT

/-! ## Pushing a literal list of glyphs -/

/-- `pushGlyphs l k r` pushes the glyphs of `l` onto stack `k`, first element first: the top of
stack `k` after the run is `l.reverse`.  Register `r` is used as a scratch. -/
def pushGlyphs (l : List Glyph) (k : Stk) (r : Reg) : Cmd :=
  l.foldr (fun g c => Cmd.set r g ;; Cmd.push k r ;; c) Cmd.skip

/-- Result state of `pushGlyphs l k r` from state `s`. -/
def pushGlyphsState (l : List Glyph) (k : Stk) (r : Reg) (s : State) : State :=
  l.foldl (fun s g => State.tPush (State.tSet s r g) k r) s

/-- Cost of `pushGlyphs`. -/
def pushGlyphsCost : List Glyph → ℕ
  | [] => 1
  | _ :: t => 1 + (1 + pushGlyphsCost t)

theorem pushGlyphsState_cons (g : Glyph) (t : List Glyph) (k : Stk) (r : Reg) (s : State) :
    pushGlyphsState (g :: t) k r s = pushGlyphsState t k r (State.tPush (State.tSet s r g) k r) :=
  rfl

theorem eval_pushGlyphs (main : Cmd) (l : List Glyph) (k : Stk) (r : Reg) :
    ∀ s : State, Eval main (pushGlyphs l k r) s (pushGlyphsState l k r s) (pushGlyphsCost l) := by
  intro s
  induction l generalizing s with
  | nil => exact Eval.skip s
  | cons g t ih =>
    have h2 : Eval main (.push k r) (State.tSet s r g) (State.tPush (State.tSet s r g) k r) 1 :=
      Eval.push k r _
    exact Eval.seq (Eval.set r g s) (Eval.seq h2 (ih _))

/-- Content of the stack `k` after `pushGlyphs`. -/
theorem pushGlyphsState_stk (l : List Glyph) (k : Stk) (r : Reg) (s : State) (j : Stk) :
    (pushGlyphsState l k r s).stk j =
      if j = k then l.reverse ++ s.stk j else s.stk j := by
  induction l generalizing s with
  | nil => simp [pushGlyphsState]
  | cons g t ih =>
    rw [pushGlyphsState_cons, ih]
    by_cases h : j = k
    · subst h
      simp [State.tPush, State.tSet, State.updStk, State.updReg, List.reverse_cons,
        List.append_assoc]
    · simp [State.tPush, State.tSet, State.updStk, State.updReg, h]

/-- Stacks other than `k` are untouched by `pushGlyphs`. -/
theorem pushGlyphsState_stk_ne (l : List Glyph) (k : Stk) (r : Reg) (s : State) {j : Stk}
    (h : j ≠ k) : (pushGlyphsState l k r s).stk j = s.stk j := by
  rw [pushGlyphsState_stk]; simp [h]

theorem pushGlyphsCost_eq (l : List Glyph) : pushGlyphsCost l = 2 * l.length + 1 := by
  induction l with
  | nil => simp [pushGlyphsCost]
  | cons g t ih => simp [pushGlyphsCost, ih]; ring

theorem pushGlyphsCost_le (l : List Glyph) : pushGlyphsCost l ≤ 2 * (l.length + 1) := by
  rw [pushGlyphsCost_eq]; omega

/-! ## The easy laws of `KernelLib` -/

theorem WordR_seq {main p q : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {P' : List Val → Prop} {Q' : List Val → List Val → Prop}
    {C' B : List Val → ℕ} (hp : WordR main p P Q C) (hq : WordR main q P' Q' C')
    (hmid : ∀ vs mid, P vs → Q vs mid → P' mid ∧ C' mid ≤ B vs) :
    WordR main (.seq p q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out) (fun vs => C vs + B vs) := by
  intro vs hP s R hR
  obtain ⟨mid, s₂, n₁, hQ, he₁, hn₁, hstk₁, hoth₁⟩ := hp vs hP s R hR
  obtain ⟨hP', hC'm⟩ := hmid vs mid hP hQ
  obtain ⟨out, s₃, n₂, hQ', he₂, hn₂, hstk₂, hoth₂⟩ := hq mid hP' s₂ R hstk₁
  exact ⟨out, s₃, n₁ + n₂, ⟨mid, hQ, hQ'⟩, Eval.seq he₁ he₂,
    Nat.add_le_add hn₁ (le_trans hn₂ hC'm), hstk₂,
    fun k hk => by rw [hoth₂ k hk, hoth₁ k hk]⟩

theorem WordR_conseq {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hP' s R hR
  obtain ⟨out, s', n, hQh, he, hn, hstk, hoth⟩ := h vs (hP vs hP') s R hR
  exact ⟨out, s', n, hQ vs out hP' hQh, he, le_trans hn (hC vs hP'), hstk, hoth⟩

theorem WordR_skip (main : Cmd) :
    WordR main .skip (fun _ => True) (fun vs out => out = vs) (fun _ => 1) := by
  intro vs _ s R hR
  exact ⟨vs, s, 1, rfl, Eval.skip s, le_refl 1, hR, fun k _ => rfl⟩

theorem WordR_self {main : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} (h : WordR main main P Q C) : WordR main .self P Q (fun vs => C vs + 1) := by
  intro vs hP s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := h vs hP s R hR
  exact ⟨out, s', n + 1, hQ, Eval.self he, Nat.add_le_add_right hn 1, hstk, hoth⟩

/-! ## Value encodings -/

theorem encs_cons (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := rfl

theorem encs_nil : encs ([] : List Val) = [] := rfl

theorem encs_append (vs ws : List Val) : encs (vs ++ ws) = encs vs ++ encs ws := by
  simp [encs]

/-! ## Worked example: `pushVal` -/

/-- Push the constant value `v` on top of the value stack. -/
def pushValProg (v : Val) : Cmd := pushGlyphs v.enc.reverse 0 0

theorem pushValProg_stk (v : Val) (s : State) :
    (pushGlyphsState v.enc.reverse 0 0 s).stk 0 =
      v.enc ++ s.stk 0 := by
  rw [pushGlyphsState_stk]
  simp

theorem kernelLib_pushVal : ∃ (prog : Val → Cmd) (K : ℕ), ∀ (main : Cmd) (v : Val),
    WordR main (prog v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => K * (vsz v + 1)) := by
  refine ⟨pushValProg, 2, ?_⟩
  intro main v vs _ s R hR
  refine ⟨v :: vs, pushGlyphsState v.enc.reverse 0 0 s, pushGlyphsCost v.enc.reverse, rfl, ?_, ?_, ?_, ?_⟩
  · exact eval_pushGlyphs main v.enc.reverse 0 0 s
  · rw [pushGlyphsCost_eq]; simp only [List.length_reverse, vsz]; omega
  · rw [pushValProg_stk, hR, encs_cons]; simp only [List.append_assoc]
  · intro k hk
    exact pushGlyphsState_stk_ne _ _ _ _ hk

end Work.Kernel
