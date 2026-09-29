import Mathlib
import Submission.HvdH.Interfaces

/-!
# `IntLib` / shift words: raw toolkit

A small self-contained `Ev`-style toolkit for writing StackLang programs and proving their
`Eval` specifications, plus the four standard *region* procedures `drain` (move a marked region
onto another stack, reversed), `drainPop` (same, then pop the marker), `clearRgn` (discard a
marked region) and `clearAll` (discard it and the marker).

Regions are delimited by a *frame marker* `gmk k = Glyph.mk k`, distinct from the data glyphs of a
`Val` encoding: a stack `k` carries arbitrary junk below, our data strictly above `Glyph.mk k`.
For the concrete stacks used here (`1`–`7`) the markers are `.mk 1`–`.mk 7`, while the flag glyphs
are `.mk 8`–`.mk 13`, so they never collide (`by decide` proves the concrete instances).

Specifications of region procedures are *componentwise*: the program reaches some state `s'` with
`Eval main p ⟨g, X⟩ s' n`, `n ≤ C`, the relevant stacks given by explicit lists, and all other
stacks unchanged.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace Shift

open HvdH

/-! ## Flags and markers -/

/-- loop-continue flag -/
def gGo : Glyph := .mk 8
/-- loop-stop flag -/
def gStop : Glyph := .mk 9

theorem gGo_ne_gStop : gGo ≠ gStop := by decide
theorem gStop_ne_gGo : gStop ≠ gGo := by decide

/-- Frame marker of stack `k`. -/
def gmk (k : Stk) : Glyph := .mk k

theorem gmk_ne_bit (k : Stk) (b : Bool) : gmk k ≠ Glyph.bit b := fun h => by cases h
theorem bit_ne_gmk (k : Stk) (b : Bool) : Glyph.bit b ≠ gmk k := fun h => by cases h
theorem gmk_ne_pos (k : Stk) : gmk k ≠ Glyph.pos := fun h => by cases h
theorem gmk_ne_neg (k : Stk) : gmk k ≠ Glyph.neg := fun h => by cases h
theorem gmk_ne_iend (k : Stk) : gmk k ≠ Glyph.iend := fun h => by cases h
theorem gmk_ne_eos (k : Stk) : gmk k ≠ Glyph.eos := fun h => by cases h
theorem gmk_ne_inp (k : Stk) (a b : Option Bool) : gmk k ≠ Glyph.inp a b := fun h => by cases h
theorem gmk_ne_cons (k : Stk) : gmk k ≠ Glyph.cons := fun h => by cases h
theorem gmk_ne_nil (k : Stk) : gmk k ≠ Glyph.nil := fun h => by cases h

/-- `l` contains no frame marker. -/
def NoMark (l : List Glyph) : Prop := ∀ g ∈ l, ∀ k : Stk, g ≠ gmk k

theorem NoMark.tail {g : Glyph} {l : List Glyph} (h : NoMark (g :: l)) : NoMark l :=
  fun x hx => h x (List.mem_cons_of_mem g hx)

theorem NoMark.cons {g : Glyph} {l : List Glyph} (h : NoMark l) (hg : ∀ k : Stk, g ≠ gmk k) :
    NoMark (g :: l) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hg
  · exact h x hx

theorem noMark_bitsG (l : List Bool) : NoMark (l.map Glyph.bit) :=
  fun g hg k => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
    exact bit_ne_gmk k b

/-! ## Bounded evaluation -/

/-- `Ev main p s s' C`: `p` runs from `s` to `s'` in at most `C` steps. -/
def Ev (main : Cmd) (p : Cmd) (s s' : State) (C : ℕ) : Prop := ∃ n, Eval main p s s' n ∧ n ≤ C

theorem Ev.mono {main : Cmd} {p : Cmd} {s s' : State} {C C' : ℕ} (h : Ev main p s s' C)
    (hC : C ≤ C') : Ev main p s s' C' := by
  obtain ⟨n, he, hl⟩ := h; exact ⟨n, he, le_trans hl hC⟩

theorem Ev.seq' {main : Cmd} {p q : Cmd} {s t u : State} {C₁ C₂ C : ℕ}
    (h₁ : Ev main p s t C₁) (h₂ : Ev main q t u C₂) (hC : C₁ + C₂ ≤ C) :
    Ev main (.seq p q) s u C := by
  obtain ⟨n₁, e₁, l₁⟩ := h₁
  obtain ⟨n₂, e₂, l₂⟩ := h₂
  refine ⟨n₁ + n₂, Eval.seq e₁ e₂, ?_⟩; omega

theorem Ev.iteT {main : Cmd} {r : Reg} {c : Glyph} {p q : Cmd} {s s' : State} {C : ℕ}
    (hr : s.reg r = c) (h : Ev main p s s' C) : Ev main (.ite r c p q) s s' (C + 1) := by
  obtain ⟨n, he, hl⟩ := h
  exact ⟨n + 1, Eval.iteT hr he, by omega⟩

theorem Ev.iteF {main : Cmd} {r : Reg} {c : Glyph} {p q : Cmd} {s s' : State} {C : ℕ}
    (hr : s.reg r ≠ c) (h : Ev main q s s' C) : Ev main (.ite r c p q) s s' (C + 1) := by
  obtain ⟨n, he, hl⟩ := h
  exact ⟨n + 1, Eval.iteF hr he, by omega⟩

theorem Ev.loopF {main : Cmd} {r : Reg} {c : Glyph} {body : Cmd} {s : State}
    (hr : s.reg r ≠ c) : Ev main (.loop r c body) s s 1 := ⟨1, Eval.loopF hr, le_rfl⟩

theorem Ev.loopT {main : Cmd} {r : Reg} {c : Glyph} {body : Cmd} {s s' s'' : State} {C₁ C₂ : ℕ}
    (hr : s.reg r = c) (h₁ : Ev main body s s' C₁) (h₂ : Ev main (.loop r c body) s' s'' C₂) :
    Ev main (.loop r c body) s s'' (C₁ + C₂ + 1) := by
  obtain ⟨n₁, e₁, l₁⟩ := h₁
  obtain ⟨n₂, e₂, l₂⟩ := h₂
  exact ⟨n₁ + n₂ + 1, Eval.loopT hr e₁ e₂, by omega⟩

theorem ev_pop' (main : Cmd) (k : Stk) (r : Reg) (g : Reg → Glyph) (X : Stk → List Glyph) :
    Ev main (.pop k r) ⟨g, X⟩
      ⟨Function.update g r ((X k).headD .eos), Function.update X k (X k).tail⟩ 1 :=
  ⟨1, Eval.pop k r ⟨g, X⟩, le_rfl⟩

theorem ev_push' (main : Cmd) (k : Stk) (r : Reg) (g : Reg → Glyph) (X : Stk → List Glyph) :
    Ev main (.push k r) ⟨g, X⟩ ⟨g, Function.update X k (g r :: X k)⟩ 1 :=
  ⟨1, Eval.push k r ⟨g, X⟩, le_rfl⟩

theorem ev_set' (main : Cmd) (r : Reg) (c : Glyph) (g : Reg → Glyph) (X : Stk → List Glyph) :
    Ev main (.set r c) ⟨g, X⟩ ⟨Function.update g r c, X⟩ 1 :=
  ⟨1, Eval.set r c ⟨g, X⟩, le_rfl⟩

@[simp] theorem upStk_same {X : Stk → List Glyph} (k : Stk) (l : List Glyph) :
    (Function.update X k l) k = l := Function.update_self k l X

@[simp] theorem upStk_ne {X : Stk → List Glyph} {k k' : Stk} (h : k ≠ k')
    (l : List Glyph) : (Function.update X k' l) k = X k := Function.update_of_ne h l X

@[simp] theorem upStk_ne' {X : Stk → List Glyph} {k k' : Stk} (h : k' ≠ k)
    (l : List Glyph) : (Function.update X k' l) k = X k :=
  Function.update_of_ne (Ne.symm h) l X

/-- Sequence a list of commands. -/
def seqs : List Cmd → Cmd
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

theorem seqs_pair (c d : Cmd) : seqs [c, d] = .seq c d := rfl

/-! ## `drain`: move a marked region onto another stack, reversed -/

/-- One iteration of the drain loop. -/
def drainBody (a b : Stk) (T : Glyph) (r rF : Reg) : Cmd :=
  seqs [.pop a r,
        .ite r T (seqs [.push a r, .set rF gStop]) (seqs [.push b r, .set rF gGo])]

theorem drain_body_go {main : Cmd} {a b : Stk} {T : Glyph} {r rF : Reg} (hab : a ≠ b)
    {h : Glyph} (hh : h ≠ T) {G A B : List Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} (ha : X a = h :: G ++ T :: A) (hb : X b = B) :
    ∃ (s' : State) (n : ℕ), Eval main (drainBody a b T r rF) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.reg rF = gGo ∧ s'.stk a = G ++ T :: A ∧ s'.stk b = h :: B ∧
      (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  have h1 : Ev main (.pop a r) ⟨g, X⟩
      ⟨Function.update g r h, Function.update X a (G ++ T :: A)⟩ 1 := by
    simpa [ha] using ev_pop' main a r g X
  have hh1 : (Function.update g r h) r ≠ T := by simpa using hh
  have hp : Ev main (.push b r) ⟨Function.update g r h, Function.update X a (G ++ T :: A)⟩
      ⟨Function.update g r h, Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩ 1 := by
    have h0 := ev_push' main b r (Function.update g r h) (Function.update X a (G ++ T :: A))
    have hXb : (Function.update X a (G ++ T :: A)) b = B := by
      simp [Function.update_apply, hab, Ne.symm hab, hb]
    simp only [hXb] at h0
    simpa using h0
  have hs : Ev main (.set rF gGo)
      ⟨Function.update g r h, Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩
      ⟨Function.update (Function.update g r h) rF gGo,
        Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩ 1 :=
    ev_set' main rF gGo (Function.update g r h)
      (Function.update (Function.update X a (G ++ T :: A)) b (h :: B))
  have h23 : Ev main (seqs [.push b r, .set rF gGo])
      ⟨Function.update g r h, Function.update X a (G ++ T :: A)⟩
      ⟨Function.update (Function.update g r h) rF gGo,
        Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩ 2 := by
    rw [seqs_pair]
    exact Ev.seq' hp hs (le_rfl)
  have hite : Ev main
      (seqs [.pop a r, .ite r T (seqs [.push a r, .set rF gStop]) (seqs [.push b r, .set rF gGo])])
      ⟨g, X⟩
      ⟨Function.update (Function.update g r h) rF gGo,
        Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩ 4 := by
    exact Ev.seq' h1 (Ev.iteF hh1 h23) (le_rfl)
  obtain ⟨n, he, hn⟩ := hite
  refine ⟨⟨Function.update (Function.update g r h) rF gGo,
    Function.update (Function.update X a (G ++ T :: A)) b (h :: B)⟩, n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [drainBody] using he
  · omega
  · exact Function.update_self rF gGo (Function.update g r h)
  · show (Function.update (Function.update X a (G ++ T :: A)) b (h :: B)) a = G ++ T :: A
    rw [upStk_ne hab, upStk_same]
  · show (Function.update (Function.update X a (G ++ T :: A)) b (h :: B)) b = h :: B
    rw [upStk_same]
  · intro k hk1 hk2
    show (Function.update (Function.update X a (G ++ T :: A)) b (h :: B)) k = X k
    rw [upStk_ne hk2, upStk_ne hk1]

theorem drain_body_hit {main : Cmd} {a b : Stk} {T : Glyph} {r rF : Reg} (hab : a ≠ b)
    {A B : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} (ha : X a = T :: A)
    (hb : X b = B) :
    ∃ (s' : State) (n : ℕ), Eval main (drainBody a b T r rF) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.reg rF = gStop ∧ s'.stk a = T :: A ∧ s'.stk b = B ∧
      (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  have h1 : Ev main (.pop a r) ⟨g, X⟩
      ⟨Function.update g r T, Function.update X a A⟩ 1 := by
    simpa [ha] using ev_pop' main a r g X
  have hp : Ev main (.push a r) ⟨Function.update g r T, Function.update X a A⟩
      ⟨Function.update g r T, Function.update X a (T :: A)⟩ 1 := by
    have h0 := ev_push' main a r (Function.update g r T) (Function.update X a A)
    simp only [Function.update_self, Function.update_idem] at h0
    simpa using h0
  have hs : Ev main (.set rF gStop)
      ⟨Function.update g r T, Function.update X a (T :: A)⟩
      ⟨Function.update (Function.update g r T) rF gStop, Function.update X a (T :: A)⟩ 1 :=
    ev_set' main rF gStop (Function.update g r T) (Function.update X a (T :: A))
  have h23 : Ev main (seqs [.push a r, .set rF gStop])
      ⟨Function.update g r T, Function.update X a A⟩
      ⟨Function.update (Function.update g r T) rF gStop, Function.update X a (T :: A)⟩ 2 := by
    rw [seqs_pair]
    exact Ev.seq' hp hs (le_rfl)
  have hreg : (⟨Function.update g r T, Function.update X a A⟩ : State).reg r = T :=
    Function.update_self r T g
  have hite : Ev main
      (seqs [.pop a r, .ite r T (seqs [.push a r, .set rF gStop]) (seqs [.push b r, .set rF gGo])])
      ⟨g, X⟩ ⟨Function.update (Function.update g r T) rF gStop, Function.update X a (T :: A)⟩ 4 := by
    exact Ev.seq' h1 (Ev.iteT hreg h23) (by omega)
  obtain ⟨n, he, hn⟩ := hite
  refine ⟨⟨Function.update (Function.update g r T) rF gStop, Function.update X a (T :: A)⟩,
    n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [drainBody] using he
  · omega
  · exact Function.update_self rF gStop (Function.update g r T)
  · show (Function.update X a (T :: A)) a = T :: A
    rw [upStk_same]
  · show (Function.update X a (T :: A)) b = B
    rw [upStk_ne' hab]; exact hb
  · intro k hk1 hk2
    show (Function.update X a (T :: A)) k = X k
    rw [upStk_ne hk1]

/-- The drain loop: move the region `G` above the marker `T` of stack `a` onto stack `b`
(reversing it); `T` stays on `a`. -/
theorem drain_loop_ev (main : Cmd) (a b : Stk) (T : Glyph) (r rF : Reg) (hab : a ≠ b)
    (hrF : rF ≠ r) :
    ∀ (G : List Glyph) (A B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ T) → g rF = gGo → X a = G ++ T :: A → X b = B →
      ∃ (s' : State) (n : ℕ), Eval main (.loop rF gGo (drainBody a b T r rF)) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (G.length + 1) + 1 ∧ s'.reg rF ≠ gGo ∧
        s'.stk a = T :: A ∧ s'.stk b = G.reverse ++ B ∧
        (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  intro G
  induction G with
  | nil =>
      intro A B g X _ hgo ha hb
      obtain ⟨s1, n1, he1, hn1, hre1, ha1, hb1, ho1⟩ :=
        drain_body_hit (main := main) (a := a) (b := b) (T := T) (r := r) (rF := rF)
          (hab := hab) (A := A) (B := B) (g := g) (X := X) ha hb
      have hne : s1.reg rF ≠ gGo := by rw [hre1]; exact gStop_ne_gGo
      have hloop : Eval main (.loop rF gGo (drainBody a b T r rF)) ⟨g, X⟩ s1 (n1 + 1 + 1) :=
        Eval.loopT hgo he1 (Eval.loopF (main := main) (s := s1) hne)
      refine ⟨s1, n1 + 1 + 1, hloop, ?_, hne, ha1, ?_, ho1⟩
      · simp only [List.length_nil]; omega
      · rw [List.reverse_nil, List.nil_append]; exact hb1
  | cons h G' ih =>
      intro A B g X hG hgo ha hb
      have hh : h ≠ T := hG h (List.mem_cons_self ..)
      have hG' : ∀ x ∈ G', x ≠ T := fun x hx => hG x (List.mem_cons_of_mem h hx)
      obtain ⟨s1, n1, he1, hn1, hre1, ha1, hb1, ho1⟩ :=
        drain_body_go (main := main) (a := a) (b := b) (T := T) (r := r) (rF := rF)
          (hab := hab) (hh := hh) (G := G') (A := A) (B := B) (g := g) (X := X) ha hb
      obtain ⟨s2, n2, he2, hn2, hre2, ha2, hb2, ho2⟩ :=
        ih A (h :: B) s1.reg s1.stk hG' hre1 ha1 hb1
      have hloop : Eval main (.loop rF gGo (drainBody a b T r rF)) ⟨g, X⟩ s2 (n1 + n2 + 1) :=
        Eval.loopT hgo he1 he2
      refine ⟨s2, n1 + n2 + 1, hloop, ?_, hre2, ha2, ?_, ?_⟩
      · have hlen : G'.length + 1 = (h :: G').length := rfl
        omega
      · rw [hb2, List.reverse_cons, List.append_assoc]
        rfl
      · intro k hk1 hk2
        rw [ho2 k hk1 hk2, ho1 k hk1 hk2]

/-- Move the region above the marker `T` of stack `a` onto stack `b` (reversing it); `T` is
pushed back onto `a`. -/
def drain (a b : Stk) (T : Glyph) (r rF : Reg) : Cmd :=
  seqs [.set rF gGo, .loop rF gGo (drainBody a b T r rF)]

theorem drain_ev (main : Cmd) (a b : Stk) (T : Glyph) (r rF : Reg) (hab : a ≠ b)
    (hrF : rF ≠ r) :
    ∀ (G A B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ T) → X a = G ++ T :: A → X b = B →
      ∃ (s' : State) (n : ℕ), Eval main (drain a b T r rF) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (G.length + 1) + 2 ∧ s'.reg rF ≠ gGo ∧
        s'.stk a = T :: A ∧ s'.stk b = G.reverse ++ B ∧
        (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  intro G A B g X hG ha hb
  have hgo : (Function.update g rF gGo) rF = gGo := Function.update_self rF gGo g
  obtain ⟨s', n, he, hn, hne, ha', hb', ho'⟩ :=
    drain_loop_ev main a b T r rF hab hrF G A B (Function.update g rF gGo) X hG hgo ha hb
  have hset : Ev main (.set rF gGo) ⟨g, X⟩ ⟨Function.update g rF gGo, X⟩ 1 :=
    ev_set' main rF gGo g X
  obtain ⟨m, hm, _⟩ := hset
  refine ⟨s', m + n, ?_, ?_, hne, ha', hb', ho'⟩
  · rw [drain, seqs_pair]; exact Eval.seq hm he
  · omega

/-- `drain` followed by popping the marker `T` from `a`. -/
def drainPop (a b : Stk) (T : Glyph) (r rF : Reg) : Cmd := seqs [drain a b T r rF, .pop a r]

theorem drainPop_ev (main : Cmd) (a b : Stk) (T : Glyph) (r rF : Reg) (hab : a ≠ b)
    (hrF : rF ≠ r) :
    ∀ (G A B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ T) → X a = G ++ T :: A → X b = B →
      ∃ (s' : State) (n : ℕ), Eval main (drainPop a b T r rF) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (G.length + 1) + 4 ∧ s'.stk a = A ∧ s'.stk b = G.reverse ++ B ∧
        (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  intro G A B g X hG ha hb
  obtain ⟨s1, n1, he1, hn1, _, ha1, hb1, ho1⟩ :=
    drain_ev (main := main) a b T r rF hab hrF G A B g X hG ha hb
  have hp : Ev main (.pop a r) s1
      ⟨Function.update s1.reg r ((s1.stk a).headD .eos),
        Function.update s1.stk a (s1.stk a).tail⟩ 1 :=
    ev_pop' main a r s1.reg s1.stk
  obtain ⟨m, hm, _⟩ := hp
  refine ⟨⟨Function.update s1.reg r ((s1.stk a).headD .eos),
    Function.update s1.stk a ((s1.stk a).tail)⟩, n1 + m, ?_, ?_, ?_, ?_, ?_⟩
  · rw [drainPop, seqs_pair]; exact Eval.seq he1 hm
  · omega
  · show (Function.update s1.stk a ((s1.stk a).tail)) a = A
    rw [upStk_same, ha1]; rfl
  · show (Function.update s1.stk a ((s1.stk a).tail)) b = G.reverse ++ B
    rw [upStk_ne' hab]; exact hb1
  · intro k hk1 hk2
    show (Function.update s1.stk a ((s1.stk a).tail)) k = X k
    rw [upStk_ne hk1]; exact ho1 k hk1 hk2

/-! ## `clearRgn`: discard a marked region -/

/-- One iteration of the clearing loop. -/
def clearBody (k : Stk) (M : Glyph) (r rF : Reg) : Cmd :=
  seqs [.pop k r,
        .ite r M (seqs [.push k r, .set rF gStop]) (.set rF gGo)]

theorem clear_body_go {main : Cmd} {k : Stk} {M : Glyph} {r rF : Reg} {h : Glyph} (hh : h ≠ M)
    {G A : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} (ha : X k = h :: G ++ M :: A)
    (hgo : g rF = gGo) :
    ∃ (s' : State) (n : ℕ), Eval main (clearBody k M r rF) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.reg rF = gGo ∧ s'.stk k = G ++ M :: A ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  have h1 : Ev main (.pop k r) ⟨g, X⟩
      ⟨Function.update g r h, Function.update X k (G ++ M :: A)⟩ 1 := by
    simpa [ha] using ev_pop' main k r g X
  have hh1 : (Function.update g r h) r ≠ M := by simpa using hh
  have hs : Ev main (.set rF gGo)
      ⟨Function.update g r h, Function.update X k (G ++ M :: A)⟩
      ⟨Function.update (Function.update g r h) rF gGo, Function.update X k (G ++ M :: A)⟩ 1 :=
    ev_set' main rF gGo (Function.update g r h) (Function.update X k (G ++ M :: A))
  have hite : Ev main
      (seqs [.pop k r, .ite r M (seqs [.push k r, .set rF gStop]) (.set rF gGo)])
      ⟨g, X⟩ ⟨Function.update (Function.update g r h) rF gGo, Function.update X k (G ++ M :: A)⟩ 3 :=
    Ev.seq' h1 (Ev.iteF hh1 hs) (le_rfl)
  obtain ⟨n, he, hn⟩ := hite
  refine ⟨⟨Function.update (Function.update g r h) rF gGo, Function.update X k (G ++ M :: A)⟩,
    n, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [clearBody] using he
  · omega
  · exact Function.update_self rF gGo (Function.update g r h)
  · show (Function.update X k (G ++ M :: A)) k = G ++ M :: A
    rw [upStk_same]
  · intro j hj
    show (Function.update X k (G ++ M :: A)) j = X j
    rw [upStk_ne hj]

theorem clear_body_hit {main : Cmd} {k : Stk} {M : Glyph} {r rF : Reg} {A : List Glyph}
    {g : Reg → Glyph} {X : Stk → List Glyph} (ha : X k = M :: A) :
    ∃ (s' : State) (n : ℕ), Eval main (clearBody k M r rF) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.reg rF = gStop ∧ s'.stk k = M :: A ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  have h1 : Ev main (.pop k r) ⟨g, X⟩
      ⟨Function.update g r M, Function.update X k A⟩ 1 := by
    simpa [ha] using ev_pop' main k r g X
  have hp : Ev main (.push k r) ⟨Function.update g r M, Function.update X k A⟩
      ⟨Function.update g r M, Function.update X k (M :: A)⟩ 1 := by
    have h0 := ev_push' main k r (Function.update g r M) (Function.update X k A)
    simp only [Function.update_self, Function.update_idem] at h0
    simpa using h0
  have hs : Ev main (.set rF gStop)
      ⟨Function.update g r M, Function.update X k (M :: A)⟩
      ⟨Function.update (Function.update g r M) rF gStop, Function.update X k (M :: A)⟩ 1 :=
    ev_set' main rF gStop (Function.update g r M) (Function.update X k (M :: A))
  have h23 : Ev main (seqs [.push k r, .set rF gStop])
      ⟨Function.update g r M, Function.update X k A⟩
      ⟨Function.update (Function.update g r M) rF gStop, Function.update X k (M :: A)⟩ 2 := by
    rw [seqs_pair]; exact Ev.seq' hp hs (le_rfl)
  have hreg : (⟨Function.update g r M, Function.update X k A⟩ : State).reg r = M :=
    Function.update_self r M g
  have hite : Ev main
      (seqs [.pop k r, .ite r M (seqs [.push k r, .set rF gStop]) (.set rF gGo)])
      ⟨g, X⟩ ⟨Function.update (Function.update g r M) rF gStop, Function.update X k (M :: A)⟩ 4 :=
    Ev.seq' h1 (Ev.iteT hreg h23) (le_rfl)
  obtain ⟨n, he, hn⟩ := hite
  refine ⟨⟨Function.update (Function.update g r M) rF gStop, Function.update X k (M :: A)⟩,
    n, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [clearBody] using he
  · omega
  · exact Function.update_self rF gStop (Function.update g r M)
  · show (Function.update X k (M :: A)) k = M :: A
    rw [upStk_same]
  · intro j hj
    show (Function.update X k (M :: A)) j = X j
    rw [upStk_ne hj]

/-- The clearing loop: discard the region `G` above the marker `M` of stack `k`. -/
theorem clearRgn_loop_ev (main : Cmd) (k : Stk) (M : Glyph) (r rF : Reg) :
    ∀ (G A : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ M) → g rF = gGo → X k = G ++ M :: A →
      ∃ (s' : State) (n : ℕ), Eval main (.loop rF gGo (clearBody k M r rF)) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (G.length + 1) + 1 ∧ s'.reg rF ≠ gGo ∧ s'.stk k = M :: A ∧
        (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  intro G
  induction G with
  | nil =>
      intro A g X _ hgo ha
      obtain ⟨s1, n1, he1, hn1, hre1, ha1, ho1⟩ :=
        clear_body_hit (main := main) (k := k) (M := M) (r := r) (rF := rF) (A := A) (g := g)
          (X := X) ha
      have hne : s1.reg rF ≠ gGo := by rw [hre1]; exact gStop_ne_gGo
      have hloop : Eval main (.loop rF gGo (clearBody k M r rF)) ⟨g, X⟩ s1 (n1 + 1 + 1) :=
        Eval.loopT hgo he1 (Eval.loopF (main := main) (s := s1) hne)
      refine ⟨s1, n1 + 1 + 1, hloop, ?_, hne, ha1, ho1⟩
      · simp only [List.length_nil]; omega
  | cons h G' ih =>
      intro A g X hG hgo ha
      have hh : h ≠ M := hG h (List.mem_cons_self ..)
      have hG' : ∀ x ∈ G', x ≠ M := fun x hx => hG x (List.mem_cons_of_mem h hx)
      obtain ⟨s1, n1, he1, hn1, hre1, ha1, ho1⟩ :=
        clear_body_go (main := main) (k := k) (M := M) (r := r) (rF := rF) (h := h) (hh := hh)
          (G := G') (A := A) (g := g) (X := X) ha hgo
      obtain ⟨s2, n2, he2, hn2, hre2, ha2, ho2⟩ := ih A s1.reg s1.stk hG' hre1 ha1
      have hloop : Eval main (.loop rF gGo (clearBody k M r rF)) ⟨g, X⟩ s2 (n1 + n2 + 1) :=
        Eval.loopT hgo he1 he2
      refine ⟨s2, n1 + n2 + 1, hloop, ?_, hre2, ha2, ?_⟩
      · have hlen : G'.length + 1 = (h :: G').length := rfl
        omega
      · intro j hj
        rw [ho2 j hj, ho1 j hj]

/-- Discard the region above the marker `M` of stack `k`. -/
def clearRgn (k : Stk) (M : Glyph) (r rF : Reg) : Cmd :=
  seqs [.set rF gGo, .loop rF gGo (clearBody k M r rF)]

theorem clearRgn_ev (main : Cmd) (k : Stk) (M : Glyph) (r rF : Reg) :
    ∀ (G A : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ M) → X k = G ++ M :: A →
      ∃ (s' : State) (n : ℕ), Eval main (clearRgn k M r rF) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (G.length + 1) + 2 ∧ s'.reg rF ≠ gGo ∧ s'.stk k = M :: A ∧
        (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  intro G A g X hG ha
  have hgo : (Function.update g rF gGo) rF = gGo := Function.update_self rF gGo g
  obtain ⟨s', n, he, hn, hne, ha', ho'⟩ :=
    clearRgn_loop_ev main k M r rF G A (Function.update g rF gGo) X hG hgo ha
  have hset : Ev main (.set rF gGo) ⟨g, X⟩ ⟨Function.update g rF gGo, X⟩ 1 :=
    ev_set' main rF gGo g X
  obtain ⟨m, hm, _⟩ := hset
  refine ⟨s', m + n, ?_, ?_, hne, ha', ho'⟩
  · rw [clearRgn, seqs_pair]; exact Eval.seq hm he
  · omega

/-- Discard the region above the marker of stack `k` and pop the marker itself. -/
def clearAll (k : Stk) (r rF : Reg) : Cmd := seqs [clearRgn k (gmk k) r rF, .pop k r]

theorem clearAll_ev {main : Cmd} (k : Stk) (r rF : Reg) :
    ∀ (G A : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ gmk k) → X k = G ++ gmk k :: A →
      ∃ (s' : State) (n : ℕ), Eval main (clearAll k r rF) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (G.length + 1) + 4 ∧ s'.stk k = A ∧
        (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  intro G A g X hG ha
  obtain ⟨s1, n1, he1, hn1, _, ha1, ho1⟩ := clearRgn_ev main k (gmk k) r rF G A g X hG ha
  have hp : Ev main (.pop k r) s1
      ⟨Function.update s1.reg r ((s1.stk k).headD .eos),
        Function.update s1.stk k (s1.stk k).tail⟩ 1 :=
    ev_pop' main k r s1.reg s1.stk
  obtain ⟨m, hm, _⟩ := hp
  refine ⟨⟨Function.update s1.reg r ((s1.stk k).headD .eos),
    Function.update s1.stk k ((s1.stk k).tail)⟩, n1 + m, ?_, ?_, ?_, ?_⟩
  · rw [clearAll, seqs_pair]; exact Eval.seq he1 hm
  · omega
  · show (Function.update s1.stk k ((s1.stk k).tail)) k = A
    rw [upStk_same, ha1]; rfl
  · intro j hj
    show (Function.update s1.stk k ((s1.stk k).tail)) j = X j
    rw [upStk_ne hj]; exact ho1 j hj

end Shift
end Work.IntLib
