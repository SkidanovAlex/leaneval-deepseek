import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.Defs

/-!
# Raw StackLang toolkit for the IntLib development (area IntLib)

Reusable `Eval` lemmas for writing and verifying raw StackLang programs on 16 stacks of `Glyph`.
Nothing here mentions values on stack 0; see `Bits.lean` for the bit-string layer and `Value.lean`
for the value-level read/write words.

Conventions
* `consume k T r handler`: repeatedly `pop` a glyph from stack `k` into register `r`; if it is `T`
  (the frame marker of the data on `k`) push it back and stop; otherwise run `handler` (with `r`
  holding the glyph) and continue.  The stack `k` is left exactly as found.
* a `Reg` is a `Fin 16`, a `Stk` is a `Fin 16`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-! ## Basic `Eval` lemmas -/

theorem Eval.pop_cons {main : Cmd} {k : Stk} {r : Reg} {s : State} {g : Glyph} {rest : List Glyph}
    (h : s.stk k = g :: rest) :
    Eval main (.pop k r) s ⟨Function.update s.reg r g, Function.update s.stk k rest⟩ 1 := by
  simpa [h] using Eval.pop k r s

theorem Eval.peek_cons {main : Cmd} {k : Stk} {r : Reg} {s : State} {g : Glyph} {rest : List Glyph}
    (h : s.stk k = g :: rest) :
    Eval main (.peek k r) s ⟨Function.update s.reg r g, s.stk⟩ 1 := by
  simpa [h] using Eval.peek k r s

theorem Eval.push_eq {main : Cmd} {k : Stk} {r : Reg} {s : State} {g : Glyph}
    (h : s.reg r = g) :
    Eval main (.push k r) s ⟨s.reg, Function.update s.stk k (g :: s.stk k)⟩ 1 := by
  simpa [h] using Eval.push k r s

theorem Eval.set_eq {main : Cmd} {r : Reg} {s : State} {c : Glyph} :
    Eval main (.set r c) s ⟨Function.update s.reg r c, s.stk⟩ 1 := Eval.set r c s

/-- state equality from register and stack functions -/
theorem State.ext_mk {s t : State} (h1 : t.reg = s.reg) (h2 : t.stk = s.stk) : t = s := by
  have e : t = ⟨t.reg, t.stk⟩ := rfl
  rw [e, h1, h2]

/-- changing the register is unsensitive: state equality -/
theorem State.mk_reg_stk (s : State) (r : Reg) (g : Glyph) :
    (⟨Function.update s.reg r g, s.stk⟩ : State).stk = s.stk := rfl

theorem State.stk_update_eq {s : State} {k : Stk} {l : List Glyph} (h : s.stk k = l) :
    (⟨s.reg, Function.update s.stk k l⟩ : State) = s := by
  have h2 : Function.update s.stk k l = s.stk := by
    funext j
    by_cases hj : j = k
    · subst hj; simpa using h.symm
    · simp [Function.update_of_ne hj]
  simp [h2]

theorem State.reg_update_eq {s : State} {r : Reg} {g : Glyph} (h : s.reg r = g) :
    (⟨Function.update s.reg r g, s.stk⟩ : State) = s := by
  have h2 : Function.update s.reg r g = s.reg := by
    funext j
    by_cases hj : j = r
    · subst hj; simpa using h.symm
    · simp [Function.update_of_ne hj]
  simp [h2]

/-! ## A general loop lemma -/

/-- `Eval.loop` with a decreasing measure: if each iteration of `body` (run while `reg r = c`)
costs at most `b` and strictly decreases `meas`, then the loop terminates in at most
`meas s * (b + 1) + 1` steps. -/
theorem loop_measure {main : Cmd} (r : Reg) (c : Glyph) (body : Cmd) (Inv : State → Prop)
    (meas : State → ℕ) (b : ℕ)
    (hpos : ∀ s, Inv s → s.reg r = c → 0 < meas s)
    (h : ∀ s, Inv s → s.reg r = c →
      ∃ s' n, Eval main body s s' n ∧ n ≤ b ∧ Inv s' ∧ meas s' < meas s) :
    ∀ s, Inv s → s.reg r = c →
      ∃ s' n, Eval main (.loop r c body) s s' n ∧ Inv s' ∧ s'.reg r ≠ c ∧ n ≤ meas s * (b + 1) + 1 := by
  have hwf : WellFounded (fun (a b : State) => meas a < meas b) := InvImage.wf meas Nat.lt_wfRel.wf
  intro s
  refine hwf.induction (C := fun s => Inv s → s.reg r = c →
      ∃ s' n, Eval main (.loop r c body) s s' n ∧ Inv s' ∧ s'.reg r ≠ c ∧
        n ≤ meas s * (b + 1) + 1) s ?_
  intro s ih hs hrc
  obtain ⟨s', n, hev, hn, hinv, hlt⟩ := h s hs hrc
  by_cases hrc' : s'.reg r = c
  · obtain ⟨s'', n', hev', hinv', hreg', hn'⟩ := ih s' hlt hinv hrc'
    have hm : 1 ≤ meas s := hpos s hs hrc
    refine ⟨s'', n + n' + 1, Eval.loopT hrc hev hev', hinv', hreg', ?_⟩
    have h1 : meas s' + 1 ≤ meas s := by omega
    have h2 : (meas s' + 1) * (b + 1) ≤ meas s * (b + 1) := Nat.mul_le_mul_right _ h1
    have h3 : n + meas s' * (b + 1) + 1 ≤ meas s' * (b + 1) + (b + 1) + 1 := by
      have : n ≤ b := hn
      nlinarith
    calc n + n' + 1 ≤ n + (meas s' * (b + 1) + 1) + 1 := by omega
      _ ≤ meas s' * (b + 1) + (b + 1) + 1 := by omega
      _ = (meas s' + 1) * (b + 1) + 1 := by ring
      _ ≤ meas s * (b + 1) + 1 := by omega
  · refine ⟨s', n + 1 + 1, Eval.loopT hrc hev (Eval.loopF hrc'), hinv, hrc', ?_⟩
    have hm : 1 ≤ meas s := hpos s hs hrc
    nlinarith

/-! ## `consume`: pop a marked segment of a stack, feeding its glyphs to a handler -/

/-- Body of the `consume` loop. -/
def consumeStep (k : Stk) (T : Glyph) (r : Reg) (handler : Cmd) : Cmd :=
  .seq (.pop k r)
    (.ite r T (.seq (.push k r) (.set r (.mk 0))) (.seq handler (.set r .eos)))

/-- `consumeLoop k T r handler`: while `reg r = eos`, pop a glyph `g` from the top of stack `k`;
if `g = T` (frame marker) push it back and stop, otherwise run `handler` (with `reg r = g`)
and continue. -/
def consumeLoop (k : Stk) (T : Glyph) (r : Reg) (handler : Cmd) : Cmd :=
  .loop r .eos (consumeStep k T r handler)

/-- `consume k T r handler` = `consumeLoop` with the loop register initialised. -/
def consume (k : Stk) (T : Glyph) (r : Reg) (handler : Cmd) : Cmd :=
  .seq (.set r .eos) (consumeLoop k T r handler)

/-- Specification of `consumeLoop`: `Inv gs s` says that `gs` are the glyphs of stack `k` above its
frame marker `T`, with all other data as described by `Inv`; `handler` is run once per glyph. -/
theorem consumeLoop_eval {main : Cmd} {k : Stk} {T : Glyph} {r : Reg} {handler : Cmd}
    {Inv : List Glyph → State → Prop} {below : List Glyph} {b : ℕ}
    (hstk : ∀ gs s, Inv gs s → s.stk k = gs ++ T :: below)
    (hterm : ∀ (g : Glyph) (gs : List Glyph) (s : State), Inv (g :: gs) s → g ≠ T)
    (hreg : ∀ gs s (g : Glyph), Inv gs s → Inv gs ⟨Function.update s.reg r g, s.stk⟩)
    (hpop : ∀ (g : Glyph) (gs : List Glyph) (s : State), Inv (g :: gs) s →
      Inv gs ⟨Function.update s.reg r g, Function.update s.stk k (gs ++ T :: below)⟩)
    (hstep : ∀ (g : Glyph) (gs : List Glyph) (s : State), g ≠ T → s.reg r = g → Inv gs s →
      ∃ s' n, Eval main handler s s' n ∧ n ≤ b ∧ Inv gs s') :
    ∀ (gs : List Glyph) (s : State), Inv gs s → s.reg r = Glyph.eos →
      ∃ s' n, Eval main (consumeLoop k T r handler) s s' n ∧ Inv [] s' ∧ s'.reg r ≠ Glyph.eos ∧
        n ≤ (gs.length + 1) * (b + 4) + 6 := by
  intro gs
  induction gs with
  | nil =>
    intro s hs hr
    have hsk : s.stk k = T :: below := hstk [] s hs
    let s1 : State := ⟨Function.update s.reg r T, Function.update s.stk k below⟩
    let s2 : State := ⟨s1.reg, Function.update s1.stk k (T :: s1.stk k)⟩
    let s3 : State := ⟨Function.update s2.reg r (Glyph.mk 0), s2.stk⟩
    have h1 : Eval main (.pop k r) s s1 1 := Eval.pop_cons hsk
    have hr1 : s1.reg r = T := by simp [s1]
    have h2 : Eval main (.push k r) s1 s2 1 := by
      have h := Eval.push (main := main) k r s1
      simpa [s2, hr1] using h
    have h3 : Eval main (.set r (Glyph.mk 0)) s2 s3 1 := by
      have h := Eval.set (main := main) r (Glyph.mk 0) s2
      simpa [s3] using h
    have h23 : Eval main (.seq (.push k r) (.set r (Glyph.mk 0))) s1 s3 2 := Eval.seq h2 h3
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (Glyph.mk 0)))
        (.seq handler (.set r .eos))) s1 s3 3 := Eval.iteT hr1 h23
    have hbody : Eval main (consumeStep k T r handler) s s3 4 := Eval.seq h1 hite
    have hexit : s3.reg r ≠ Glyph.eos := by simp [s3, s2, s1]
    have hloop : Eval main (consumeLoop k T r handler) s3 s3 1 := Eval.loopF hexit
    have hmain : Eval main (consumeLoop k T r handler) s s3 6 := Eval.loopT hr hbody hloop
    have hs3stk : s3.stk = s.stk := by
      funext j
      simp only [s3, s2, s1, Function.update_apply]
      by_cases hjk : j = k
      · subst hjk; simp [hsk]
      · simp [hjk]
    have hs3reg : s3.reg = Function.update s.reg r (Glyph.mk 0) := by
      funext j
      simp only [s3, s2, s1, Function.update_apply]
      by_cases hjr : j = r <;> simp [hjr]
    have hs3eq : s3 = ⟨Function.update s.reg r (Glyph.mk 0), s.stk⟩ := State.ext_mk hs3reg hs3stk
    refine ⟨s3, 6, hmain, ?_, hexit, by simp⟩
    rw [hs3eq]
    exact hreg [] s (Glyph.mk 0) hs
  | cons g gs ih =>
    intro s hs hr
    have hgT : g ≠ T := hterm g gs s hs
    have hsk : s.stk k = g :: (gs ++ T :: below) := by
      simpa using hstk (g :: gs) s hs
    let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (gs ++ T :: below)⟩
    have h1 : Eval main (.pop k r) s s1 1 := Eval.pop_cons hsk
    have hr1 : s1.reg r = g := by simp [s1]
    have hpop' : Inv gs s1 := hpop g gs s hs
    obtain ⟨s2, n2, hev2, hn2, hinv2⟩ := hstep g gs s1 hgT hr1 hpop'
    let s3 : State := ⟨Function.update s2.reg r Glyph.eos, s2.stk⟩
    have h3 : Eval main (.set r .eos) s2 s3 1 := by
      have h := Eval.set (main := main) r Glyph.eos s2
      simpa [s3] using h
    have hb : Eval main (consumeStep k T r handler) s s3 (1 + ((n2 + 1) + 1)) := by
      have h23 : Eval main (.seq handler (.set r .eos)) s1 s3 (n2 + 1) := Eval.seq hev2 h3
      have hite : Eval main (.ite r T (.seq (.push k r) (.set r (.mk 0)))
          (.seq handler (.set r .eos))) s1 s3 ((n2 + 1) + 1) :=
        Eval.iteF (by rw [hr1]; exact hgT) h23
      exact Eval.seq h1 hite
    have hr3 : s3.reg r = Glyph.eos := by simp [s3]
    have hs3stk : s3.stk = s2.stk := by funext j; simp [s3]
    have hs3eq : s3 = ⟨Function.update s2.reg r Glyph.eos, s2.stk⟩ := State.ext_mk rfl hs3stk
    have hinv3 : Inv gs s3 := hs3eq ▸ hreg gs s2 Glyph.eos hinv2
    obtain ⟨s4, n4, hev4, hinv4, hneq4, hn4⟩ := ih s3 hinv3 hr3
    have hloop : Eval main (consumeLoop k T r handler) s3 s4 n4 := hev4
    refine ⟨s4, (1 + ((n2 + 1) + 1)) + n4 + 1, Eval.loopT hr hb hloop, hinv4, hneq4, ?_⟩
    have hlen : (gs.length + 1) * (b + 4) + 6 + (b + 4) = ((g :: gs).length + 1) * (b + 4) + 6 := by
      simp [List.length_cons]; ring
    omega

/-- Specification of `consume`: as `consumeLoop_eval`, one extra step for the initial `set r eos`. -/
theorem consume_eval {main : Cmd} {k : Stk} {T : Glyph} {r : Reg} {handler : Cmd}
    {Inv : List Glyph → State → Prop} {below : List Glyph} {b : ℕ}
    (hstk : ∀ gs s, Inv gs s → s.stk k = gs ++ T :: below)
    (hterm : ∀ (g : Glyph) (gs : List Glyph) (s : State), Inv (g :: gs) s → g ≠ T)
    (hreg : ∀ gs s (g : Glyph), Inv gs s → Inv gs ⟨Function.update s.reg r g, s.stk⟩)
    (hpop : ∀ (g : Glyph) (gs : List Glyph) (s : State), Inv (g :: gs) s →
      Inv gs ⟨Function.update s.reg r g, Function.update s.stk k (gs ++ T :: below)⟩)
    (hstep : ∀ (g : Glyph) (gs : List Glyph) (s : State), g ≠ T → s.reg r = g → Inv gs s →
      ∃ s' n, Eval main handler s s' n ∧ n ≤ b ∧ Inv gs s')
    (gs : List Glyph) (s : State) (hs : Inv gs s) :
    ∃ s' n, Eval main (consume k T r handler) s s' n ∧ Inv [] s' ∧ s'.reg r ≠ Glyph.eos ∧
      n ≤ (gs.length + 1) * (b + 4) + 7 := by
  let s1 : State := ⟨Function.update s.reg r Glyph.eos, s.stk⟩
  have h1 : Eval main (.set r Glyph.eos) s s1 1 := Eval.set_eq
  have hs1 : Inv gs s1 := hreg gs s Glyph.eos hs
  have hr1 : s1.reg r = Glyph.eos := by simp [s1]
  obtain ⟨s', n, hev, hinv, hneq, hn⟩ :=
    consumeLoop_eval hstk hterm hreg hpop hstep gs s1 hs1 hr1
  exact ⟨s', 1 + n, Eval.seq h1 hev, hinv, hneq, by omega⟩

end Work.IntLib
