import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.mvRevOntoTight

/-!
# `div_emit_eval`: emitting the result of the division core onto the value stack

`Work.IntLib.Div.emit sg` is the last part of the fix-ups of the division core: it writes the value
on stack 8 (`Div.stX`, `l.reverse` above the marker `gX`) as a value onto stack 0, preceded by the
`iend` and followed by the sign glyph held in register `sg`:

`seqs [set rgT iend, push 0 rgT, mvRevOnto stX gX 0 rgT, mkG stX gX, mov rgT sg, push 0 rgT]`

The cost bound `5 * l.length + 15` is tight: the region move costs `5 * l.length + 8` (the marker
loop `consumeLoop` costs `5 * L` plus its `6` steps of initialisation, `consume` one more step for
its `set r eos`, and the final `pop` one step), the remaining six primitive steps being
`set`, `push`, `set`, `push`, `mov`, `push` and the trailing `skip` of `seqs`.

The existing `mvRevOntoTight` has *one* step of slack (`5 * L + 9`) and says nothing about the
registers, while the `mov rgT sg` at the end needs the fact that `mvRevOnto` leaves every register
other than `rgT` untouched.  We therefore reprove the region move with a register frame and the
tight cost; the extra conclusion is carried through the same induction.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- `consumeLoop k T r (.push k' r)` moves the glyphs above the marker `T` of stack `k` onto stack
`k'` in reverse order (`l = pre ++ gs`, `gs` the part still on `k`), costing at most
`6 + 5 * gs.length`, and it changes no register other than `r`. -/
theorem consumeLoop_push_rev_regs (main : Cmd) (k : Stk) (T : Glyph) (k' : Stk) (r : Reg)
    (hne : k ≠ k') (bk bk' l : List Glyph) (hT : ∀ g ∈ l, g ≠ T) :
    ∀ (pre gs : List Glyph) (s : State), l = pre ++ gs → s.stk k = gs ++ T :: bk →
      s.stk k' = pre.reverse ++ bk' → s.reg r = Glyph.eos →
      ∃ s' n, Eval main (consumeLoop k T r (.push k' r)) s s' n ∧
        s'.stk k = T :: bk ∧ s'.stk k' = l.reverse ++ bk' ∧ s'.reg r ≠ Glyph.eos ∧
        n ≤ 6 + 5 * gs.length ∧
        (∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) ∧
        (∀ j : Reg, j ≠ r → s'.reg j = s.reg j) := by
  intro pre gs
  induction gs generalizing pre with
  | nil =>
    intro s hl hstk hstk' hreg
    have hl' : l = pre := by rw [hl, List.append_nil]
    have hsk : s.stk k = T :: bk := by rw [hstk]; simp
    let s1 : State := ⟨Function.update s.reg r T, Function.update s.stk k bk⟩
    let s2 : State := ⟨s1.reg, Function.update s1.stk k (T :: s1.stk k)⟩
    let s3 : State := ⟨Function.update s2.reg r (Glyph.mk 0), s2.stk⟩
    have e1 : Eval main (.pop k r) s s1 1 := Eval.pop_cons hsk
    have hr1 : s1.reg r = T := by simp [s1]
    have e2 : Eval main (.push k r) s1 s2 1 := by
      have h := Eval.push (main := main) k r s1
      simpa [s2, hr1] using h
    have e3 : Eval main (.set r (Glyph.mk 0)) s2 s3 1 := by
      have h := Eval.set (main := main) r (Glyph.mk 0) s2
      simpa [s3] using h
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (.mk 0)))
        (.seq (.push k' r) (.set r .eos))) s1 s3 3 :=
      Eval.iteT hr1 (Eval.seq e2 e3)
    have hbody : Eval main (consumeStep k T r (.push k' r)) s s3 4 := Eval.seq e1 hite
    have hexit : s3.reg r ≠ Glyph.eos := by simp [s3, s2, s1]
    have hloop : Eval main (consumeLoop k T r (.push k' r)) s3 s3 1 := Eval.loopF hexit
    have hmain : Eval main (consumeLoop k T r (.push k' r)) s s3 6 :=
      Eval.loopT hreg hbody hloop
    refine ⟨s3, 6, hmain, ?_, ?_, hexit, by simp, ?_, ?_⟩
    · simp [s3, s2, s1]
    · rw [hl']
      simpa [s3, s2, s1, Function.update_of_ne (Ne.symm hne)] using hstk'
    · intro j hj hj'
      simp [s3, s2, s1, Function.update_of_ne hj]
    · intro j hj
      simp [s3, s2, s1, Function.update_of_ne hj]
  | cons g gs' ih =>
    intro s hl hstk hstk' hreg
    have hgT : g ≠ T := hT g (by rw [hl]; simp)
    have hl' : l = (pre ++ [g]) ++ gs' := by rw [hl, List.append_assoc]; simp
    have hstk1 : s.stk k = g :: (gs' ++ T :: bk) := by simpa using hstk
    let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (gs' ++ T :: bk)⟩
    let s2 : State := ⟨s1.reg, Function.update s1.stk k' (s1.reg r :: s1.stk k')⟩
    let s3 : State := ⟨Function.update s2.reg r Glyph.eos, s2.stk⟩
    have e1 : Eval main (.pop k r) s s1 1 := Eval.pop_cons hstk1
    have hr1 : s1.reg r = g := by simp [s1]
    have e2 : Eval main (.push k' r) s1 s2 1 := by
      have h := Eval.push (main := main) k' r s1
      simpa [s2] using h
    have e3 : Eval main (.set r Glyph.eos) s2 s3 1 := by
      have h := Eval.set (main := main) r Glyph.eos s2
      simpa [s3] using h
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (.mk 0)))
        (.seq (.push k' r) (.set r .eos))) s1 s3 3 :=
      Eval.iteF (by rw [hr1]; exact hgT) (Eval.seq e2 e3)
    have hbody : Eval main (consumeStep k T r (.push k' r)) s s3 4 := Eval.seq e1 hite
    have hstk3 : s3.stk k = gs' ++ T :: bk := by
      simp only [s3, s2, s1]
      rw [Function.update_of_ne hne]
      exact Function.update_self k (gs' ++ T :: bk) s.stk
    have hstk3' : s3.stk k' = (pre ++ [g]).reverse ++ bk' := by
      simp only [s3, s2, s1]
      rw [Function.update_self, Function.update_self, Function.update_of_ne (Ne.symm hne),
        hstk']
      simp [List.reverse_append]
    have hreg3 : s3.reg r = Glyph.eos := by simp [s3]
    obtain ⟨s', n', hev', hk', hk'', hreg', hn', hfr', hrf'⟩ :=
      ih (pre ++ [g]) s3 hl' hstk3 hstk3' hreg3
    have hmain : Eval main (consumeLoop k T r (.push k' r)) s s' (4 + n' + 1) :=
      Eval.loopT hreg hbody hev'
    refine ⟨s', 4 + n' + 1, hmain, hk', hk'', hreg', ?_, ?_, ?_⟩
    · have hlen : (g :: gs').length = gs'.length + 1 := by simp
      omega
    · intro j hj hj'
      rw [hfr' j hj hj']
      simp only [s3, s2, s1]
      rw [Function.update_of_ne hj', Function.update_of_ne hj]
    · intro j hj
      rw [hrf' j hj]
      simp only [s3, s2, s1]
      rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- `consume k T r (.push k' r)` moves the region of `k` above the marker `T` onto `k'`, reversed,
leaving `T` on top of `k`; the other stacks and the registers other than `r` are untouched.
Cost `≤ 5 * l.length + 7`. -/
theorem consume_push_rev_regs (main : Cmd) (k : Stk) (T : Glyph) (k' : Stk) (r : Reg)
    (l bk bk' : List Glyph) (hne : k ≠ k') (hT : ∀ g ∈ l, g ≠ T) (s : State)
    (hk : s.stk k = l ++ T :: bk) (hk' : s.stk k' = bk') :
    ∃ s' n, Eval main (consume k T r (.push k' r)) s s' n ∧
      n ≤ 5 * l.length + 7 ∧
      s'.stk k = T :: bk ∧ s'.stk k' = l.reverse ++ bk' ∧
      (∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) ∧
      (∀ j : Reg, j ≠ r → s'.reg j = s.reg j) := by
  have h1 : Eval main (.set r Glyph.eos) s ⟨Function.update s.reg r Glyph.eos, s.stk⟩ 1 :=
    Eval.set_eq
  obtain ⟨s', n', hev', hk1, hk2, hreg', hn', hfr', hrf'⟩ :=
    consumeLoop_push_rev_regs main k T k' r hne bk bk' l hT [] l
      ⟨Function.update s.reg r Glyph.eos, s.stk⟩ (by simp) (by simpa using hk)
      (by simp [hk']) (by simp)
  refine ⟨s', 1 + n', Eval.seq h1 hev', by omega, hk1, hk2, hfr', ?_⟩
  intro j hj
  rw [hrf' j hj]
  simp [Function.update_of_ne hj]

/-- `mvRevOnto k T k' r` moves the region of stack `k` above its marker `T` onto stack `k'`,
reversed, then drops `T`, at cost at most `5 * l.length + 8`; it changes no register other than
`r`. -/
theorem mvRevOntoTight_regs (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (k' : HvdH.Stk)
    (r : HvdH.Reg) (l bk bk' : List HvdH.Glyph) (s : HvdH.State)
    (hT : ∀ g ∈ l, g ≠ T) (hk : s.stk k = l ++ T :: bk) (hk' : s.stk k' = bk')
    (hne : k ≠ k') :
    ∃ s' n, HvdH.Eval main (Work.IntLib.mvRevOnto k T k' r) s s' n ∧
      n ≤ 5 * l.length + 8 ∧
      s'.stk k = bk ∧ s'.stk k' = l.reverse ++ bk' ∧
      (∀ j : HvdH.Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) ∧
      (∀ j : HvdH.Reg, j ≠ r → s'.reg j = s.reg j) := by
  obtain ⟨s₁, n₁, hev₁, hn₁, hk₁, hk₁', hfr₁, hrf₁⟩ :=
    consume_push_rev_regs main k T k' r l bk bk' hne hT s hk hk'
  refine ⟨⟨Function.update s₁.reg r T, Function.update s₁.stk k bk⟩, n₁ + 1,
    Eval.seq hev₁ (Eval.pop_cons (main := main) hk₁), by omega, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [Function.update_of_ne (Ne.symm hne)] using hk₁'
  · intro j hj hj'
    simpa [Function.update_of_ne hj] using hfr₁ j hj hj'
  · intro j hj
    show (Function.update s₁.reg r T) j = s.reg j
    rw [Function.update_of_ne hj]
    exact hrf₁ j hj

theorem div_emit_eval (main : HvdH.Cmd) (sg : HvdH.Reg) (l bkX A : List HvdH.Glyph) (s : HvdH.State)
    (hX : s.stk Work.IntLib.Div.stX = l ++ Work.IntLib.gX :: bkX) (h0 : s.stk 0 = A)
    (hT : ∀ g ∈ l, g ≠ Work.IntLib.gX) (hne : Work.IntLib.Div.stX ≠ 0)
    (hsg : sg ≠ Work.IntLib.Div.rgT) :
    ∃ s' n, HvdH.Eval main (Work.IntLib.Div.emit sg) s s' n ∧
      n ≤ 5 * l.length + 15 ∧
      s'.stk 0 = s.reg sg :: (l.reverse ++ [HvdH.Glyph.iend] ++ A) ∧
      s'.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ bkX ∧
      ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.Div.stX → s'.stk j = s.stk j := by
  -- `set rgT iend`
  let s1 : State := ⟨Function.update s.reg Div.rgT Glyph.iend, s.stk⟩
  have hev1 : Eval main (.set Div.rgT Glyph.iend) s s1 1 := by
    have h := Eval.set (main := main) Div.rgT Glyph.iend s
    simpa [s1] using h
  have hr1 : s1.reg Div.rgT = Glyph.iend := by simp [s1]
  -- `push 0 rgT`
  let s2 : State := ⟨s1.reg, Function.update s1.stk 0 (Glyph.iend :: s1.stk 0)⟩
  have hev2 : Eval main (.push 0 Div.rgT) s1 s2 1 := by
    have h := Eval.push (main := main) (0 : Stk) Div.rgT s1
    simpa [s2, hr1] using h
  have h2stk : s2.stk 0 = Glyph.iend :: A := by simp [s2, s1, h0]
  have h2X : s2.stk Div.stX = l ++ gX :: bkX := by
    have h : s2.stk Div.stX = s1.stk Div.stX := by
      simp only [s2, Function.update_of_ne hne]
    rw [h]
    simpa [s1] using hX
  -- `mvRevOnto stX gX 0 rgT`
  obtain ⟨s3, n3, hev3, hn3, h3X, h30, hfr3, hrf3⟩ :=
    mvRevOntoTight_regs main Div.stX gX (0 : Stk) Div.rgT l bkX (Glyph.iend :: A) s2
      hT h2X h2stk hne
  -- `mkG stX gX` = `set rgT gX` ; `push stX rgT`
  let s4 : State := ⟨Function.update s3.reg Div.rgT gX, s3.stk⟩
  have hev4 : Eval main (.set Div.rgT gX) s3 s4 1 := by
    have h := Eval.set (main := main) Div.rgT gX s3
    simpa [s4] using h
  have hr4 : s4.reg Div.rgT = gX := by simp [s4]
  let s5 : State := ⟨s4.reg, Function.update s4.stk Div.stX (s4.reg Div.rgT :: s4.stk Div.stX)⟩
  have hev5 : Eval main (.push Div.stX Div.rgT) s4 s5 1 := by
    have h := Eval.push (main := main) Div.stX Div.rgT s4
    simpa [s5] using h
  have hevmk : Eval main (Div.mkG Div.stX gX) s3 s5 2 := by
    have h := Eval.seq hev4 hev5
    simpa [Div.mkG] using h
  have h5X : s5.stk Div.stX = gX :: bkX := by
    simp only [s5]
    rw [Function.update_self, hr4, show s4.stk Div.stX = bkX from h3X]
  have h50 : s5.stk 0 = s4.stk 0 := by
    simp only [s5, Function.update_of_ne (Ne.symm hne)]
  -- `mov rgT sg`
  let s6 : State := ⟨Function.update s5.reg Div.rgT (s5.reg sg), s5.stk⟩
  have hev6 : Eval main (.mov Div.rgT sg) s5 s6 1 := by
    have h := Eval.mov (main := main) Div.rgT sg s5
    simpa [s6] using h
  have hreg : s5.reg sg = s.reg sg := by
    have h2 : s4.reg sg = s3.reg sg := by
      show (Function.update s3.reg Div.rgT gX) sg = s3.reg sg
      exact Function.update_of_ne hsg _ _
    have h3 : s3.reg sg = s2.reg sg := hrf3 sg hsg
    have h5 : s1.reg sg = s.reg sg := by
      show (Function.update s.reg Div.rgT Glyph.iend) sg = s.reg sg
      exact Function.update_of_ne hsg _ _
    calc s5.reg sg = s4.reg sg := rfl
      _ = s3.reg sg := h2
      _ = s2.reg sg := h3
      _ = s1.reg sg := rfl
      _ = s.reg sg := h5
  have hr6 : s6.reg Div.rgT = s.reg sg := by
    show (Function.update s5.reg Div.rgT (s5.reg sg)) Div.rgT = s.reg sg
    rw [Function.update_self, hreg]
  -- `push 0 rgT`
  let s7 : State := ⟨s6.reg, Function.update s6.stk 0 (s6.reg Div.rgT :: s6.stk 0)⟩
  have hev7 : Eval main (.push 0 Div.rgT) s6 s7 1 := by
    have h := Eval.push (main := main) (0 : Stk) Div.rgT s6
    simpa [s7, hr6] using h
  have hev8 : Eval main .skip s7 s7 1 := Eval.skip s7
  -- assemble the six commands (plus the trailing `skip` of `seqs`)
  have hwhole : Eval main (Div.emit sg) s s7 (1 + (1 + (n3 + (2 + (1 + (1 + 1)))))) := by
    simp only [Div.emit, Div.seqs_cons, Div.seqs_nil]
    exact Eval.seq hev1
      (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hevmk (Eval.seq hev6 (Eval.seq hev7 hev8)))))
  -- the stack of stack 0 between the region move and the final push
  have h6stk0 : s6.stk 0 = l.reverse ++ Glyph.iend :: A := by
    show s5.stk 0 = l.reverse ++ Glyph.iend :: A
    rw [h50]
    show s4.stk 0 = l.reverse ++ Glyph.iend :: A
    exact h30
  -- the region of stack 8 between the `mkG` and the final push
  have h6stkX : s6.stk Div.stX = gX :: bkX := by
    show s5.stk Div.stX = gX :: bkX
    exact h5X
  refine ⟨s7, 1 + (1 + (n3 + (2 + (1 + (1 + 1))))), hwhole, by omega, ?_, ?_, ?_⟩
  · -- the value just written
    show (Function.update s6.stk 0 (s6.reg Div.rgT :: s6.stk 0)) 0 =
      s.reg sg :: (l.reverse ++ [Glyph.iend] ++ A)
    rw [Function.update_self, hr6, h6stk0]
    simp
  · -- the scratch region of stack 8 is restored
    show (Function.update s6.stk 0 (s6.reg Div.rgT :: s6.stk 0)) Div.stX = [gX] ++ bkX
    rw [Function.update_of_ne hne, h6stkX, List.singleton_append]
  · -- frame
    intro j hj hj'
    have e1 : s7.stk j = s6.stk j := Function.update_of_ne hj _ _
    have e2 : s6.stk j = s5.stk j := rfl
    have e3 : s5.stk j = s4.stk j := by simp only [s5, Function.update_of_ne hj']
    have e4 : s4.stk j = s3.stk j := rfl
    have e5 : s3.stk j = s2.stk j := hfr3 j hj' hj
    have e6 : s2.stk j = s1.stk j := by simp only [s2, Function.update_of_ne hj]
    have e7 : s1.stk j = s.stk j := rfl
    rw [e1, e2, e3, e4, e5, e6, e7]

end Work.IntLib
