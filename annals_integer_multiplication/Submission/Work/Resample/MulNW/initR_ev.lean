import Mathlib
import Submission.Work.Resample.MulNW.Defs

/-!
# `Work.Resample.MulNW.initR_ev`

`initRProg` initialises the remainder `ρ` of the schoolbook multiplier: it moves the `size a` bits
of `a` from `sA` to the scratch stack `sW` while pushing one zero bit into `sR` for each bit of
`a`, and then moves the bits back from `sW` to `sA`.  Hence `sA` ends exactly as it started, `sW`
is restored, and `sR` gains `size a` zero bits above its frame marker — with cost `O(size a)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Resample.MulNW

open HvdH

/-! ## The glyph-level all-false word -/

/-- the list of `m` false bits, as glyphs -/
abbrev zerosG (m : ℕ) : List Glyph := List.replicate m (Glyph.bit false)

theorem zerosG_succ (m : ℕ) : zerosG (m + 1) = Glyph.bit false :: zerosG m :=
  List.replicate_succ

theorem zerosG_length (m : ℕ) : (zerosG m).length = m := List.length_replicate

theorem bitsG_zeros (m : ℕ) : bitsG (zeros m) = zerosG m := by
  simp [zeros, zerosG, List.map_replicate]

theorem natBits_length (a : ℕ) : (natBits a).length = a.size := by
  simp [natBits, List.length_map, Nat.size_eq_bits_len]

/-! ## A `consumeLoop` that also pushes one false bit per glyph -/

/-- `consumeLoop k T r (.seq (.push k' r) (.push k'' rZ))`: move the region of `k` above the
marker `T` onto `k'` (reversed), pushing one `bit false` onto `k''` for every glyph moved.  Here
`l` is the whole region, `pre` the part already moved and `gs` the part still on `k`. -/
theorem consumeLoop_push2 (main : Cmd) (k : Stk) (T : Glyph) (k' k'' : Stk) (r rZ : Reg)
    (hne : k ≠ k') (hne2 : k ≠ k'') (hne' : k' ≠ k'') (hrz : rZ ≠ r)
    (bk bk' bk'' l : List Glyph) (hT : ∀ g ∈ l, g ≠ T) :
    ∀ (pre gs : List Glyph) (s : State), l = pre ++ gs → s.stk k = gs ++ T :: bk →
      s.stk k' = pre.reverse ++ bk' → s.stk k'' = zerosG pre.length ++ bk'' →
      s.reg r = Glyph.eos → s.reg rZ = Glyph.bit false →
      ∃ s' n,
        Eval main (Work.IntLib.consumeLoop k T r (.seq (.push k' r) (.push k'' rZ))) s s' n ∧
        n ≤ 6 + 6 * gs.length ∧ s'.stk k = T :: bk ∧ s'.stk k' = l.reverse ++ bk' ∧
        s'.stk k'' = zerosG l.length ++ bk'' ∧ s'.reg r ≠ Glyph.eos ∧
        (∀ j : Stk, j ≠ k → j ≠ k' → j ≠ k'' → s'.stk j = s.stk j) := by
  intro pre gs
  induction gs generalizing pre with
  | nil =>
    intro s hl hstk hstk' hstk'' hreg hregZ
    have hl' : l = pre := by rw [hl, List.append_nil]
    have hsk : s.stk k = T :: bk := by rw [hstk]; simp
    let s1 : State := ⟨Function.update s.reg r T, Function.update s.stk k bk⟩
    let s2 : State := ⟨s1.reg, Function.update s1.stk k (T :: s1.stk k)⟩
    let s3 : State := ⟨Function.update s2.reg r (Glyph.mk 0), s2.stk⟩
    have e1 : Eval main (.pop k r) s s1 1 := Work.IntLib.Eval.pop_cons hsk
    have hr1 : s1.reg r = T := by simp [s1]
    have e2 : Eval main (.push k r) s1 s2 1 := by
      have h := Eval.push (main := main) k r s1
      simpa [s2, hr1] using h
    have e3 : Eval main (.set r (Glyph.mk 0)) s2 s3 1 := by
      have h := Eval.set (main := main) r (Glyph.mk 0) s2
      simpa [s3] using h
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (Glyph.mk 0)))
        (.seq (.seq (.push k' r) (.push k'' rZ)) (.set r Glyph.eos))) s1 s3 3 :=
      Eval.iteT hr1 (Eval.seq e2 e3)
    have hbody : Eval main
        (Work.IntLib.consumeStep k T r (.seq (.push k' r) (.push k'' rZ))) s s3 4 :=
      Eval.seq e1 hite
    have hexit : s3.reg r ≠ Glyph.eos := by simp [s3, s2, s1]
    have hloop : Eval main
        (Work.IntLib.consumeLoop k T r (.seq (.push k' r) (.push k'' rZ))) s3 s3 1 :=
      Eval.loopF hexit
    have hmain : Eval main
        (Work.IntLib.consumeLoop k T r (.seq (.push k' r) (.push k'' rZ))) s s3 6 :=
      Eval.loopT hreg hbody hloop
    refine ⟨s3, 6, hmain, by simp, ?_, ?_, ?_, hexit, ?_⟩
    · simp [s3, s2, s1]
    · rw [hl']
      simpa [s3, s2, s1, Function.update_of_ne (Ne.symm hne)] using hstk'
    · rw [hl']
      simpa [s3, s2, s1, Function.update_of_ne (Ne.symm hne2)] using hstk''
    · intro j hj1 hj2 hj3
      simp [s3, s2, s1, Function.update_of_ne hj1]
  | cons g gs' ih =>
    intro s hl hstk hstk' hstk'' hreg hregZ
    have hgT : g ≠ T := hT g (by rw [hl]; simp)
    have hl' : l = (pre ++ [g]) ++ gs' := by rw [hl, List.append_assoc]; simp
    have hstk1 : s.stk k = g :: (gs' ++ T :: bk) := by simpa using hstk
    let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (gs' ++ T :: bk)⟩
    let s2 : State := ⟨s1.reg, Function.update s1.stk k' (s1.reg r :: s1.stk k')⟩
    let s3 : State := ⟨s2.reg, Function.update s2.stk k'' (s2.reg rZ :: s2.stk k'')⟩
    let s4 : State := ⟨Function.update s3.reg r Glyph.eos, s3.stk⟩
    have e1 : Eval main (.pop k r) s s1 1 := Work.IntLib.Eval.pop_cons hstk1
    have hr1 : s1.reg r = g := by simp [s1]
    have hs2Z : s2.reg rZ = Glyph.bit false := by
      simp only [s2, s1]
      rw [Function.update_of_ne hrz, hregZ]
    have e2 : Eval main (.push k' r) s1 s2 1 := by
      have h := Eval.push (main := main) k' r s1
      simpa [s2] using h
    have e3 : Eval main (.push k'' rZ) s2 s3 1 := by
      have h := Eval.push (main := main) k'' rZ s2
      simpa [s3] using h
    have e4 : Eval main (.set r Glyph.eos) s3 s4 1 := by
      have h := Eval.set (main := main) r Glyph.eos s3
      simpa [s4] using h
    have hne1 : s1.reg r ≠ T := by rw [hr1]; exact hgT
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (Glyph.mk 0)))
        (.seq (.seq (.push k' r) (.push k'' rZ)) (.set r Glyph.eos))) s1 s4 4 :=
      Eval.iteF hne1 (Eval.seq (Eval.seq e2 e3) e4)
    have hbody : Eval main
        (Work.IntLib.consumeStep k T r (.seq (.push k' r) (.push k'' rZ))) s s4 5 :=
      Eval.seq e1 hite
    have hs4k : s4.stk k = gs' ++ T :: bk := by
      simp only [s4, s3, s2, s1]
      rw [Function.update_of_ne hne2, Function.update_of_ne hne, Function.update_self]
    have hs4k' : s4.stk k' = (pre ++ [g]).reverse ++ bk' := by
      simp only [s4, s3, s2, s1]
      rw [Function.update_of_ne hne', Function.update_self, Function.update_self,
        Function.update_of_ne (Ne.symm hne), hstk']
      simp [List.reverse_append]
    have hs4k'' : s4.stk k'' = zerosG (pre ++ [g]).length ++ bk'' := by
      simp only [s4, s3, s2, s1]
      rw [Function.update_self, Function.update_of_ne hrz, hregZ,
        Function.update_of_ne (Ne.symm hne'), Function.update_of_ne (Ne.symm hne2), hstk'']
      rw [List.length_append, List.length_singleton, zerosG_succ]
      simp
    have hs4r : s4.reg r = Glyph.eos := by simp [s4]
    have hs4rZ : s4.reg rZ = Glyph.bit false := by
      simp only [s4, s3]
      rw [Function.update_of_ne hrz, hs2Z]
    have hs4oth : ∀ j : Stk, j ≠ k → j ≠ k' → j ≠ k'' → s4.stk j = s.stk j := by
      intro j hj1 hj2 hj3
      simp only [s4, s3, s2, s1]
      rw [Function.update_of_ne hj3, Function.update_of_ne hj2, Function.update_of_ne hj1]
    obtain ⟨s', n', hev', hn', hk', hk'', hk''', hreg', hfr'⟩ :=
      ih (pre ++ [g]) s4 hl' hs4k hs4k' hs4k'' hs4r hs4rZ
    have hmain : Eval main
        (Work.IntLib.consumeLoop k T r (.seq (.push k' r) (.push k'' rZ))) s s' (5 + n' + 1) :=
      Eval.loopT hreg hbody hev'
    refine ⟨s', 5 + n' + 1, hmain, ?_, hk', hk'', hk''', hreg', ?_⟩
    · have hlen : (g :: gs').length = gs'.length + 1 := by simp
      omega
    · intro j hj1 hj2 hj3
      rw [hfr' j hj1 hj2 hj3]
      simp only [s4, s3, s2, s1]
      rw [Function.update_of_ne hj3, Function.update_of_ne hj2, Function.update_of_ne hj1]

/-- `consume k T r (.push k' r)`: move the region of `k` above the marker `T` onto `k'`, reversed,
leaving `T` on top of `k`; the other stacks are untouched. -/
theorem consumeLoop_push1 (main : Cmd) (k : Stk) (T : Glyph) (k' : Stk) (r : Reg)
    (hne : k ≠ k') (bk bk' l : List Glyph) (hT : ∀ g ∈ l, g ≠ T) :
    ∀ (pre gs : List Glyph) (s : State), l = pre ++ gs → s.stk k = gs ++ T :: bk →
      s.stk k' = pre.reverse ++ bk' → s.reg r = Glyph.eos →
      ∃ s' n, Eval main (Work.IntLib.consumeLoop k T r (.push k' r)) s s' n ∧
        n ≤ 6 + 6 * gs.length ∧ s'.stk k = T :: bk ∧ s'.stk k' = l.reverse ++ bk' ∧
        s'.reg r ≠ Glyph.eos ∧
        (∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) := by
  intro pre gs
  induction gs generalizing pre with
  | nil =>
    intro s hl hstk hstk' hreg
    have hl' : l = pre := by rw [hl, List.append_nil]
    have hsk : s.stk k = T :: bk := by rw [hstk]; simp
    let s1 : State := ⟨Function.update s.reg r T, Function.update s.stk k bk⟩
    let s2 : State := ⟨s1.reg, Function.update s1.stk k (T :: s1.stk k)⟩
    let s3 : State := ⟨Function.update s2.reg r (Glyph.mk 0), s2.stk⟩
    have e1 : Eval main (.pop k r) s s1 1 := Work.IntLib.Eval.pop_cons hsk
    have hr1 : s1.reg r = T := by simp [s1]
    have e2 : Eval main (.push k r) s1 s2 1 := by
      have h := Eval.push (main := main) k r s1
      simpa [s2, hr1] using h
    have e3 : Eval main (.set r (Glyph.mk 0)) s2 s3 1 := by
      have h := Eval.set (main := main) r (Glyph.mk 0) s2
      simpa [s3] using h
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (Glyph.mk 0)))
        (.seq (.push k' r) (.set r Glyph.eos))) s1 s3 3 :=
      Eval.iteT hr1 (Eval.seq e2 e3)
    have hbody : Eval main (Work.IntLib.consumeStep k T r (.push k' r)) s s3 4 :=
      Eval.seq e1 hite
    have hexit : s3.reg r ≠ Glyph.eos := by simp [s3, s2, s1]
    have hloop : Eval main (Work.IntLib.consumeLoop k T r (.push k' r)) s3 s3 1 :=
      Eval.loopF hexit
    have hmain : Eval main (Work.IntLib.consumeLoop k T r (.push k' r)) s s3 6 :=
      Eval.loopT hreg hbody hloop
    refine ⟨s3, 6, hmain, by simp, ?_, ?_, hexit, ?_⟩
    · simp [s3, s2, s1]
    · rw [hl']
      simpa [s3, s2, s1, Function.update_of_ne (Ne.symm hne)] using hstk'
    · intro j hj1 hj2
      simp [s3, s2, s1, Function.update_of_ne hj1]
  | cons g gs' ih =>
    intro s hl hstk hstk' hreg
    have hgT : g ≠ T := hT g (by rw [hl]; simp)
    have hl' : l = (pre ++ [g]) ++ gs' := by rw [hl, List.append_assoc]; simp
    have hstk1 : s.stk k = g :: (gs' ++ T :: bk) := by simpa using hstk
    let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (gs' ++ T :: bk)⟩
    let s2 : State := ⟨s1.reg, Function.update s1.stk k' (s1.reg r :: s1.stk k')⟩
    let s3 : State := ⟨Function.update s2.reg r Glyph.eos, s2.stk⟩
    have e1 : Eval main (.pop k r) s s1 1 := Work.IntLib.Eval.pop_cons hstk1
    have hr1 : s1.reg r = g := by simp [s1]
    have e2 : Eval main (.push k' r) s1 s2 1 := by
      have h := Eval.push (main := main) k' r s1
      simpa [s2] using h
    have e3 : Eval main (.set r Glyph.eos) s2 s3 1 := by
      have h := Eval.set (main := main) r Glyph.eos s2
      simpa [s3] using h
    have hne1 : s1.reg r ≠ T := by rw [hr1]; exact hgT
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (Glyph.mk 0)))
        (.seq (.push k' r) (.set r Glyph.eos))) s1 s3 3 :=
      Eval.iteF hne1 (Eval.seq e2 e3)
    have hbody : Eval main (Work.IntLib.consumeStep k T r (.push k' r)) s s3 4 :=
      Eval.seq e1 hite
    have hs3k : s3.stk k = gs' ++ T :: bk := by
      simp only [s3, s2, s1]
      rw [Function.update_of_ne hne, Function.update_self]
    have hs3k' : s3.stk k' = (pre ++ [g]).reverse ++ bk' := by
      simp only [s3, s2, s1]
      rw [Function.update_self, Function.update_self, Function.update_of_ne (Ne.symm hne), hstk']
      simp [List.reverse_append]
    have hs3r : s3.reg r = Glyph.eos := by simp [s3]
    have hs3oth : ∀ j : Stk, j ≠ k → j ≠ k' → s3.stk j = s.stk j := by
      intro j hj1 hj2
      simp only [s3, s2, s1]
      rw [Function.update_of_ne hj2, Function.update_of_ne hj1]
    obtain ⟨s', n', hev', hn', hk', hk'', hreg', hfr'⟩ :=
      ih (pre ++ [g]) s3 hl' hs3k hs3k' hs3r
    have hmain : Eval main (Work.IntLib.consumeLoop k T r (.push k' r)) s s' (4 + n' + 1) :=
      Eval.loopT hreg hbody hev'
    refine ⟨s', 4 + n' + 1, hmain, ?_, hk', hk'', hreg', ?_⟩
    · have hlen : (g :: gs').length = gs'.length + 1 := by simp
      omega
    · intro j hj1 hj2
      rw [hfr' j hj1 hj2]
      simp only [s3, s2, s1]
      rw [Function.update_of_ne hj2, Function.update_of_ne hj1]

/-! ## The two `consume`s of `initRProg` -/

/-- `consume k T r (.seq (.push k' r) (.push k'' rZ))` with the initialising `set`. -/
theorem consume_push2 (main : Cmd) (k : Stk) (T : Glyph) (k' k'' : Stk) (r rZ : Reg)
    (hne : k ≠ k') (hne2 : k ≠ k'') (hne' : k' ≠ k'') (hrz : rZ ≠ r)
    (bk bk' bk'' l : List Glyph) (hT : ∀ g ∈ l, g ≠ T) (s : State)
    (hstk : s.stk k = l ++ T :: bk) (hstk' : s.stk k' = bk') (hstk'' : s.stk k'' = bk'')
    (hrZ : s.reg rZ = Glyph.bit false) :
    ∃ s' n, Eval main (Work.IntLib.consume k T r (.seq (.push k' r) (.push k'' rZ))) s s' n ∧
      n ≤ 6 * l.length + 7 ∧ s'.stk k = T :: bk ∧ s'.stk k' = l.reverse ++ bk' ∧
      s'.stk k'' = zerosG l.length ++ bk'' ∧
      (∀ j : Stk, j ≠ k → j ≠ k' → j ≠ k'' → s'.stk j = s.stk j) := by
  let s1 : State := ⟨Function.update s.reg r Glyph.eos, s.stk⟩
  have hset : Eval main (.set r Glyph.eos) s s1 1 := Work.IntLib.Eval.set_eq
  have hr1 : s1.reg r = Glyph.eos := by simp [s1]
  have hrZ1 : s1.reg rZ = Glyph.bit false := by
    simp only [s1]
    rw [Function.update_of_ne hrz, hrZ]
  have hs1k : s1.stk k = l ++ T :: bk := by simpa [s1] using hstk
  have hs1k' : s1.stk k' = bk' := by simpa [s1] using hstk'
  have hs1k'' : s1.stk k'' = bk'' := by simpa [s1] using hstk''
  obtain ⟨s', n, hev, hn, hk, hk', hk'', hreg, hfr⟩ :=
    consumeLoop_push2 main k T k' k'' r rZ hne hne2 hne' hrz bk bk' bk'' l hT
      [] l s1 (by simp) hs1k hs1k' hs1k'' hr1 hrZ1
  refine ⟨s', 1 + n, Eval.seq hset hev, ?_, hk, hk', hk'', ?_⟩
  · omega
  · intro j hj1 hj2 hj3
    simpa [s1] using hfr j hj1 hj2 hj3

/-- `consume k T r (.push k' r)` with the initialising `set`. -/
theorem consume_push1 (main : Cmd) (k : Stk) (T : Glyph) (k' : Stk) (r : Reg)
    (hne : k ≠ k') (bk bk' l : List Glyph) (hT : ∀ g ∈ l, g ≠ T) (s : State)
    (hstk : s.stk k = l ++ T :: bk) (hstk' : s.stk k' = bk') :
    ∃ s' n, Eval main (Work.IntLib.consume k T r (.push k' r)) s s' n ∧
      n ≤ 6 * l.length + 7 ∧ s'.stk k = T :: bk ∧ s'.stk k' = l.reverse ++ bk' ∧
      (∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) := by
  let s1 : State := ⟨Function.update s.reg r Glyph.eos, s.stk⟩
  have hset : Eval main (.set r Glyph.eos) s s1 1 := Work.IntLib.Eval.set_eq
  have hr1 : s1.reg r = Glyph.eos := by simp [s1]
  obtain ⟨s', n, hev, hn, hk, hk', hneq, hfr⟩ :=
    consumeLoop_push1 main k T k' r hne bk bk' l hT [] l s1 (by simp)
      (by simpa [s1] using hstk) (by simpa [s1] using hstk') hr1
  refine ⟨s', 1 + n, Eval.seq hset hev, ?_, hk, hk', ?_⟩
  · omega
  · intro j hj1 hj2
    simpa [s1] using hfr j hj1 hj2

/-! ## The phase lemma -/

theorem initR_ev (main : HvdH.Cmd) (a : ℕ) : Work.Resample.MulNW.InitRSpec main a := by
  intro bkA bkW bkR s hA hW hR
  let s0 : State := ⟨Function.update s.reg rZ (Glyph.bit false), s.stk⟩
  have e0 : Eval main (.set rZ (Glyph.bit false)) s s0 1 := Work.IntLib.Eval.set_eq
  have hrZ0 : s0.reg rZ = Glyph.bit false := by simp [s0]
  have hs0 : ∀ j : Stk, s0.stk j = s.stk j := fun j => by simp [s0]
  have hTnat : ∀ g ∈ natBits a, g ≠ mkA := fun g hg => bitsG_ne_mkA a.bits g hg 1
  obtain ⟨s1, n1, he1, hn1, hk1, hk1', hk1'', hfr1⟩ :=
    consume_push2 main sA mkA sW sR rL rZ (by decide) (by decide) (by decide) (by decide)
      bkA (mkW :: bkW) bkR (natBits a) hTnat s0 (by simpa [s0] using hA)
      (by simpa [s0] using hW) (by simpa [s0] using hR) hrZ0
  have hTrev : ∀ g ∈ (natBits a).reverse, g ≠ mkW :=
    fun g hg => bitsG_ne_mkA a.bits g (List.mem_reverse.mp hg) 7
  obtain ⟨s2, n2, he2, hn2, hk2, hk2', hfr2⟩ :=
    consume_push1 main sW mkW sA rL (by decide) bkW (mkA :: bkA) (natBits a).reverse hTrev
      s1 hk1' hk1
  refine ⟨s2, 1 + (n1 + n2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc1 : Eval main
        (Work.IntLib.consume sA mkA rL (Work.IntLib.MulS.seqs [.push sW rL, .push sR rZ]))
        s0 s1 n1 := by
      simpa [Work.IntLib.MulS.seqs] using he1
    have h := Eval.seq e0 (Eval.seq hc1 he2)
    simpa [initRProg, Work.IntLib.MulS.seqs] using h
  · have h1 : n1 ≤ 6 * a.size + 7 := by rw [natBits_length] at hn1; exact hn1
    have h2 : n2 ≤ 6 * a.size + 7 := by
      have h := hn2
      rw [List.length_reverse, natBits_length] at h
      exact h
    omega
  · rw [hk2', List.reverse_reverse]
  · exact hk2
  · have h1 : s2.stk sR = s1.stk sR := hfr2 sR (by decide) (by decide)
    rw [h1, hk1'', natBits_length]
    simp [bitsG_zeros]
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨hjA, hjR, hjW⟩ := hj
    rw [hfr2 j hjW hjA, hfr1 j hjA hjW hjR, hs0 j]

end Work.Resample.MulNW
