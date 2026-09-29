import Mathlib
import Submission.Work.Resample.MulNW.Defs

/-!
# `Work.Resample.MulNW`: the serial multiplier loop

`mainLoopProg` consumes the bits of `b` one by one; each iteration adds `(β ? a : 0)` to the running
remainder `ρ` (with the inner phase `addAProg`, whose specification `AddASpec` is taken as a
hypothesis) and emits the low bit of the sum on `sC`.  The invariant is expressed with the
arithmetic layer's `run α bs acc ρ`, so that `run_spec`/`run_final_val` give the value of the
product at the end.

The phase lemma `mainLoop_ev` is stated for a program `main` and a proof `haddA : AddASpec main` of
the inner phase; the assembly instantiates `haddA` with `Work.Resample.MulNW.addA_ev`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Resample.MulNW

open HvdH
open Work.IntLib.MulS (Ev ev_pop ev_push ev_set ev_mov)

/-! ## A `snoc` lemma for `run`, and the empty run -/

theorem run_snoc (α : List Bool) (b : Bool) (bs acc ρ : List Bool) :
    run α (bs ++ [b]) acc ρ =
      ((stepR α (run α bs acc ρ).2 b).1 :: (run α bs acc ρ).1,
        (stepR α (run α bs acc ρ).2 b).2) := by
  induction bs generalizing acc ρ with
  | nil => simp only [List.nil_append, run_cons, run_nil]
  | cons b₀ bs ih =>
      simp only [List.cons_append, run_cons, ih]

theorem run_nil_fst (α ρ : List Bool) : (run α [] [] ρ).1 = [] := rfl

theorem zeros_length (a : ℕ) : (zeros a.size).length = a.bits.length := by
  rw [zeros, List.length_replicate, Nat.size_eq_bits_len]

/-! ## The loop -/

theorem mainLoop_aux (main : Cmd) (haddA : AddASpec main) (a : ℕ) (bs : List Bool)
    (bkA bkB bkR bkC bkW bkT : List Glyph) :
    ∀ (pre rest : List Bool) (s : State), bs = pre ++ rest →
      s.stk sB = bitsG rest ++ mkB :: bkB →
      s.stk sR = bitsG ((run a.bits pre [] (zeros a.size)).2) ++ mkR :: bkR →
      s.stk sC = bitsG ((run a.bits pre [] (zeros a.size)).1) ++ mkC :: bkC →
      s.stk sA = natBits a ++ mkA :: bkA →
      s.stk sW = mkW :: bkW → s.stk sT = mkT :: bkT → s.reg rL = Glyph.eos →
      ∃ (s' : State) (n : ℕ), Eval main (consumeLoop sB mkB rL mainBody) s s' n ∧
        n ≤ (rest.length + 1) * (40 * (a.size + 2) + 23) ∧
        s'.stk sB = mkB :: bkB ∧
        s'.stk sR = bitsG ((run a.bits bs [] (zeros a.size)).2) ++ mkR :: bkR ∧
        s'.stk sC = bitsG ((run a.bits bs [] (zeros a.size)).1) ++ mkC :: bkC ∧
        s'.stk sA = natBits a ++ mkA :: bkA ∧
        s'.stk sW = mkW :: bkW ∧ s'.stk sT = mkT :: bkT ∧ s'.reg rL ≠ Glyph.eos := by
  intro pre rest s
  induction rest generalizing pre s with
  | nil =>
      intro hbs hB hR hC hA hW hT hrL
      rw [List.append_nil] at hbs
      subst hbs
      have hB0 : s.stk sB = mkB :: bkB := by simpa using hB
      -- pop the marker
      let s1 : State := ⟨Function.update s.reg rL ((s.stk sB).headD Glyph.eos),
        Function.update s.stk sB (s.stk sB).tail⟩
      have e1 : Ev main (.pop sB rL) s s1 1 := ev_pop main sB rL s
      have hfr1 : ∀ k : Stk, k ≠ sB → s1.stk k = s.stk k :=
        fun k hk => Ev.frame e1 (S := ({sB} : Finset Stk)) (by decide) (by simpa using hk)
      have hrL1 : s1.reg rL = mkB := by
        show Function.update s.reg rL ((s.stk sB).headD Glyph.eos) rL = mkB
        rw [Function.update_apply]
        simp [hB0]
      have hs1B : s1.stk sB = bkB := by
        show Function.update s.stk sB ((s.stk sB).tail) sB = bkB
        rw [Function.update_apply]
        simp [hB0]
      -- push the marker back
      let s2 : State := ⟨s1.reg, Function.update s1.stk sB (s1.reg rL :: s1.stk sB)⟩
      have hs2B : s2.stk sB = mkB :: bkB := by
        show Function.update s1.stk sB (s1.reg rL :: s1.stk sB) sB = mkB :: bkB
        rw [Function.update_apply]
        simp [hrL1, hs1B]
      have hfr2 : ∀ k : Stk, k ≠ sB → s2.stk k = s1.stk k :=
        fun k hk => by
          show Function.update s1.stk sB (s1.reg rL :: s1.stk sB) k = s1.stk k
          exact Function.update_of_ne hk _ _
      have e2 : Ev main (.push sB rL) s1 s2 1 := ev_push main sB rL s1
      -- stop the loop
      let s2b : State := ⟨Function.update s2.reg rL (Glyph.mk 0), s2.stk⟩
      have e3 : Ev main (.set rL (Glyph.mk 0)) s2 s2b 1 := ev_set main rL (Glyph.mk 0) s2
      have hrg2 : s2b.reg rL = Glyph.mk 0 := by
        show Function.update s2.reg rL (Glyph.mk 0) rL = Glyph.mk 0
        rw [Function.update_apply]; simp
      have hfr2b : ∀ k : Stk, s2b.stk k = s2.stk k := fun k => rfl
      have hite : Ev main
          (.ite rL mkB (.seq (.push sB rL) (.set rL (Glyph.mk 0)))
            (.seq mainBody (.set rL Glyph.eos))) s1 s2b 3 :=
        Ev.iteT hrL1 (Ev.seq e2 e3)
      have ebody : Ev main (Work.IntLib.consumeStep sB mkB rL mainBody) s s2b 4 := Ev.seq e1 hite
      have hexit : s2b.reg rL ≠ Glyph.eos := by rw [hrg2]; decide
      have eloop : Ev main (consumeLoop sB mkB rL mainBody) s2b s2b 1 := Ev.loopF hexit
      obtain ⟨n, hev, hn⟩ := Ev.loopT hrL ebody eloop
      have hs2bB : s2b.stk sB = mkB :: bkB := by
        show s2.stk sB = mkB :: bkB
        exact hs2B
      have hs2bR : s2b.stk sR = s.stk sR := by
        rw [hfr2b sR, hfr2 sR (by decide), hfr1 sR (by decide)]
      have hs2bC : s2b.stk sC = s.stk sC := by
        rw [hfr2b sC, hfr2 sC (by decide), hfr1 sC (by decide)]
      have hs2bA : s2b.stk sA = s.stk sA := by
        rw [hfr2b sA, hfr2 sA (by decide), hfr1 sA (by decide)]
      have hs2bW : s2b.stk sW = s.stk sW := by
        rw [hfr2b sW, hfr2 sW (by decide), hfr1 sW (by decide)]
      have hs2bT : s2b.stk sT = s.stk sT := by
        rw [hfr2b sT, hfr2 sT (by decide), hfr1 sT (by decide)]
      exact ⟨s2b, n, hev, by
          simp only [List.length_nil, Nat.add_zero, Nat.one_mul]
          omega,
        hs2bB, by rw [hs2bR, hR], by rw [hs2bC, hC], by rw [hs2bA, hA],
        by rw [hs2bW, hW], by rw [hs2bT, hT], by rw [hrg2]; decide⟩
  | cons β rest' ih =>
      intro hbs hB hR hC hA hW hT hrL
      have hB0 : s.stk sB = Glyph.bit β :: (bitsG rest' ++ mkB :: bkB) := by
        rw [hB, bitsG_cons, List.cons_append]
      -- pop the bit
      let s1 : State := ⟨Function.update s.reg rL ((s.stk sB).headD Glyph.eos),
        Function.update s.stk sB (s.stk sB).tail⟩
      have e1 : Ev main (.pop sB rL) s s1 1 := ev_pop main sB rL s
      have hfr1 : ∀ k : Stk, k ≠ sB → s1.stk k = s.stk k :=
        fun k hk => Ev.frame e1 (S := ({sB} : Finset Stk)) (by decide) (by simpa using hk)
      have hrL1 : s1.reg rL = Glyph.bit β := by
        show Function.update s.reg rL ((s.stk sB).headD Glyph.eos) rL = Glyph.bit β
        rw [Function.update_apply]
        simp [hB0]
      have hs1B : s1.stk sB = bitsG rest' ++ mkB :: bkB := by
        show Function.update s.stk sB ((s.stk sB).tail) sB = bitsG rest' ++ mkB :: bkB
        rw [Function.update_apply]
        simp [hB0]
      -- `mov rBit rL`
      let s2 : State := ⟨Function.update s1.reg rBit (s1.reg rL), s1.stk⟩
      have e2 : Ev main (.mov rBit rL) s1 s2 1 := ev_mov main rBit rL s1
      have hbit2 : s2.reg rBit = Glyph.bit β := by
        show Function.update s1.reg rBit (s1.reg rL) rBit = Glyph.bit β
        rw [Function.update_apply]; simp [hrL1]
      have hfr2 : ∀ k : Stk, s2.stk k = s1.stk k := fun k => rfl
      -- the inner phase
      have hρlen : ((run a.bits pre [] (zeros a.size)).2).length = a.bits.length :=
        (Work.IntLib.MulS.run_spec a.bits pre [] (zeros a.size) (zeros_length a)).2.2
      obtain ⟨s3, n3, e3, hn3, hA3, hR3, hC3, hW3, hT3, hfr3⟩ :=
        haddA a.bits (run a.bits pre [] (zeros a.size)).2 β bkA bkR bkW bkT s2 hρlen
          (by rw [hfr2 sA, hfr1 sA (by decide)]; exact hA)
          (by rw [hfr2 sR, hfr1 sR (by decide)]; exact hR)
          (by rw [hfr2 sW, hfr1 sW (by decide)]; exact hW)
          (by rw [hfr2 sT, hfr1 sT (by decide)]; exact hT) hbit2
      have hn3' : n3 ≤ 30 * (a.size + 2) := by
        have h := hn3
        rw [Nat.size_eq_bits_len a] at h
        exact h
      have hmovAdd : Ev main mainBody s1 s3 (30 * (a.size + 2) + 2) := by
        have h := Ev.seq e2 (⟨n3, e3, hn3'⟩ : Ev main addAProg s2 s3 (30 * (a.size + 2)))
        exact h.mono (by omega)
      -- `set rL eos`
      let s4 : State := ⟨Function.update s3.reg rL Glyph.eos, s3.stk⟩
      have e4 : Ev main (.set rL Glyph.eos) s3 s4 1 := ev_set main rL Glyph.eos s3
      have hrL4 : s4.reg rL = Glyph.eos := by
        show Function.update s3.reg rL Glyph.eos rL = Glyph.eos
        rw [Function.update_apply]; simp
      have hfr4 : ∀ k : Stk, s4.stk k = s3.stk k := fun k => rfl
      have h234 : Ev main (.seq mainBody (.set rL Glyph.eos)) s1 s4 (30 * (a.size + 2) + 3) := by
        have h := Ev.seq hmovAdd e4
        exact h.mono (by omega)
      have hneB : s1.reg rL ≠ mkB := by
        rw [hrL1]
        exact bit_ne_mk β 2
      have hite : Ev main
          (.ite rL mkB (.seq (.push sB rL) (.set rL (Glyph.mk 0)))
            (.seq mainBody (.set rL Glyph.eos))) s1 s4 (30 * (a.size + 2) + 5) := by
        have h := Ev.iteF (p := .seq (.push sB rL) (.set rL (Glyph.mk 0))) hneB h234
        exact h.mono (by omega)
      have hbody : Ev main (Work.IntLib.consumeStep sB mkB rL mainBody) s s4
          (40 * (a.size + 2) + 22) := by
        have h := Ev.seq e1 hite
        exact h.mono (by omega)
      -- state facts for the induction hypothesis
      have hs4B : s4.stk sB = bitsG rest' ++ mkB :: bkB := by
        rw [hfr4 sB, hfr3 sB (by decide), hfr2 sB]
        exact hs1B
      have hs4R : s4.stk sR
          = bitsG ((run a.bits (pre ++ [β]) [] (zeros a.size)).2) ++ mkR :: bkR := by
        rw [hfr4 sR, hR3, run_snoc]
      have hC2 : s2.stk sC = s.stk sC := by rw [hfr2 sC, hfr1 sC (by decide)]
      have hs4C : s4.stk sC
          = bitsG ((run a.bits (pre ++ [β]) [] (zeros a.size)).1) ++ mkC :: bkC := by
        rw [hfr4 sC, hC3, hC2, hC, run_snoc]
        simp
      have hs4A : s4.stk sA = natBits a ++ mkA :: bkA := by
        rw [hfr4 sA, hA3]
      have hs4W : s4.stk sW = mkW :: bkW := by
        rw [hfr4 sW, hW3]
      have hs4T : s4.stk sT = mkT :: bkT := by
        rw [hfr4 sT, hT3]
      have hbs4 : bs = (pre ++ [β]) ++ rest' := by
        rw [hbs, List.append_assoc, List.singleton_append]
      obtain ⟨s5, n5, e5, hn5, hB5, hR5, hC5, hA5, hW5, hT5, hne5⟩ :=
        ih (pre ++ [β]) s4 hbs4 hs4B hs4R hs4C hs4A hs4W hs4T hrL4
      obtain ⟨n, hev, hn⟩ := Ev.loopT hrL hbody
        (⟨n5, e5, hn5⟩ : Ev main (consumeLoop sB mkB rL mainBody) s4 s5
          ((rest'.length + 1) * (40 * (a.size + 2) + 23)))
      refine ⟨s5, n, hev, ?_, hB5, hR5, hC5, hA5, hW5, hT5, hne5⟩
      have hn5' : n5 ≤ (rest'.length + 1) * (40 * (a.size + 2) + 23) := hn5
      have hbodyC : 40 * (a.size + 2) + 22 ≤ 40 * (a.size + 2) + 23 := by omega
      rw [List.length_cons]
      nlinarith [hn, hn5', Nat.zero_le rest'.length, Nat.zero_le a.size]

theorem mainLoop_ev (main : Cmd) (haddA : AddASpec main) (a b : ℕ) : MainLoopSpec main a b := by
  intro bkA bkB bkR bkC bkW bkT s hA hB hR hC hW hT
  let s0 : State := s.updReg rL Glyph.eos
  have e0 : Ev main (.set rL Glyph.eos) s s0 1 := by
    have h := ev_set main rL Glyph.eos s
    have hst0 : (⟨Function.update s.reg rL Glyph.eos, s.stk⟩ : State) = s0 := by
      simp only [s0, State.updReg]
    rw [hst0] at h
    exact h
  have hrL0 : s0.reg rL = Glyph.eos := by
    show Function.update s.reg rL Glyph.eos rL = Glyph.eos
    rw [Function.update_apply]; simp
  have hA0 : s0.stk sA = natBits a ++ mkA :: bkA := by
    show s.stk sA = natBits a ++ mkA :: bkA
    exact hA
  have hB0 : s0.stk sB = bitsG b.bits ++ mkB :: bkB := by
    show s.stk sB = bitsG b.bits ++ mkB :: bkB
    exact hB
  have hR0 : s0.stk sR = bitsG ((run a.bits [] [] (zeros a.size)).2) ++ mkR :: bkR := by
    show s.stk sR = bitsG ((run a.bits [] [] (zeros a.size)).2) ++ mkR :: bkR
    rw [hR, run_nil]
  have hC0 : s0.stk sC = bitsG ((run a.bits [] [] (zeros a.size)).1) ++ mkC :: bkC := by
    show s.stk sC = bitsG ((run a.bits [] [] (zeros a.size)).1) ++ mkC :: bkC
    rw [hC, run_nil]
    rfl
  have hW0 : s0.stk sW = mkW :: bkW := by
    show s.stk sW = mkW :: bkW
    exact hW
  have hT0 : s0.stk sT = mkT :: bkT := by
    show s.stk sT = mkT :: bkT
    exact hT
  obtain ⟨s1, n1, e1, hn1, hB1, hR1, hC1, hA1, hW1, hT1, -⟩ :=
    mainLoop_aux main haddA a b.bits bkA bkB bkR bkC bkW bkT [] b.bits s0 (by simp) hB0 hR0 hC0
      hA0 hW0 hT0 hrL0
  obtain ⟨n, hev, hn⟩ := Ev.seq e0 (⟨n1, e1, hn1⟩ : Ev main (consumeLoop sB mkB rL mainBody) s0 s1
      ((b.bits.length + 1) * (40 * (a.size + 2) + 23)))
  have hsub : Work.IntLib.MulS.cmdTouches mainLoopProg ⊆
      ({sA, sB, sC, sR, sT, sW} : Finset Stk) := by decide
  refine ⟨s1, n, by simpa [mainLoopProg, Work.IntLib.consume, Work.IntLib.consumeLoop] using hev,
    ?_, hB1, hR1, hC1, hA1, hW1, hT1, ?_⟩
  · have hb : b.bits.length = b.size := Nat.size_eq_bits_len b
    have hn1' : n1 ≤ (b.size + 1) * (40 * (a.size + 2) + 23) := by
      have h := hn1
      rw [hb] at h
      exact h
    nlinarith [hn, hn1', Nat.zero_le a.size, Nat.zero_le b.size]
  · intro j hj
    exact Work.IntLib.MulS.Eval.stk_frame hev (fun hc => hj (hsub hc))

end Work.Resample.MulNW
