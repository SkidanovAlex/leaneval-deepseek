import Mathlib
import Submission.Work.Resample.MulNW.Defs
import Submission.Work.Kernel.Raw

/-!
# `Work.Resample.MulNW`: the straight-line phases of the multiplication word

* `open_ev`  : `openProg` pushes the eight frame markers (and sets two constant registers);
* `close_ev` : `closeProg` pops the markers, restoring the scratch stacks.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

namespace Work.Resample.MulNW

open HvdH

/-! ## Pushing a list of markers -/

/-- `markPush r l` sets `r` to each first component of `l` in turn and pushes it on the second
component: every stack of `l` (assumed distinct) gains its marker, nothing else is touched. -/
theorem ev_markPush (main : Cmd) (r : Reg) (l : List (Glyph × Stk)) (s : State)
    (hnd : (l.map Prod.snd).Nodup) :
    ∃ (s' : State) (n : ℕ), Eval main (markPush r l) s s' n ∧ n ≤ 2 * l.length + 1 ∧
      (∀ p ∈ l, s'.stk p.2 = p.1 :: s.stk p.2) ∧
      (∀ j : Stk, (∀ p ∈ l, j ≠ p.2) → s'.stk j = s.stk j) := by
  induction l generalizing s with
  | nil => exact ⟨s, 1, Eval.skip s, by simp, by intro p hp; simp at hp, by intro j _; rfl⟩
  | cons q l' ih =>
      obtain ⟨g, k⟩ := q
      have hnd2 : (k :: l'.map Prod.snd).Nodup := by simpa using hnd
      obtain ⟨hknot, hnd'⟩ := List.nodup_cons.mp hnd2
      have hgs : Function.update s.reg r g r = g := Function.update_self r g s.reg
      let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (g :: s.stk k)⟩
      have e1 : Eval main (.set r g) s ⟨Function.update s.reg r g, s.stk⟩ 1 :=
        Eval.set (main := main) r g s
      have e2 : Eval main (.push k r) ⟨Function.update s.reg r g, s.stk⟩ s1 1 := by
        have h := Eval.push (main := main) k r (⟨Function.update s.reg r g, s.stk⟩ : State)
        simpa [hgs] using h
      have e12 : Eval main (.seq (.set r g) (.push k r)) s s1 2 := Eval.seq e1 e2
      have hs1k : s1.stk k = g :: s.stk k := by
        show Function.update s.stk k (g :: s.stk k) k = g :: s.stk k
        exact Function.update_self k (g :: s.stk k) s.stk
      have hs1stk : ∀ j : Stk, j ≠ k → s1.stk j = s.stk j := fun j hj =>
        Function.update_of_ne hj (g :: s.stk k) s.stk
      have hnot : ∀ p ∈ l', p.2 ≠ k := fun p hp hh =>
        hknot (by rw [← hh]; exact List.mem_map_of_mem (f := Prod.snd) hp)
      obtain ⟨s2, n2, e2', hn2, hcont2, hfr2⟩ := ih s1 hnd'
      refine ⟨s2, 2 + n2, ?_, ?_, ?_, ?_⟩
      · exact Eval.seq e12 e2'
      · simp only [List.length_cons]; omega
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · rw [hfr2 k (fun p hp hh => hknot (by
            rw [hh]; exact List.mem_map_of_mem (f := Prod.snd) hp))]
          exact hs1k
        · rw [hcont2 p hp']
          show p.1 :: Function.update s.stk k (g :: s.stk k) p.2 = p.1 :: s.stk p.2
          rw [Function.update_of_ne (hnot p hp') (g :: s.stk k) s.stk]
      · intro j hj
        have hjk : ∀ p ∈ l', j ≠ p.2 := fun p hp hh => hj p (List.mem_cons_of_mem (g, k) hp) hh
        rw [hfr2 j hjk]
        exact hs1stk j (hj (g, k) (by simp))

/-! ## `openProg` -/

theorem open_ev (main : Cmd) : OpenSpec main := by
  intro s
  obtain ⟨s1, n1, e1, hn1, hcont, hfr⟩ := ev_markPush main rTmp marks s (by decide)
  let s2 : State := ⟨Function.update s1.reg rZ (Glyph.bit false), s1.stk⟩
  let s3 : State := ⟨Function.update s2.reg rIe Glyph.iend, s2.stk⟩
  have e2 : Eval main (.set rZ (Glyph.bit false)) s1 s2 1 :=
    Eval.set (main := main) rZ (Glyph.bit false) s1
  have e3 : Eval main (.set rIe Glyph.iend) s2 s3 1 :=
    Eval.set (main := main) rIe Glyph.iend s2
  have eall : Eval main openProg s s3 (n1 + (1 + 1)) := by
    have h := Eval.seq e1 (Eval.seq e2 e3)
    simpa [openProg] using h
  have hs3 : ∀ j : Stk, s3.stk j = s1.stk j := fun j => rfl
  have hmark : ∀ p ∈ marks, p.2 ∈ ({sA, sB, sR, sC, sS, sT, sW, sU} : Finset Stk) := by
    decide
  refine ⟨s3, n1 + (1 + 1), eall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn1' : n1 ≤ 2 * marks.length + 1 := hn1
    have hm : marks.length = 8 := rfl
    rw [hm] at hn1'
    omega
  · show s3.stk 0 = s.stk 0
    rw [hs3 0]
    exact hfr 0 (fun p hp hh => by
      have h1 := hmark p hp
      rw [← hh] at h1
      exact absurd h1 (by decide))
  · show s3.stk sA = mkA :: s.stk sA
    rw [hs3 sA]; exact hcont (mkA, sA) (by decide)
  · show s3.stk sB = mkB :: s.stk sB
    rw [hs3 sB]; exact hcont (mkB, sB) (by decide)
  · show s3.stk sR = mkR :: s.stk sR
    rw [hs3 sR]; exact hcont (mkR, sR) (by decide)
  · show s3.stk sC = mkC :: s.stk sC
    rw [hs3 sC]; exact hcont (mkC, sC) (by decide)
  · show s3.stk sS = mkS :: s.stk sS
    rw [hs3 sS]; exact hcont (mkS, sS) (by decide)
  · show s3.stk sT = mkT :: s.stk sT
    rw [hs3 sT]; exact hcont (mkT, sT) (by decide)
  · show s3.stk sW = mkW :: s.stk sW
    rw [hs3 sW]; exact hcont (mkW, sW) (by decide)
  · show s3.stk sU = mkU :: s.stk sU
    rw [hs3 sU]; exact hcont (mkU, sU) (by decide)
  · intro j hj
    have hj' : j ≠ 0 ∧ j ≠ sA ∧ j ≠ sB ∧ j ≠ sR ∧ j ≠ sC ∧ j ≠ sS ∧ j ≠ sT ∧ j ≠ sW ∧
        j ≠ sU := by
      simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hj
    obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hj'
    rw [hs3 j]
    refine hfr j (fun p hp hpk => ?_)
    simp only [marks, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with hh | hh | hh | hh | hh | hh | hh | hh
    · rw [hh] at hpk; exact h1 hpk
    · rw [hh] at hpk; exact h2 hpk
    · rw [hh] at hpk; exact h3 hpk
    · rw [hh] at hpk; exact h4 hpk
    · rw [hh] at hpk; exact h5 hpk
    · rw [hh] at hpk; exact h6 hpk
    · rw [hh] at hpk; exact h7 hpk
    · rw [hh] at hpk; exact h8 hpk

/-! ## Single marker pops -/

/-- A single `pop` of a marker glyph above `bk`: the stack loses the marker, every other stack is
unchanged, at cost exactly 1. -/
theorem ev_pop_marker (main : Cmd) (k : Stk) (T : Glyph) (r : Reg) (bk : List Glyph) (s : State)
    (h : s.stk k = T :: bk) :
    ∃ (s' : State), Eval main (.pop k r) s s' 1 ∧ s'.stk k = bk ∧
      (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) :=
  ⟨⟨Function.update s.reg r ((s.stk k).headD Glyph.eos), Function.update s.stk k (s.stk k).tail⟩,
    HvdH.Eval.pop k r s, by
      show Function.update s.stk k (s.stk k).tail k = bk
      rw [Function.update_self k ((s.stk k).tail) s.stk, h, List.tail_cons],
    fun j hj => by
      show Function.update s.stk k (s.stk k).tail j = s.stk j
      exact Function.update_of_ne hj (s.stk k).tail s.stk⟩

theorem close_ev (main : Cmd) (a : ℕ) : CloseSpec main a := by
  intro bkA bkB bkR bkC bkT bkW bkU s hA hB hR hC hT hW hU
  let Inv : List Glyph → State → Prop := fun gs t =>
    (∃ l : List Bool, gs = bitsG l) ∧ t.stk sA = gs ++ mkA :: bkA ∧
      (∀ j : Stk, j ≠ sA → t.stk j = s.stk j)
  have hstk : ∀ gs t, Inv gs t → t.stk sA = gs ++ mkA :: bkA := fun gs t h => h.2.1
  have hterm : ∀ (g : Glyph) (gs : List Glyph) (t : State), Inv (g :: gs) t → g ≠ mkA := by
    rintro g gs t ⟨⟨l, hgs⟩, -, -⟩
    have hg : g ∈ bitsG l := by rw [← hgs]; exact List.mem_cons_self
    exact bitsG_ne_mkA l g hg 1
  have hreg : ∀ gs t (g : Glyph), Inv gs t → Inv gs ⟨Function.update t.reg rL g, t.stk⟩ := by
    rintro gs t g ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun j hj => h3 j hj⟩
  have hpop : ∀ (g : Glyph) (gs : List Glyph) (t : State), Inv (g :: gs) t →
      Inv gs (⟨Function.update t.reg rL g,
        Function.update t.stk sA (gs ++ mkA :: bkA)⟩ : State) := by
    rintro g gs t ⟨⟨l, hgs⟩, h2, h3⟩
    obtain ⟨b, l1, -, hgs1⟩ := exists_of_bitglyph_head hgs
    refine ⟨⟨l1, hgs1⟩, ?_, ?_⟩
    · show Function.update t.stk sA (gs ++ mkA :: bkA) sA = gs ++ mkA :: bkA
      exact Function.update_self sA (gs ++ mkA :: bkA) t.stk
    · intro j hj
      show Function.update t.stk sA (gs ++ mkA :: bkA) j = s.stk j
      rw [Function.update_of_ne hj (gs ++ mkA :: bkA) t.stk]
      exact h3 j hj
  have hstep : ∀ (g : Glyph) (gs : List Glyph) (t : State), g ≠ mkA → t.reg rL = g →
      Inv gs t → ∃ t' n, Eval main .skip t t' n ∧ n ≤ 1 ∧ Inv gs t' :=
    fun g gs t _ _ h => ⟨t, 1, Eval.skip t, le_rfl, h⟩
  obtain ⟨s1, n1, e1, hI1, -, hn1⟩ :=
    Work.IntLib.consume_eval (main := main) (k := sA) (T := mkA) (r := rL) (handler := .skip)
      (Inv := Inv) (below := bkA) (b := 1) hstk hterm hreg hpop hstep (gs := natBits a) (s := s)
      ⟨⟨a.bits, rfl⟩, hA, fun j _ => rfl⟩
  obtain ⟨⟨l1, hgs1⟩, hA1, hfr1⟩ := hI1
  have hl1 : l1 = [] := by simpa [bitsG] using hgs1.symm
  have hAnil : s1.stk sA = mkA :: bkA := by rw [hA1]; rfl
  -- the seven pops
  obtain ⟨t1, ep1, ht1, hf1⟩ := ev_pop_marker main sA mkA rTmp bkA s1 hAnil
  have G1 : ∀ j, j ≠ sA → t1.stk j = s.stk j := fun j h1 => (hf1 j h1).trans (hfr1 j h1)
  obtain ⟨t2, ep2, ht2, hf2⟩ := ev_pop_marker main sB mkB rTmp bkB t1
    ((G1 sB (show sB ≠ sA by decide)).trans hB)
  have G2 : ∀ j, j ≠ sA → j ≠ sB → t2.stk j = s.stk j := fun j h1 h2 =>
    (hf2 j h2).trans (G1 j h1)
  obtain ⟨t3, ep3, ht3, hf3⟩ := ev_pop_marker main sR mkR rTmp bkR t2
    ((G2 sR (show sR ≠ sA by decide) (show sR ≠ sB by decide)).trans hR)
  have G3 : ∀ j, j ≠ sA → j ≠ sB → j ≠ sR → t3.stk j = s.stk j := fun j h1 h2 h3 =>
    (hf3 j h3).trans (G2 j h1 h2)
  obtain ⟨t4, ep4, ht4, hf4⟩ := ev_pop_marker main sC mkC rTmp bkC t3
    ((G3 sC (show sC ≠ sA by decide) (show sC ≠ sB by decide)
      (show sC ≠ sR by decide)).trans hC)
  have G4 : ∀ j, j ≠ sA → j ≠ sB → j ≠ sR → j ≠ sC → t4.stk j = s.stk j :=
    fun j h1 h2 h3 h4 => (hf4 j h4).trans (G3 j h1 h2 h3)
  obtain ⟨t5, ep5, ht5, hf5⟩ := ev_pop_marker main sT mkT rTmp bkT t4
    ((G4 sT (show sT ≠ sA by decide) (show sT ≠ sB by decide) (show sT ≠ sR by decide)
      (show sT ≠ sC by decide)).trans hT)
  have G5 : ∀ j, j ≠ sA → j ≠ sB → j ≠ sR → j ≠ sC → j ≠ sT → t5.stk j = s.stk j :=
    fun j h1 h2 h3 h4 h5 => (hf5 j h5).trans (G4 j h1 h2 h3 h4)
  obtain ⟨t6, ep6, ht6, hf6⟩ := ev_pop_marker main sW mkW rTmp bkW t5
    ((G5 sW (show sW ≠ sA by decide) (show sW ≠ sB by decide) (show sW ≠ sR by decide)
      (show sW ≠ sC by decide) (show sW ≠ sT by decide)).trans hW)
  have G6 : ∀ j, j ≠ sA → j ≠ sB → j ≠ sR → j ≠ sC → j ≠ sT → j ≠ sW → t6.stk j = s.stk j :=
    fun j h1 h2 h3 h4 h5 h6 => (hf6 j h6).trans (G5 j h1 h2 h3 h4 h5)
  obtain ⟨t7, ep7, ht7, hf7⟩ := ev_pop_marker main sU mkU rTmp bkU t6
    ((G6 sU (show sU ≠ sA by decide) (show sU ≠ sB by decide) (show sU ≠ sR by decide)
      (show sU ≠ sC by decide) (show sU ≠ sT by decide) (show sU ≠ sW by decide)).trans hU)
  -- the contents after the seven pops
  have csA : t7.stk sA = bkA := by
    rw [hf7 sA (show sA ≠ sU by decide), hf6 sA (show sA ≠ sW by decide),
      hf5 sA (show sA ≠ sT by decide), hf4 sA (show sA ≠ sC by decide),
      hf3 sA (show sA ≠ sR by decide), hf2 sA (show sA ≠ sB by decide)]
    exact ht1
  have csB : t7.stk sB = bkB := by
    rw [hf7 sB (show sB ≠ sU by decide), hf6 sB (show sB ≠ sW by decide),
      hf5 sB (show sB ≠ sT by decide), hf4 sB (show sB ≠ sC by decide),
      hf3 sB (show sB ≠ sR by decide)]
    exact ht2
  have csR : t7.stk sR = bkR := by
    rw [hf7 sR (show sR ≠ sU by decide), hf6 sR (show sR ≠ sW by decide),
      hf5 sR (show sR ≠ sT by decide), hf4 sR (show sR ≠ sC by decide)]
    exact ht3
  have csC : t7.stk sC = bkC := by
    rw [hf7 sC (show sC ≠ sU by decide), hf6 sC (show sC ≠ sW by decide),
      hf5 sC (show sC ≠ sT by decide)]
    exact ht4
  have csT : t7.stk sT = bkT := by
    rw [hf7 sT (show sT ≠ sU by decide), hf6 sT (show sT ≠ sW by decide)]
    exact ht5
  have csW : t7.stk sW = bkW := by
    rw [hf7 sW (show sW ≠ sU by decide)]
    exact ht6
  have csU : t7.stk sU = bkU := ht7
  have hpops : Eval main (Work.IntLib.MulS.seqs [.pop sA rTmp, .pop sB rTmp, .pop sR rTmp,
      .pop sC rTmp, .pop sT rTmp, .pop sW rTmp, .pop sU rTmp]) s1 t7 7 := by
    simp only [Work.IntLib.MulS.seqs]
    exact Eval.seq ep1 (Eval.seq ep2 (Eval.seq ep3 (Eval.seq ep4 (Eval.seq ep5
      (Eval.seq ep6 ep7)))))
  have eall : Eval main closeProg s t7 (n1 + 7) := by
    have h := Eval.seq e1 hpops
    simpa [closeProg, Work.IntLib.MulS.seqs] using h
  have hsub : Work.IntLib.MulS.cmdTouches closeProg ⊆
      ({sA, sB, sR, sC, sT, sW, sU} : Finset Stk) := by decide
  have hlen : (natBits a).length = a.size := by
    simp [natBits, bitsG, Nat.size_eq_bits_len]
  have hn1' : n1 ≤ (a.size + 1) * 5 + 7 := by
    have h := hn1
    rw [hlen] at h
    simpa using h
  refine ⟨t7, n1 + 7, eall, ?_, csA, csB, csR, csC, csT, csW, csU, ?_⟩
  · omega
  · intro j hj
    exact Work.IntLib.MulS.Eval.stk_frame eall (fun hc => hj (hsub hc))

end Work.Resample.MulNW
