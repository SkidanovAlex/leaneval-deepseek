import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.Shift.Base
import Submission.Work.IntLib.preMainEnc
import Submission.Work.IntLib.preMainEntryEq
import Submission.Work.IntLib.preMainCostBound

namespace Work.IntLib

open HvdH

theorem preMainPhaseV2 (main : HvdH.Cmd) (rebuildB loopP : HvdH.Cmd) (KR : ℕ) (Cloop : ℕ → ℕ → ℕ)
    (x b N : ℕ) (hb : 1 ≤ b) (hN : 1 ≤ N) (hxN : x < 2 ^ (b * N))
    (hrebuildB : ∀ (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (bs : List Bool)
      (Gs Gt Gc Gs' : List HvdH.Glyph),
      X Work.IntLib.sR = (HvdH.Glyph.iend :: (bs.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos])) ++ Work.IntLib.Shift.gmk Work.IntLib.sR :: Gs →
      X Work.IntLib.sB = Gt → X Work.IntLib.sCB = Gc → X Work.IntLib.sCT = Gs' →
      ∃ s' n, Work.Layout.Ev main rebuildB ⟨g, X⟩ s' n ∧ n ≤ KR * (bs.length + Work.IntLib.ofBits bs + 1) ∧
        s'.stk Work.IntLib.sR = Work.IntLib.Shift.gmk Work.IntLib.sR :: Gs ∧
        s'.stk Work.IntLib.sB = (HvdH.Glyph.pos :: (bs.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend])) ++ Gt ∧
        s'.stk Work.IntLib.sCB = Work.IntLib.Unary (Work.IntLib.ofBits bs) Gc ∧ s'.stk Work.IntLib.sCT = Gs' ∧
        (∀ k, k ≠ Work.IntLib.sR → k ≠ Work.IntLib.sB → k ≠ Work.IntLib.sCB → k ≠ Work.IntLib.sCT → s'.stk k = X k))
    (hloop : ∀ (Y : HvdH.Stk → List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (Ca : List HvdH.Glyph),
      Y Work.IntLib.sCB = Work.IntLib.Unary b Ca → (∀ r : HvdH.Reg, r ≠ Work.IntLib.rG → g r = HvdH.Glyph.eos) →
      Work.Layout.Ev main loopP (⟨g, Work.IntLib.lStk x b N Y 0⟩ : HvdH.State)
        (Work.IntLib.lSt x b N Y (b * N)) (Cloop b N))
    (X₀ : HvdH.Stk → List HvdH.Glyph)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h0 : X 0 = X₀ 0)
    (hX : X Work.IntLib.sX = HvdH.Val.enc (HvdH.Val.int (x : ℤ)) ++ Work.IntLib.Shift.gmk Work.IntLib.sX :: X₀ Work.IntLib.sX)
    (hB : X Work.IntLib.sB = HvdH.Val.enc (HvdH.Val.int (b : ℤ)) ++ Work.IntLib.Shift.gmk Work.IntLib.sB :: X₀ Work.IntLib.sB)
    (hNv : X Work.IntLib.sN = HvdH.Val.enc (HvdH.Val.int (N : ℤ)) ++ Work.IntLib.Shift.gmk Work.IntLib.sN :: X₀ Work.IntLib.sN)
    (hR : X Work.IntLib.sR = Work.IntLib.Shift.gmk Work.IntLib.sR :: X₀ Work.IntLib.sR)
    (hS : X Work.IntLib.sS = Work.IntLib.Shift.gmk Work.IntLib.sS :: X₀ Work.IntLib.sS)
    (hCW : X Work.IntLib.sCW = Work.IntLib.gEnd :: Work.IntLib.Shift.gmk Work.IntLib.sCW :: X₀ Work.IntLib.sCW)
    (hCB : X Work.IntLib.sCB = Work.IntLib.Shift.gmk Work.IntLib.sCB :: X₀ Work.IntLib.sCB)
    (hCT : X Work.IntLib.sCT = Work.IntLib.Shift.gmk Work.IntLib.sCT :: X₀ Work.IntLib.sCT)
    (hCN : X Work.IntLib.sCN = Work.IntLib.Unary N (Work.IntLib.Shift.gmk Work.IntLib.sCN :: X₀ Work.IntLib.sCN))
    (hZ : X Work.IntLib.sZ = Work.IntLib.Shift.gmk Work.IntLib.sZ :: X₀ Work.IntLib.sZ)
    (hoth : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.sX → j ≠ Work.IntLib.sB → j ≠ Work.IntLib.sN → j ≠ Work.IntLib.sR →
      j ≠ Work.IntLib.sS → j ≠ Work.IntLib.sCW → j ≠ Work.IntLib.sCB → j ≠ Work.IntLib.sCT → j ≠ Work.IntLib.sCN →
      j ≠ Work.IntLib.sZ → X j = X₀ j) :
    ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main (Work.IntLib.preMainProg rebuildB loopP) ⟨g, X⟩ s' n ∧
      n ≤ (2 * KR + 100) * (HvdH.isz x + HvdH.isz b + HvdH.isz N + N * (b + 1) + 1) + Cloop b N ∧
      s' = Work.IntLib.lSt x b N (Work.IntLib.Yinit b N X₀) (b * N) := by
  -- ## 1. the `b`-encoding moves from `sB` onto `sR`, reversed
  obtain ⟨s1, n1, he1, hn1, _hreg1, hs1B, hs1R, ho1⟩ :=
    Shift.drain_ev main sB sR (Shift.gmk sB) rH rK (by decide) (by decide)
      (Val.enc (.int (b : ℤ))) (X₀ sB) (Shift.gmk sR :: X₀ sR) g X
      (fun h hh => noMark_enc_natCast b h hh sB) hB hR
  have hn1' : n1 ≤ 5 * (isz (b : ℤ) + 1) + 2 := by
    have h := hn1
    simp only [enc_natCast_length, isz_natCast] at h ⊢
    exact h
  -- ## 2. `rebuildB` restores the `b`-value on `sB` and the `b`-counter on `sCB`
  have hY1 : s1.stk sR =
      Glyph.iend :: (b.bits.reverse.map Glyph.bit ++ [Glyph.pos]) ++ Shift.gmk sR :: X₀ sR := by
    rw [hs1R, enc_natCast_reverse]
  have hCB1 : s1.stk sCB = Shift.gmk sCB :: X₀ sCB := by
    rw [ho1 sCB (by decide) (by decide)]; exact hCB
  have hCT1 : s1.stk sCT = Shift.gmk sCT :: X₀ sCT := by
    rw [ho1 sCT (by decide) (by decide)]; exact hCT
  obtain ⟨s2, n2, hev2, hn2, hs2R, hs2B, hs2CB, hs2CT, ho2⟩ :=
    hrebuildB s1.reg s1.stk b.bits (X₀ sR) (Shift.gmk sB :: X₀ sB) (s1.stk sCB) (s1.stk sCT)
      hY1 hs1B rfl rfl
  have hn2' : n2 ≤ KR * (b.size + b + 1) := by
    have h := hn2
    rw [ofBits_bits, Nat.size_eq_bits_len] at h
    exact h
  -- ## 3. stacks that neither region move touches
  have hs2oth : ∀ j : Stk, j ≠ sR → j ≠ sB → j ≠ sCB → j ≠ sCT → s2.stk j = X j :=
    fun j h1 h2 h3 h4 => by rw [ho2 j h1 h2 h3 h4, ho1 j h2 h1]
  have hs2X : s2.stk sX = X sX := hs2oth sX (by decide) (by decide) (by decide) (by decide)
  have hs2N : s2.stk sN = X sN := hs2oth sN (by decide) (by decide) (by decide) (by decide)
  have hs2S : s2.stk sS = X sS := hs2oth sS (by decide) (by decide) (by decide) (by decide)
  have hs2CW : s2.stk sCW = X sCW := hs2oth sCW (by decide) (by decide) (by decide) (by decide)
  have hs2CN : s2.stk sCN = X sCN := hs2oth sCN (by decide) (by decide) (by decide) (by decide)
  have hs2Z : s2.stk sZ = X sZ := hs2oth sZ (by decide) (by decide) (by decide) (by decide)
  have hs20 : s2.stk (0 : Stk) = X 0 := hs2oth 0 (by decide) (by decide) (by decide) (by decide)
  -- ## 4. `pop sX`/`push sR` seed the loop accumulator `sR` with the sign of `x`
  have hs2X' : s2.stk sX = Glyph.pos :: (streamOf x ++ Shift.gmk sX :: X₀ sX) := by
    rw [hs2X, hX, enc_natCast]
    rfl
  have hhead : (s2.stk sX).headD Glyph.eos = Glyph.pos := by simp [hs2X']
  have htail : (s2.stk sX).tail = streamOf x ++ Shift.gmk sX :: X₀ sX := by simp [hs2X']
  -- ## 5. `resetRegs` clears all registers; the state just before the loop is
  have hS4stk : (⟨Function.update s2.reg rA Glyph.pos,
        Function.update (Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)) sR
          (Glyph.pos :: Shift.gmk sR :: X₀ sR)⟩ : State).stk =
      Function.update (Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)) sR
        (Glyph.pos :: Shift.gmk sR :: X₀ sR) := rfl
  obtain ⟨s5, n5, hev5, hn5, hreg5, hstk5⟩ :=
    resetRegs_ev main
      ⟨Function.update s2.reg rA Glyph.pos,
        Function.update (Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)) sR
          (Glyph.pos :: Shift.gmk sR :: X₀ sR)⟩
  -- ## 6. the loop-entry state has exactly the `Yinit` shape
  have hX5 : s5.stk sX = streamOf x ++ Shift.gmk sX :: X₀ sX := by
    rw [hstk5, hS4stk, Function.update_of_ne (show sX ≠ sR by decide), Function.update_self]
  have hB5 : s5.stk sB = Val.enc (.int (b : ℤ)) ++ Shift.gmk sB :: X₀ sB := by
    rw [hstk5, hS4stk, Function.update_of_ne (show sB ≠ sR by decide),
      Function.update_of_ne (show sB ≠ sX by decide), hs2B, enc_natCast]
  have hN5 : s5.stk sN = Val.enc (.int (N : ℤ)) ++ Shift.gmk sN :: X₀ sN := by
    rw [hstk5, hS4stk, Function.update_of_ne (show sN ≠ sR by decide),
      Function.update_of_ne (show sN ≠ sX by decide), hs2N, hNv]
  have hR5 : s5.stk sR = [Glyph.pos] ++ Shift.gmk sR :: X₀ sR := by
    rw [hstk5, hS4stk, Function.update_self]
    simp
  have hS5 : s5.stk sS = Shift.gmk sS :: X₀ sS := by
    rw [hstk5, hS4stk, Function.update_of_ne (show sS ≠ sR by decide),
      Function.update_of_ne (show sS ≠ sX by decide), hs2S, hS]
  have hCW5 : s5.stk sCW = gEnd :: Shift.gmk sCW :: X₀ sCW := by
    rw [hstk5, hS4stk, Function.update_of_ne (show sCW ≠ sR by decide),
      Function.update_of_ne (show sCW ≠ sX by decide), hs2CW, hCW]
  have hCB5 : s5.stk sCB = Unary b (Shift.gmk sCB :: X₀ sCB) := by
    rw [hstk5, hS4stk, Function.update_of_ne (show sCB ≠ sR by decide),
      Function.update_of_ne (show sCB ≠ sX by decide), hs2CB, hCB1, ofBits_bits]
  have hCT5 : s5.stk sCT = Shift.gmk sCT :: X₀ sCT := by
    rw [hstk5, hS4stk, Function.update_of_ne (show sCT ≠ sR by decide),
      Function.update_of_ne (show sCT ≠ sX by decide), hs2CT, hCT1]
  have hCN5 : s5.stk sCN = Unary N (Shift.gmk sCN :: X₀ sCN) := by
    rw [hstk5, hS4stk, Function.update_of_ne (show sCN ≠ sR by decide),
      Function.update_of_ne (show sCN ≠ sX by decide), hs2CN, hCN]
  have hZ5 : s5.stk sZ = Shift.gmk sZ :: X₀ sZ := by
    rw [hstk5, hS4stk, Function.update_of_ne (show sZ ≠ sR by decide),
      Function.update_of_ne (show sZ ≠ sX by decide), hs2Z, hZ]
  have h05 : s5.stk (0 : Stk) = X₀ 0 := by
    rw [hstk5, hS4stk, Function.update_of_ne (show (0 : Stk) ≠ sR by decide),
      Function.update_of_ne (show (0 : Stk) ≠ sX by decide), hs20]
    exact h0
  have hoth5 : ∀ j : Stk, j ≠ 0 → j ≠ sX → j ≠ sB → j ≠ sN → j ≠ sR → j ≠ sS → j ≠ sCW →
      j ≠ sCB → j ≠ sCT → j ≠ sCN → j ≠ sZ → s5.stk j = X₀ j := by
    intro j hj0 hjX hjB hjN hjR hjS hjCW hjCB hjCT hjCN hjZ
    rw [hstk5, hS4stk, Function.update_of_ne hjR, Function.update_of_ne hjX,
      hs2oth j hjR hjB hjCB hjCT,
      hoth j hj0 hjX hjB hjN hjR hjS hjCW hjCB hjCT hjCN hjZ]
  have hs5eq : s5 = ⟨fun _ => Glyph.eos, lStk x b N (Yinit b N X₀) 0⟩ :=
    preMainEntryEq x b N X₀ s5 hreg5 hX5 hB5 hN5 hR5 hS5 hCW5 hCB5 hCT5 hCN5 hZ5 h05 hoth5
  -- ## 7. the main loop, and the cost accounting
  have hloop5 : Work.Layout.Ev main loopP ⟨fun _ => Glyph.eos, lStk x b N (Yinit b N X₀) 0⟩
      (lSt x b N (Yinit b N X₀) (b * N)) (Cloop b N) :=
    hloop (Yinit b N X₀) (fun _ => Glyph.eos) (Shift.gmk sCB :: X₀ sCB) (Yinit_sCB b N X₀)
      (fun _ _ => rfl)
  have hloop5' : Work.Layout.Ev main loopP s5 (lSt x b N (Yinit b N X₀) (b * N)) (Cloop b N) := by
    rw [hs5eq]
    exact hloop5
  have hstep1 : Work.Layout.Ev main (Shift.drain sB sR (Shift.gmk sB) rH rK) ⟨g, X⟩ s1
      (5 * (isz (b : ℤ) + 1) + 2) := ⟨n1, he1, hn1'⟩
  have hstep2 : Work.Layout.Ev main rebuildB s1 s2 (KR * (b.size + b + 1)) := hev2.mono hn2'
  have hstep3 : Work.Layout.Ev main (.pop sX rA) s2
      ⟨Function.update s2.reg rA Glyph.pos,
        Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)⟩ 1 := by
    have h := Work.Layout.ev_pop' main sX rA s2.reg s2.stk
    rw [hhead, htail] at h
    exact h
  have hstep4 : Work.Layout.Ev main (.push sR rA)
      ⟨Function.update s2.reg rA Glyph.pos,
        Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)⟩
      ⟨Function.update s2.reg rA Glyph.pos,
        Function.update (Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)) sR
          (Glyph.pos :: Shift.gmk sR :: X₀ sR)⟩ 1 := by
    have h := Work.Layout.ev_push' main sR rA (Function.update s2.reg rA Glyph.pos)
      (Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX))
    have h1 : (Function.update s2.reg rA Glyph.pos) rA = Glyph.pos :=
      Function.update_self rA Glyph.pos s2.reg
    have h2 : (Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)) sR =
        Shift.gmk sR :: X₀ sR := by
      rw [Function.update_of_ne (show sR ≠ sX by decide), hs2R]
    rw [h1, h2] at h
    exact h
  have hstep5 : Work.Layout.Ev main resetRegs
      ⟨Function.update s2.reg rA Glyph.pos,
        Function.update (Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)) sR
          (Glyph.pos :: Shift.gmk sR :: X₀ sR)⟩ s5 17 := hev5.mono hn5
  have h_loop_reset : Work.Layout.Ev main (Layout.seqs [resetRegs, loopP])
      ⟨Function.update s2.reg rA Glyph.pos,
        Function.update (Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)) sR
          (Glyph.pos :: Shift.gmk sR :: X₀ sR)⟩
      (lSt x b N (Yinit b N X₀) (b * N)) (17 + Cloop b N) :=
    Work.Layout.Ev.seqs_cons (cs := [loopP]) hstep5 hloop5'
  have h_push_loop : Work.Layout.Ev main (Layout.seqs [.push sR rA, resetRegs, loopP])
      ⟨Function.update s2.reg rA Glyph.pos,
        Function.update s2.stk sX (streamOf x ++ Shift.gmk sX :: X₀ sX)⟩
      (lSt x b N (Yinit b N X₀) (b * N)) (1 + (17 + Cloop b N)) :=
    Work.Layout.Ev.seqs_cons (cs := [resetRegs, loopP]) hstep4 h_loop_reset
  have h_pop_loop : Work.Layout.Ev main (Layout.seqs [.pop sX rA, .push sR rA, resetRegs, loopP])
      s2 (lSt x b N (Yinit b N X₀) (b * N)) (1 + (1 + (17 + Cloop b N))) :=
    Work.Layout.Ev.seqs_cons (cs := [.push sR rA, resetRegs, loopP]) hstep3 h_push_loop
  have h_rebuild_loop :
      Work.Layout.Ev main (Layout.seqs [rebuildB, .pop sX rA, .push sR rA, resetRegs, loopP])
        s1 (lSt x b N (Yinit b N X₀) (b * N))
        (KR * (b.size + b + 1) + (1 + (1 + (17 + Cloop b N)))) :=
    Work.Layout.Ev.seqs_cons (cs := [.pop sX rA, .push sR rA, resetRegs, loopP]) hstep2 h_pop_loop
  have h_all : Work.Layout.Ev main
      (Layout.seqs [Shift.drain sB sR (Shift.gmk sB) rH rK, rebuildB, .pop sX rA, .push sR rA,
        resetRegs, loopP]) ⟨g, X⟩ (lSt x b N (Yinit b N X₀) (b * N))
      (5 * (isz (b : ℤ) + 1) + 2 + (KR * (b.size + b + 1) + (1 + (1 + (17 + Cloop b N))))) :=
    Work.Layout.Ev.seqs_cons (cs := [rebuildB, .pop sX rA, .push sR rA, resetRegs, loopP])
      hstep1 h_rebuild_loop
  refine ⟨lSt x b N (Yinit b N X₀) (b * N),
    5 * (isz (b : ℤ) + 1) + 2 + (KR * (b.size + b + 1) + (1 + (1 + (17 + Cloop b N)))), ?_, ?_, rfl⟩
  · exact h_all
  · exact preMainCostBound KR b N (isz x) (isz N) (Cloop b N)
      (5 * (isz (b : ℤ) + 1) + 2) (KR * (b.size + b + 1)) 17 (Cloop b N)
      hb hN le_rfl le_rfl le_rfl le_rfl


end Work.IntLib
