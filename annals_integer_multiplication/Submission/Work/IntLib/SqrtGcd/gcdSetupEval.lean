import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdProg
import Submission.Work.IntLib.SqrtGcd.parseToEval
import Submission.Work.Kernel.Raw
import Submission.Work.IntLib.encodeNatBridge

/-!
# `SG.gcdSetup`: parsing the two values into the bit regions `sU`, `sV`

`SG.gcdSetup` pushes the seven frame markers, pops the sign of the first value, parses its
magnitude bits from stack 0 onto `sP` (`SG.parseTo`), moves the bits (reversed, hence least
significant bit first) onto `sU`, and does the same for the second value onto `sV`.

The main ingredient is the already-proved `parseToEval`; the rest is straight-line composition
with the canonical states of `Work.Kernel.Raw`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH Work.Layout
open Work.IntLib.SG

/-! ## Private bookkeeping lemmas -/

private theorem gBit_ne_mk' (b : Bool) (i : HvdH.Stk) : Glyph.bit b ≠ Glyph.mk i := fun h => by
  cases h

private theorem gMk_ne_eos' (i : HvdH.Stk) : Glyph.mk i ≠ Glyph.eos := fun h => by cases h

private theorem mem_map_bit_ne_mk' (l : List Bool) (i : HvdH.Stk) :
    ∀ g ∈ l.map Glyph.bit, g ≠ Glyph.mk i := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨b, -, rfl⟩ := hg
  exact gBit_ne_mk' b i

private theorem mStK' (k : HvdH.Stk) (T : HvdH.Glyph) (d : HvdH.Stk) (r : HvdH.Reg)
    (gs below : List HvdH.Glyph) (s : HvdH.State) (h : k ≠ d) :
    (SG.mSt k T d r gs below s).stk k = T :: below := by simp [SG.mSt, h]

private theorem mStD' (k : HvdH.Stk) (T : HvdH.Glyph) (d : HvdH.Stk) (r : HvdH.Reg)
    (gs below : List HvdH.Glyph) (s : HvdH.State) :
    (SG.mSt k T d r gs below s).stk d = gs.reverse ++ s.stk d := by simp [SG.mSt]

private theorem mStO' (k : HvdH.Stk) (T : HvdH.Glyph) (d j : HvdH.Stk) (r : HvdH.Reg)
    (gs below : List HvdH.Glyph) (s : HvdH.State) (h1 : j ≠ k) (h2 : j ≠ d) :
    (SG.mSt k T d r gs below s).stk j = s.stk j := by simp [SG.mSt, h1, h2]

private theorem tPop_ne' (s : HvdH.State) (j : HvdH.Stk) (r : HvdH.Reg) (h : j ≠ 0) :
    (State.tPop s 0 r).stk j = s.stk j := by
  simp only [State.tPop, State.updReg_stk, State.updStk_apply, if_neg h]

private theorem tPop_zero' (s : HvdH.State) (r : HvdH.Reg) :
    (State.tPop s 0 r).stk 0 = (s.stk 0).tail := by
  simp only [State.tPop, State.updReg_stk, State.updStk_same]

private theorem evOf' {main p : HvdH.Cmd} {s s' : HvdH.State} {n : ℕ}
    (h : HvdH.Eval main p s s' n) : Work.Layout.Ev main p s s' n := ⟨n, h, le_rfl⟩

private theorem mkPushEval' (main : HvdH.Cmd) (k : HvdH.Stk) (r : HvdH.Reg) (s : HvdH.State) :
    HvdH.Eval main (SG.mkPush k r) s
      ((s.updReg r (Glyph.mk k)).updStk k (Glyph.mk k :: s.stk k)) (1 + 1) := by
  have h1 : HvdH.Eval main (HvdH.Cmd.set r (Glyph.mk k)) s (s.updReg r (Glyph.mk k)) 1 :=
    Work.Kernel.eval_set main r (Glyph.mk k) s
  have h2 : HvdH.Eval main (HvdH.Cmd.push k r) (s.updReg r (Glyph.mk k))
      ((s.updReg r (Glyph.mk k)).updStk k ((s.updReg r (Glyph.mk k)).reg r
        :: (s.updReg r (Glyph.mk k)).stk k)) 1 :=
    Work.Kernel.eval_push main k r (s.updReg r (Glyph.mk k))
  have h3 := HvdH.Eval.seq h1 h2
  rw [SG.mkPush]
  simpa using h3

/-! ## The setup program -/

theorem gcdSetupEval (main : HvdH.Cmd) (a b : ℤ) (R : List HvdH.Glyph) (s : HvdH.State)
    (hstk : s.stk 0 = (HvdH.Val.int a).enc ++ (HvdH.Val.int b).enc ++ R) :
    ∃ s' m, HvdH.Eval main Work.IntLib.SG.gcdSetup s s' m ∧
      m ≤ 200 + (HvdH.isz a + HvdH.isz b) * 100 ∧
      s'.stk 0 = R ∧
      s'.stk Work.IntLib.SG.sU = a.natAbs.bits.map HvdH.Glyph.bit
        ++ HvdH.Glyph.mk Work.IntLib.SG.sU :: s.stk Work.IntLib.SG.sU ∧
      s'.stk Work.IntLib.SG.sV = b.natAbs.bits.map HvdH.Glyph.bit
        ++ HvdH.Glyph.mk Work.IntLib.SG.sV :: s.stk Work.IntLib.SG.sV ∧
      s'.stk Work.IntLib.SG.sG = HvdH.Glyph.mk Work.IntLib.SG.sG :: s.stk Work.IntLib.SG.sG ∧
      s'.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: s.stk Work.IntLib.SG.sP ∧
      s'.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: s.stk Work.IntLib.SG.sQ ∧
      s'.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: s.stk Work.IntLib.SG.sR ∧
      s'.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: s.stk Work.IntLib.SG.sS ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.SG.sU → j ≠ Work.IntLib.SG.sV →
        j ≠ Work.IntLib.SG.sG → j ≠ Work.IntLib.SG.sP → j ≠ Work.IntLib.SG.sQ →
        j ≠ Work.IntLib.SG.sR → j ≠ Work.IntLib.SG.sS → s'.stk j = s.stk j) := by
  -- the second operand, as it sits below the first one on stack 0
  set P : List HvdH.Glyph := (if b < 0 then Glyph.neg else Glyph.pos) ::
      (b.natAbs.bits.map Glyph.bit ++ [Glyph.iend] ++ R) with hP
  have hs0 : s.stk 0 = (if a < 0 then Glyph.neg else Glyph.pos) ::
      (a.natAbs.bits.map Glyph.bit ++ [Glyph.iend] ++ P) := by
    rw [hstk, Work.IntLib.enc_int, Work.IntLib.enc_int, Work.IntLib.encodeNat_eq_bits, hP]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- ## 1. the seven frame markers
  set t1 : HvdH.State := (s.updReg rgT (Glyph.mk sU)).updStk sU (Glyph.mk sU :: s.stk sU) with ht1
  have e1 : HvdH.Eval main (SG.mkPush SG.sU SG.rgT) s t1 (1 + 1) := by
    rw [ht1]
    exact mkPushEval' main SG.sU SG.rgT s
  set t2 : HvdH.State := (t1.updReg rgT (Glyph.mk sV)).updStk sV (Glyph.mk sV :: t1.stk sV) with ht2
  have e2 : HvdH.Eval main (SG.mkPush SG.sV SG.rgT) t1 t2 (1 + 1) := by
    rw [ht2]
    exact mkPushEval' main SG.sV SG.rgT t1
  set t3 : HvdH.State := (t2.updReg rgT (Glyph.mk sG)).updStk sG (Glyph.mk sG :: t2.stk sG) with ht3
  have e3 : HvdH.Eval main (SG.mkPush SG.sG SG.rgT) t2 t3 (1 + 1) := by
    rw [ht3]
    exact mkPushEval' main SG.sG SG.rgT t2
  set t4 : HvdH.State := (t3.updReg rgT (Glyph.mk sP)).updStk sP (Glyph.mk sP :: t3.stk sP) with ht4
  have e4 : HvdH.Eval main (SG.mkPush SG.sP SG.rgT) t3 t4 (1 + 1) := by
    rw [ht4]
    exact mkPushEval' main SG.sP SG.rgT t3
  set t5 : HvdH.State := (t4.updReg rgT (Glyph.mk sQ)).updStk sQ (Glyph.mk sQ :: t4.stk sQ) with ht5
  have e5 : HvdH.Eval main (SG.mkPush SG.sQ SG.rgT) t4 t5 (1 + 1) := by
    rw [ht5]
    exact mkPushEval' main SG.sQ SG.rgT t4
  set t6 : HvdH.State := (t5.updReg rgT (Glyph.mk sR)).updStk sR (Glyph.mk sR :: t5.stk sR) with ht6
  have e6 : HvdH.Eval main (SG.mkPush SG.sR SG.rgT) t5 t6 (1 + 1) := by
    rw [ht6]
    exact mkPushEval' main SG.sR SG.rgT t5
  set t7 : HvdH.State := (t6.updReg rgT (Glyph.mk sS)).updStk sS (Glyph.mk sS :: t6.stk sS) with ht7
  have e7 : HvdH.Eval main (SG.mkPush SG.sS SG.rgT) t6 t7 (1 + 1) := by
    rw [ht7]
    exact mkPushEval' main SG.sS SG.rgT t6
  have hU7 : t7.stk SG.sU = Glyph.mk SG.sU :: s.stk SG.sU := by
    simp (config := { decide := true }) [ht7, ht6, ht5, ht4, ht3, ht2, ht1]
  have hV7 : t7.stk SG.sV = Glyph.mk SG.sV :: s.stk SG.sV := by
    simp (config := { decide := true }) [ht7, ht6, ht5, ht4, ht3, ht2, ht1]
  have hG7 : t7.stk SG.sG = Glyph.mk SG.sG :: s.stk SG.sG := by
    simp (config := { decide := true }) [ht7, ht6, ht5, ht4, ht3, ht2, ht1]
  have hP7 : t7.stk SG.sP = Glyph.mk SG.sP :: s.stk SG.sP := by
    simp (config := { decide := true }) [ht7, ht6, ht5, ht4, ht3, ht2, ht1]
  have hQ7 : t7.stk SG.sQ = Glyph.mk SG.sQ :: s.stk SG.sQ := by
    simp (config := { decide := true }) [ht7, ht6, ht5, ht4, ht3, ht2, ht1]
  have hR7 : t7.stk SG.sR = Glyph.mk SG.sR :: s.stk SG.sR := by
    simp (config := { decide := true }) [ht7, ht6, ht5, ht4, ht3, ht2, ht1]
  have hS7 : t7.stk SG.sS = Glyph.mk SG.sS :: s.stk SG.sS := by
    simp (config := { decide := true }) [ht7, ht6, ht5, ht4, ht3, ht2, ht1]
  have hfr7 : ∀ j : HvdH.Stk, j ≠ SG.sU → j ≠ SG.sV → j ≠ SG.sG → j ≠ SG.sP →
      j ≠ SG.sQ → j ≠ SG.sR → j ≠ SG.sS → t7.stk j = s.stk j := by
    intro j h1 h2 h3 h4 h5 h6 h7
    simp (config := { decide := true }) [ht7, ht6, ht5, ht4, ht3, ht2, ht1, h1, h2, h3, h4, h5,
      h6, h7]
  -- ## 2. pop the sign of `a`
  set s8 : HvdH.State := State.tPop t7 0 rgU with hs8
  have e8 : HvdH.Eval main (.pop 0 rgU) t7 s8 1 := by
    rw [hs8]; exact Work.Kernel.eval_pop main 0 rgU t7
  have hs80 : s8.stk 0 = a.natAbs.bits.map Glyph.bit ++ [Glyph.iend] ++ P := by
    have h70 : t7.stk 0 = s.stk 0 :=
      hfr7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hs8, tPop_zero' t7 rgU, h70, hs0]
    rfl
  have h8P : s8.stk SG.sP = Glyph.mk SG.sP :: s.stk SG.sP := by
    rw [hs8, tPop_ne' t7 SG.sP rgU (by decide), hP7]
  -- ## 3. parse the magnitude bits of `a` onto `sP`
  obtain ⟨s9, n9, e9, hn9, h90, h9P, -, h9fr⟩ :=
    parseToEval main SG.sP SG.rgU SG.rgZ SG.rgF (by decide) (by decide) (by decide) (by decide)
      (a.natAbs.bits) P s8 hs80
  have h9P' : s9.stk SG.sP
      = (a.natAbs.bits.map Glyph.bit).reverse ++ (Glyph.mk SG.sP :: s.stk SG.sP) := by
    rw [h9P, h8P]
  -- ## 4. pop the delimiter
  set s10 : HvdH.State := State.tPop s9 0 rgU with hs10
  have e10 : HvdH.Eval main (.pop 0 rgU) s9 s10 1 := by
    rw [hs10]; exact Work.Kernel.eval_pop main 0 rgU s9
  have hs10P : s10.stk 0 = P := by
    rw [hs10, tPop_zero' s9 rgU, h90]
    rfl
  -- ## 5. move the bits onto `sU` (reversing them back to least significant bit first)
  set gsU : List HvdH.Glyph := (a.natAbs.bits.map Glyph.bit).reverse with hgsU
  have h10P : s10.stk SG.sP = gsU ++ Glyph.mk SG.sP :: s.stk SG.sP := by
    rw [hs10, tPop_ne' s9 SG.sP rgU (by decide), h9P', hgsU]
  have hTU : ∀ g ∈ gsU, g ≠ Glyph.mk SG.sP := by
    intro g hg
    rw [hgsU, List.mem_reverse] at hg
    exact mem_map_bit_ne_mk' (a.natAbs.bits) SG.sP g hg
  have e11 : HvdH.Eval main (SG.rLoop SG.sP (Glyph.mk SG.sP) (some SG.sU) SG.rgT) s10
      (SG.mSt SG.sP (Glyph.mk SG.sP) SG.sU SG.rgT gsU (s.stk SG.sP) s10)
      (7 + gsU.length * 5) :=
    SG.mLoop_eval main SG.sP (Glyph.mk SG.sP) SG.sU SG.rgT (gMk_ne_eos' SG.sP) (by decide)
      gsU (s.stk SG.sP) s10 h10P hTU
  set s11 : HvdH.State := SG.mSt SG.sP (Glyph.mk SG.sP) SG.sU SG.rgT gsU (s.stk SG.sP) s10
    with hs11
  have h11U : s11.stk SG.sU = a.natAbs.bits.map Glyph.bit ++ Glyph.mk SG.sU :: s.stk SG.sU := by
    rw [hs11, mStD' SG.sP (Glyph.mk SG.sP) SG.sU SG.rgT gsU (s.stk SG.sP) s10]
    have h2 : s10.stk SG.sU = Glyph.mk SG.sU :: s.stk SG.sU := by
      rw [hs10, tPop_ne' s9 SG.sU rgU (by decide), h9fr SG.sU (by decide) (by decide),
        hs8, tPop_ne' t7 SG.sU rgU (by decide), hU7]
    rw [h2, hgsU, List.reverse_reverse]
  have h11P : s11.stk SG.sP = Glyph.mk SG.sP :: s.stk SG.sP := by
    rw [hs11, mStK' SG.sP (Glyph.mk SG.sP) SG.sU SG.rgT gsU (s.stk SG.sP) s10 (by decide)]
  -- ## 6. pop the sign of `b`
  set s12 : HvdH.State := State.tPop s11 0 rgU with hs12
  have e12 : HvdH.Eval main (.pop 0 rgU) s11 s12 1 := by
    rw [hs12]; exact Work.Kernel.eval_pop main 0 rgU s11
  have hs12P : s12.stk 0 = b.natAbs.bits.map Glyph.bit ++ [Glyph.iend] ++ R := by
    have h110 : s11.stk 0 = P := by
      rw [hs11, mStO' SG.sP (Glyph.mk SG.sP) SG.sU 0 SG.rgT gsU (s.stk SG.sP) s10
        (by decide) (by decide), hs10P]
    rw [hs12, tPop_zero' s11 rgU, h110, hP]
    rfl
  have h12P : s12.stk SG.sP = Glyph.mk SG.sP :: s.stk SG.sP := by
    rw [hs12, tPop_ne' s11 SG.sP rgU (by decide), h11P]
  -- ## 7. parse the magnitude bits of `b`
  obtain ⟨s13, n13, e13, hn13, h130, h13P, -, h13fr⟩ :=
    parseToEval main SG.sP SG.rgU SG.rgZ SG.rgF (by decide) (by decide) (by decide) (by decide)
      (b.natAbs.bits) R s12 hs12P
  have h13P' : s13.stk SG.sP
      = (b.natAbs.bits.map Glyph.bit).reverse ++ (Glyph.mk SG.sP :: s.stk SG.sP) := by
    rw [h13P, h12P]
  -- ## 8. pop the delimiter
  set s14 : HvdH.State := State.tPop s13 0 rgU with hs14
  have e14 : HvdH.Eval main (.pop 0 rgU) s13 s14 1 := by
    rw [hs14]; exact Work.Kernel.eval_pop main 0 rgU s13
  have hs14R : s14.stk 0 = R := by
    rw [hs14, tPop_zero' s13 rgU, h130]
    rfl
  -- ## 9. move the bits onto `sV`
  set gsV : List HvdH.Glyph := (b.natAbs.bits.map Glyph.bit).reverse with hgsV
  have h14P : s14.stk SG.sP = gsV ++ Glyph.mk SG.sP :: s.stk SG.sP := by
    rw [hs14, tPop_ne' s13 SG.sP rgU (by decide), h13P', hgsV]
  have hTV : ∀ g ∈ gsV, g ≠ Glyph.mk SG.sP := by
    intro g hg
    rw [hgsV, List.mem_reverse] at hg
    exact mem_map_bit_ne_mk' (b.natAbs.bits) SG.sP g hg
  have e15 : HvdH.Eval main (SG.rLoop SG.sP (Glyph.mk SG.sP) (some SG.sV) SG.rgT) s14
      (SG.mSt SG.sP (Glyph.mk SG.sP) SG.sV SG.rgT gsV (s.stk SG.sP) s14)
      (7 + gsV.length * 5) :=
    SG.mLoop_eval main SG.sP (Glyph.mk SG.sP) SG.sV SG.rgT (gMk_ne_eos' SG.sP) (by decide)
      gsV (s.stk SG.sP) s14 h14P hTV
  set s15 : HvdH.State := SG.mSt SG.sP (Glyph.mk SG.sP) SG.sV SG.rgT gsV (s.stk SG.sP) s14
    with hs15
  -- ## 10. the invariants of the final state
  have hback : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ SG.sP → j ≠ SG.sU → j ≠ SG.sV →
      s15.stk j = t7.stk j := by
    intro j hj0 hjP hjU hjV
    rw [hs15, mStO' SG.sP (Glyph.mk SG.sP) SG.sV j SG.rgT gsV (s.stk SG.sP) s14 hjP hjV,
      hs14, tPop_ne' s13 j rgU hj0,
      h13fr j hj0 hjP,
      hs12, tPop_ne' s11 j rgU hj0,
      hs11, mStO' SG.sP (Glyph.mk SG.sP) SG.sU j SG.rgT gsU (s.stk SG.sP) s10 hjP hjU,
      hs10, tPop_ne' s9 j rgU hj0,
      h9fr j hj0 hjP,
      hs8, tPop_ne' t7 j rgU hj0]
  have h015 : s15.stk 0 = R := by
    rw [hs15, mStO' SG.sP (Glyph.mk SG.sP) SG.sV 0 SG.rgT gsV (s.stk SG.sP) s14
        (by decide) (by decide),
      hs14, tPop_zero' s13 rgU, h130]
    rfl
  have hU15 : s15.stk SG.sU
      = a.natAbs.bits.map Glyph.bit ++ Glyph.mk SG.sU :: s.stk SG.sU := by
    rw [hs15, mStO' SG.sP (Glyph.mk SG.sP) SG.sV SG.sU SG.rgT gsV (s.stk SG.sP) s14
        (by decide) (by decide),
      hs14, tPop_ne' s13 SG.sU rgU (by decide),
      h13fr SG.sU (by decide) (by decide),
      hs12, tPop_ne' s11 SG.sU rgU (by decide),
      h11U]
  have hV15 : s15.stk SG.sV
      = b.natAbs.bits.map Glyph.bit ++ Glyph.mk SG.sV :: s.stk SG.sV := by
    rw [hs15, mStD' SG.sP (Glyph.mk SG.sP) SG.sV SG.rgT gsV (s.stk SG.sP) s14]
    have h2 : s14.stk SG.sV = Glyph.mk SG.sV :: s.stk SG.sV := by
      rw [hs14, tPop_ne' s13 SG.sV rgU (by decide),
        h13fr SG.sV (by decide) (by decide),
        hs12, tPop_ne' s11 SG.sV rgU (by decide),
        hs11, mStO' SG.sP (Glyph.mk SG.sP) SG.sU SG.sV SG.rgT gsU (s.stk SG.sP) s10
          (by decide) (by decide),
        hs10, tPop_ne' s9 SG.sV rgU (by decide),
        h9fr SG.sV (by decide) (by decide),
        hs8, tPop_ne' t7 SG.sV rgU (by decide),
        hV7]
    rw [h2, hgsV, List.reverse_reverse]
  have hG15 : s15.stk SG.sG = Glyph.mk SG.sG :: s.stk SG.sG := by
    rw [hback SG.sG (by decide) (by decide) (by decide) (by decide), hG7]
  have hP15 : s15.stk SG.sP = Glyph.mk SG.sP :: s.stk SG.sP := by
    rw [hs15, mStK' SG.sP (Glyph.mk SG.sP) SG.sV SG.rgT gsV (s.stk SG.sP) s14 (by decide)]
  have hQ15 : s15.stk SG.sQ = Glyph.mk SG.sQ :: s.stk SG.sQ := by
    rw [hback SG.sQ (by decide) (by decide) (by decide) (by decide), hQ7]
  have hR15 : s15.stk SG.sR = Glyph.mk SG.sR :: s.stk SG.sR := by
    rw [hback SG.sR (by decide) (by decide) (by decide) (by decide), hR7]
  have hS15 : s15.stk SG.sS = Glyph.mk SG.sS :: s.stk SG.sS := by
    rw [hback SG.sS (by decide) (by decide) (by decide) (by decide), hS7]
  have hfr15 : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ SG.sU → j ≠ SG.sV → j ≠ SG.sG → j ≠ SG.sP →
      j ≠ SG.sQ → j ≠ SG.sR → j ≠ SG.sS → s15.stk j = s.stk j := by
    intro j hj0 hjU hjV hjG hjP hjQ hjR hjS
    rw [hback j hj0 hjP hjU hjV, hfr7 j hjU hjV hjG hjP hjQ hjR hjS]
  -- ## 11. the cost
  have hchain : Work.Layout.Ev main SG.gcdSetup s s15
      (55 + 12 * ((a.natAbs.bits).length + (b.natAbs.bits).length)) := by
    have h15 := Work.Layout.Ev.seqs_cons (evOf' e15) Work.Layout.Ev.seqs_nil
    have h14 := Work.Layout.Ev.seqs_cons (evOf' e14) h15
    have h13 := Work.Layout.Ev.seqs_cons ((evOf' e13).mono hn13) h14
    have h12 := Work.Layout.Ev.seqs_cons (evOf' e12) h13
    have h11 := Work.Layout.Ev.seqs_cons (evOf' e11) h12
    have h10 := Work.Layout.Ev.seqs_cons (evOf' e10) h11
    have h9 := Work.Layout.Ev.seqs_cons ((evOf' e9).mono hn9) h10
    have h8 := Work.Layout.Ev.seqs_cons (evOf' e8) h9
    have h7 := Work.Layout.Ev.seqs_cons (evOf' e7) h8
    have h6 := Work.Layout.Ev.seqs_cons (evOf' e6) h7
    have h5 := Work.Layout.Ev.seqs_cons (evOf' e5) h6
    have h4 := Work.Layout.Ev.seqs_cons (evOf' e4) h5
    have h3 := Work.Layout.Ev.seqs_cons (evOf' e3) h4
    have h2' := Work.Layout.Ev.seqs_cons (evOf' e2) h3
    have h1' := Work.Layout.Ev.seqs_cons (evOf' e1) h2'
    exact h1'.mono (by
      rw [hgsU, hgsV]
      simp only [List.length_map, List.length_reverse]
      omega)
  obtain ⟨n, hn, hle⟩ := hchain
  refine ⟨s15, n, hn, ?_, h015, hU15, hV15, hG15, hP15, hQ15, hR15, hS15, hfr15⟩
  have hA : (a.natAbs.bits).length = a.natAbs.size := Nat.size_eq_bits_len a.natAbs
  have hB : (b.natAbs.bits).length = b.natAbs.size := Nat.size_eq_bits_len b.natAbs
  rw [hA, hB] at hle
  rw [Work.IntLib.isz_eq, Work.IntLib.isz_eq]
  omega

end Work.IntLib.SqrtGcd
