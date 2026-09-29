import Mathlib
import Submission.Work.IntLib.SqrtGcd.SqrtProg
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.Base
import Submission.Work.IntLib.SqrtGcd.parseToEval
import Submission.Work.IntLib.SqrtGcd.sqrtSetupBits

/-!
# Correctness of `SG.sqrtSetup`

`SG.sqrtSetup` pushes the frame markers of the seven scratch stacks `sA … sS`, pops the sign
glyph of the integer value on top of stack 0, parses its magnitude onto `sA` (most significant
bit first) and pads it with a single leading `false` bit when the number of bits is odd.

The main result `sqrtSetupJunk` packages this at the `Eval` level.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH

attribute [local simp] HvdH.State.tPush HvdH.State.tSet HvdH.State.tPop HvdH.State.updStk
  HvdH.State.updReg
  Work.IntLib.SG.sA Work.IntLib.SG.sB Work.IntLib.SG.sC Work.IntLib.SG.sP
  Work.IntLib.SG.sQ Work.IntLib.SG.sR Work.IntLib.SG.sS
  Work.IntLib.SG.rgT Work.IntLib.SG.rgU Work.IntLib.SG.rgZ Work.IntLib.SG.rgF

/-- `SG.mkPush k r` pushes the marker `Glyph.mk k` onto stack `k` (cost 2). -/
theorem mkPush_ev (main : HvdH.Cmd) (k : HvdH.Stk) (r : HvdH.Reg) (s : HvdH.State) :
    Work.Layout.Ev main (Work.IntLib.SG.mkPush k r) s
      (HvdH.State.tPush (HvdH.State.tSet s r (HvdH.Glyph.mk k)) k r) 2 := by
  have a := Work.Layout.ev_set main r (HvdH.Glyph.mk k) s
  have b := Work.Layout.ev_push main k r (HvdH.State.tSet s r (HvdH.Glyph.mk k))
  exact Work.Layout.Ev.seq a b

theorem sqrtSetupJunk (main : HvdH.Cmd) (z : ℤ) (hz : 0 ≤ z) (R : List HvdH.Glyph) (s : HvdH.State)
    (hstk : s.stk 0 = (HvdH.Val.int z).enc ++ R) :
    ∃ s' m, HvdH.Eval main Work.IntLib.SG.sqrtSetup s s' m ∧
      m ≤ 100 + HvdH.isz z * 100 ∧
      (∃ bs : List Bool, s'.stk Work.IntLib.SG.sA = bs.map HvdH.Glyph.bit
          ++ HvdH.Glyph.mk Work.IntLib.SG.sA :: s.stk Work.IntLib.SG.sA ∧ bs.length % 2 = 0 ∧
        Work.IntLib.SG.bval bs = z.toNat) ∧
      s'.stk 0 = R ∧
      s'.stk Work.IntLib.SG.sB = HvdH.Glyph.mk Work.IntLib.SG.sB :: s.stk Work.IntLib.SG.sB ∧
      s'.stk Work.IntLib.SG.sC = HvdH.Glyph.mk Work.IntLib.SG.sC :: s.stk Work.IntLib.SG.sC ∧
      s'.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: s.stk Work.IntLib.SG.sP ∧
      s'.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: s.stk Work.IntLib.SG.sQ ∧
      s'.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: s.stk Work.IntLib.SG.sR ∧
      s'.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: s.stk Work.IntLib.SG.sS ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.SG.sA → j ≠ Work.IntLib.SG.sB →
        j ≠ Work.IntLib.SG.sC → j ≠ Work.IntLib.SG.sP → j ≠ Work.IntLib.SG.sQ →
        j ≠ Work.IntLib.SG.sR → j ≠ Work.IntLib.SG.sS → s'.stk j = s.stk j) := by
  -- ## 0. decode the input value
  have hzlt : ¬ z < 0 := by omega
  let L : List Bool := Computability.encodeNat z.natAbs
  have hLlen : L.length = z.natAbs.size := by
    show (Computability.encodeNat z.natAbs).length = z.natAbs.size
    exact Work.IntLib.encodeNat_length _
  have hstk_raw : s.stk 0 = HvdH.Glyph.pos ::
      ((Computability.encodeNat z.natAbs).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ R) := by
    rw [Work.IntLib.enc_int] at hstk
    rw [hstk]
    simp [hzlt, List.cons_append, List.append_assoc]
  have hstk0 : s.stk 0 = HvdH.Glyph.pos :: (L.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ R) :=
    hstk_raw
  -- ## 1. the seven marker pushes
  let s1 : HvdH.State :=
    HvdH.State.tPush (HvdH.State.tSet s Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sA))
      Work.IntLib.SG.sA Work.IntLib.SG.rgT
  let s2 : HvdH.State :=
    HvdH.State.tPush (HvdH.State.tSet s1 Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sB))
      Work.IntLib.SG.sB Work.IntLib.SG.rgT
  let s3 : HvdH.State :=
    HvdH.State.tPush (HvdH.State.tSet s2 Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sC))
      Work.IntLib.SG.sC Work.IntLib.SG.rgT
  let s4 : HvdH.State :=
    HvdH.State.tPush (HvdH.State.tSet s3 Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sP))
      Work.IntLib.SG.sP Work.IntLib.SG.rgT
  let s5 : HvdH.State :=
    HvdH.State.tPush (HvdH.State.tSet s4 Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sQ))
      Work.IntLib.SG.sQ Work.IntLib.SG.rgT
  let s6 : HvdH.State :=
    HvdH.State.tPush (HvdH.State.tSet s5 Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sR))
      Work.IntLib.SG.sR Work.IntLib.SG.rgT
  let s7 : HvdH.State :=
    HvdH.State.tPush (HvdH.State.tSet s6 Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sS))
      Work.IntLib.SG.sS Work.IntLib.SG.rgT
  have e1 : Work.Layout.Ev main (Work.IntLib.SG.mkPush Work.IntLib.SG.sA Work.IntLib.SG.rgT) s s1 2 :=
    mkPush_ev main _ _ s
  have e2 : Work.Layout.Ev main (Work.IntLib.SG.mkPush Work.IntLib.SG.sB Work.IntLib.SG.rgT) s1 s2 2 :=
    mkPush_ev main _ _ s1
  have e3 : Work.Layout.Ev main (Work.IntLib.SG.mkPush Work.IntLib.SG.sC Work.IntLib.SG.rgT) s2 s3 2 :=
    mkPush_ev main _ _ s2
  have e4 : Work.Layout.Ev main (Work.IntLib.SG.mkPush Work.IntLib.SG.sP Work.IntLib.SG.rgT) s3 s4 2 :=
    mkPush_ev main _ _ s3
  have e5 : Work.Layout.Ev main (Work.IntLib.SG.mkPush Work.IntLib.SG.sQ Work.IntLib.SG.rgT) s4 s5 2 :=
    mkPush_ev main _ _ s4
  have e6 : Work.Layout.Ev main (Work.IntLib.SG.mkPush Work.IntLib.SG.sR Work.IntLib.SG.rgT) s5 s6 2 :=
    mkPush_ev main _ _ s5
  have e7 : Work.Layout.Ev main (Work.IntLib.SG.mkPush Work.IntLib.SG.sS Work.IntLib.SG.rgT) s6 s7 2 :=
    mkPush_ev main _ _ s6
  -- ## 2. stacks after the pushes
  have h7_0 : s7.stk 0 = s.stk 0 := by simp [s7, s6, s5, s4, s3, s2, s1]
  have h7_A : s7.stk Work.IntLib.SG.sA =
      HvdH.Glyph.mk Work.IntLib.SG.sA :: s.stk Work.IntLib.SG.sA := by
    simp [s7, s6, s5, s4, s3, s2, s1]
  have h7_B : s7.stk Work.IntLib.SG.sB =
      HvdH.Glyph.mk Work.IntLib.SG.sB :: s.stk Work.IntLib.SG.sB := by
    simp [s7, s6, s5, s4, s3, s2, s1]
  have h7_C : s7.stk Work.IntLib.SG.sC =
      HvdH.Glyph.mk Work.IntLib.SG.sC :: s.stk Work.IntLib.SG.sC := by
    simp [s7, s6, s5, s4, s3, s2, s1]
  have h7_P : s7.stk Work.IntLib.SG.sP =
      HvdH.Glyph.mk Work.IntLib.SG.sP :: s.stk Work.IntLib.SG.sP := by
    simp [s7, s6, s5, s4, s3, s2, s1]
  have h7_Q : s7.stk Work.IntLib.SG.sQ =
      HvdH.Glyph.mk Work.IntLib.SG.sQ :: s.stk Work.IntLib.SG.sQ := by
    simp [s7, s6, s5, s4, s3, s2, s1]
  have h7_R : s7.stk Work.IntLib.SG.sR =
      HvdH.Glyph.mk Work.IntLib.SG.sR :: s.stk Work.IntLib.SG.sR := by
    simp [s7, s6, s5, s4, s3, s2, s1]
  have h7_S : s7.stk Work.IntLib.SG.sS =
      HvdH.Glyph.mk Work.IntLib.SG.sS :: s.stk Work.IntLib.SG.sS := by
    simp [s7, s6, s5, s4, s3, s2, s1]
  have h7_oth : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.SG.sA → j ≠ Work.IntLib.SG.sB →
      j ≠ Work.IntLib.SG.sC → j ≠ Work.IntLib.SG.sP → j ≠ Work.IntLib.SG.sQ →
      j ≠ Work.IntLib.SG.sR → j ≠ Work.IntLib.SG.sS → s7.stk j = s.stk j := by
    intro j h0 hA hB hC hP hQ hR hS
    simp only [Work.IntLib.SG.sA, Work.IntLib.SG.sB, Work.IntLib.SG.sC, Work.IntLib.SG.sP,
      Work.IntLib.SG.sQ, Work.IntLib.SG.sR, Work.IntLib.SG.sS] at hA hB hC hP hQ hR hS
    simp [s7, s6, s5, s4, s3, s2, s1, h0, hA, hB, hC, hP, hQ, hR, hS]
  -- ## 3. pop the sign glyph
  let s8 : HvdH.State := HvdH.State.tPop s7 0 Work.IntLib.SG.rgU
  have e8 : Work.Layout.Ev main (.pop 0 Work.IntLib.SG.rgU) s7 s8 1 :=
    Work.Layout.ev_pop main 0 Work.IntLib.SG.rgU s7
  have h8_0 : s8.stk 0 = L.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ R := by
    have h1 : s8.stk 0 = (s7.stk 0).tail := by simp [s8]
    have h2 : (s7.stk 0).tail = (s.stk 0).tail := by rw [h7_0]
    have h3 : (s.stk 0).tail = L.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ R := by
      simpa only [List.tail_cons] using congrArg List.tail hstk0
    rw [h1, h2, h3]
  -- ## 4. parse the magnitude onto `sA`
  obtain ⟨s9, n9, hev9, hn9, h9_0, h9_A, h9_P, h9_oth⟩ :=
    parseToEval main Work.IntLib.SG.sA Work.IntLib.SG.rgU Work.IntLib.SG.rgZ Work.IntLib.SG.rgF
      (by decide) (by decide) (by decide) (by decide) L R s8 h8_0
  have e9 : Work.Layout.Ev main
      (Work.IntLib.SG.parseTo Work.IntLib.SG.sA Work.IntLib.SG.rgU Work.IntLib.SG.rgZ
        Work.IntLib.SG.rgF) s8 s9 (7 * L.length + 10) := ⟨n9, hev9, hn9⟩
  -- ## 5. pop the `iend` delimiter
  let s10 : HvdH.State := HvdH.State.tPop s9 0 Work.IntLib.SG.rgU
  have e10 : Work.Layout.Ev main (.pop 0 Work.IntLib.SG.rgU) s9 s10 1 :=
    Work.Layout.ev_pop main 0 Work.IntLib.SG.rgU s9
  have h10_0 : s10.stk 0 = R := by
    have h1 : s10.stk 0 = (s9.stk 0).tail := by simp [s10]
    have h2 : (s9.stk 0).tail = R := by
      simpa only [List.tail_cons] using congrArg List.tail h9_0
    rw [h1, h2]
  have h10_Z : s10.reg Work.IntLib.SG.rgZ = HvdH.Glyph.bit (decide (L.length % 2 = 1)) := by
    have h1 : s10.reg Work.IntLib.SG.rgZ = s9.reg Work.IntLib.SG.rgZ := by simp [s10]
    rw [h1, h9_P]
  have h10_A : s10.stk Work.IntLib.SG.sA =
      (L.map HvdH.Glyph.bit).reverse ++ HvdH.Glyph.mk Work.IntLib.SG.sA ::
        s.stk Work.IntLib.SG.sA := by
    have h1 : s10.stk Work.IntLib.SG.sA = s9.stk Work.IntLib.SG.sA := by simp [s10]
    rw [h1, h9_A]
    have h2 : s8.stk Work.IntLib.SG.sA = s7.stk Work.IntLib.SG.sA := by simp [s8]
    rw [h2, h7_A]
  have h10_B : s10.stk Work.IntLib.SG.sB =
      HvdH.Glyph.mk Work.IntLib.SG.sB :: s.stk Work.IntLib.SG.sB := by
    have h1 : s10.stk Work.IntLib.SG.sB = s9.stk Work.IntLib.SG.sB := by simp [s10]
    rw [h1, h9_oth Work.IntLib.SG.sB (by decide) (by decide)]
    have h2 : s8.stk Work.IntLib.SG.sB = s7.stk Work.IntLib.SG.sB := by simp [s8]
    rw [h2, h7_B]
  have h10_C : s10.stk Work.IntLib.SG.sC =
      HvdH.Glyph.mk Work.IntLib.SG.sC :: s.stk Work.IntLib.SG.sC := by
    have h1 : s10.stk Work.IntLib.SG.sC = s9.stk Work.IntLib.SG.sC := by simp [s10]
    rw [h1, h9_oth Work.IntLib.SG.sC (by decide) (by decide)]
    have h2 : s8.stk Work.IntLib.SG.sC = s7.stk Work.IntLib.SG.sC := by simp [s8]
    rw [h2, h7_C]
  have h10_P : s10.stk Work.IntLib.SG.sP =
      HvdH.Glyph.mk Work.IntLib.SG.sP :: s.stk Work.IntLib.SG.sP := by
    have h1 : s10.stk Work.IntLib.SG.sP = s9.stk Work.IntLib.SG.sP := by simp [s10]
    rw [h1, h9_oth Work.IntLib.SG.sP (by decide) (by decide)]
    have h2 : s8.stk Work.IntLib.SG.sP = s7.stk Work.IntLib.SG.sP := by simp [s8]
    rw [h2, h7_P]
  have h10_Q : s10.stk Work.IntLib.SG.sQ =
      HvdH.Glyph.mk Work.IntLib.SG.sQ :: s.stk Work.IntLib.SG.sQ := by
    have h1 : s10.stk Work.IntLib.SG.sQ = s9.stk Work.IntLib.SG.sQ := by simp [s10]
    rw [h1, h9_oth Work.IntLib.SG.sQ (by decide) (by decide)]
    have h2 : s8.stk Work.IntLib.SG.sQ = s7.stk Work.IntLib.SG.sQ := by simp [s8]
    rw [h2, h7_Q]
  have h10_R : s10.stk Work.IntLib.SG.sR =
      HvdH.Glyph.mk Work.IntLib.SG.sR :: s.stk Work.IntLib.SG.sR := by
    have h1 : s10.stk Work.IntLib.SG.sR = s9.stk Work.IntLib.SG.sR := by simp [s10]
    rw [h1, h9_oth Work.IntLib.SG.sR (by decide) (by decide)]
    have h2 : s8.stk Work.IntLib.SG.sR = s7.stk Work.IntLib.SG.sR := by simp [s8]
    rw [h2, h7_R]
  have h10_S : s10.stk Work.IntLib.SG.sS =
      HvdH.Glyph.mk Work.IntLib.SG.sS :: s.stk Work.IntLib.SG.sS := by
    have h1 : s10.stk Work.IntLib.SG.sS = s9.stk Work.IntLib.SG.sS := by simp [s10]
    rw [h1, h9_oth Work.IntLib.SG.sS (by decide) (by decide)]
    have h2 : s8.stk Work.IntLib.SG.sS = s7.stk Work.IntLib.SG.sS := by simp [s8]
    rw [h2, h7_S]
  have h10_oth : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.SG.sA → j ≠ Work.IntLib.SG.sB →
      j ≠ Work.IntLib.SG.sC → j ≠ Work.IntLib.SG.sP → j ≠ Work.IntLib.SG.sQ →
      j ≠ Work.IntLib.SG.sR → j ≠ Work.IntLib.SG.sS → s10.stk j = s.stk j := by
    intro j h0 hA hB hC hP hQ hR hS
    simp only [Work.IntLib.SG.sA, Work.IntLib.SG.sB, Work.IntLib.SG.sC, Work.IntLib.SG.sP,
      Work.IntLib.SG.sQ, Work.IntLib.SG.sR, Work.IntLib.SG.sS] at hA hB hC hP hQ hR hS
    have h1 : s10.stk j = s9.stk j := by simp [s10, h0]
    rw [h1, h9_oth j h0 hA]
    have h2 : s8.stk j = s7.stk j := by simp [s8, h0]
    rw [h2]
    exact h7_oth j h0 hA hB hC hP hQ hR hS
  -- ## 6. the padding decision and the bit list `bs`
  let bs : List Bool := (if decide (L.length % 2 = 1) then [false] else []) ++ L.reverse
  have hbs_eq : bs = (if decide (z.natAbs.size % 2 = 1) then [false] else [])
      ++ (Computability.encodeNat z.natAbs).reverse := by
    show (if decide (L.length % 2 = 1) then [false] else []) ++ L.reverse = _
    rw [hLlen]
  obtain ⟨hbslen, hbsval⟩ := sqrtSetupBits z hz bs hbs_eq
  by_cases hpar : decide (L.length % 2 = 1) = true
  · -- ## 7a. the parity is odd: push one padding `false` bit
    let s11 : HvdH.State :=
      HvdH.State.tPush (HvdH.State.tSet s10 Work.IntLib.SG.rgU (HvdH.Glyph.bit false))
        Work.IntLib.SG.sA Work.IntLib.SG.rgU
    have e11 : Work.Layout.Ev main
        (.ite Work.IntLib.SG.rgZ (HvdH.Glyph.bit true)
          (.seq (.set Work.IntLib.SG.rgU (HvdH.Glyph.bit false))
            (.push Work.IntLib.SG.sA Work.IntLib.SG.rgU)) .skip) s10 s11 3 := by
      have hset := Work.Layout.ev_set main Work.IntLib.SG.rgU (HvdH.Glyph.bit false) s10
      have hpush := Work.Layout.ev_push main Work.IntLib.SG.sA Work.IntLib.SG.rgU
        (HvdH.State.tSet s10 Work.IntLib.SG.rgU (HvdH.Glyph.bit false))
      have hseq := Work.Layout.Ev.seq hset hpush
      have hZ : s10.reg Work.IntLib.SG.rgZ = HvdH.Glyph.bit true := by
        rw [h10_Z, hpar]
      exact Work.Layout.Ev.iteT hZ hseq
    have f10 := Work.Layout.Ev.seq e10 e11
    have f9 := Work.Layout.Ev.seq e9 f10
    have f8 := Work.Layout.Ev.seq e8 f9
    have f7 := Work.Layout.Ev.seq e7 f8
    have f6 := Work.Layout.Ev.seq e6 f7
    have f5 := Work.Layout.Ev.seq e5 f6
    have f4 := Work.Layout.Ev.seq e4 f5
    have f3 := Work.Layout.Ev.seq e3 f4
    have f2 := Work.Layout.Ev.seq e2 f3
    have f1 := Work.Layout.Ev.seq e1 f2
    have hfull : Work.Layout.Ev main Work.IntLib.SG.sqrtSetup s s11 (7 * L.length + 40) :=
      f1.mono (by omega)
    obtain ⟨m, hev, hm⟩ := hfull
    have hmle : m ≤ 100 + HvdH.isz z * 100 := by
      rw [HvdH.isz]; omega
    -- stacks of `s11`
    have h11_0 : s11.stk 0 = R := by
      have h1 : s11.stk 0 = s10.stk 0 := by simp [s11]
      rw [h1, h10_0]
    have h11_A : s11.stk Work.IntLib.SG.sA = HvdH.Glyph.bit false ::
        ((L.map HvdH.Glyph.bit).reverse ++ HvdH.Glyph.mk Work.IntLib.SG.sA ::
          s.stk Work.IntLib.SG.sA) := by
      have h1 : s11.stk Work.IntLib.SG.sA = HvdH.Glyph.bit false :: s10.stk Work.IntLib.SG.sA := by
        simp [s11]
      rw [h1, h10_A]
    have hbsT : bs.map HvdH.Glyph.bit = HvdH.Glyph.bit false ::
        (L.map HvdH.Glyph.bit).reverse := by
      have hbs' : bs = [false] ++ L.reverse := by
        simp [bs, hpar]
      rw [hbs']; simp [List.map_reverse]
    have hA' : s11.stk Work.IntLib.SG.sA =
        bs.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sA :: s.stk Work.IntLib.SG.sA := by
      rw [h11_A, hbsT]; simp [List.append_assoc]
    have h11_B : s11.stk Work.IntLib.SG.sB =
        HvdH.Glyph.mk Work.IntLib.SG.sB :: s.stk Work.IntLib.SG.sB := by
      have h1 : s11.stk Work.IntLib.SG.sB = s10.stk Work.IntLib.SG.sB := by simp [s11]
      rw [h1, h10_B]
    have h11_C : s11.stk Work.IntLib.SG.sC =
        HvdH.Glyph.mk Work.IntLib.SG.sC :: s.stk Work.IntLib.SG.sC := by
      have h1 : s11.stk Work.IntLib.SG.sC = s10.stk Work.IntLib.SG.sC := by simp [s11]
      rw [h1, h10_C]
    have h11_P : s11.stk Work.IntLib.SG.sP =
        HvdH.Glyph.mk Work.IntLib.SG.sP :: s.stk Work.IntLib.SG.sP := by
      have h1 : s11.stk Work.IntLib.SG.sP = s10.stk Work.IntLib.SG.sP := by simp [s11]
      rw [h1, h10_P]
    have h11_Q : s11.stk Work.IntLib.SG.sQ =
        HvdH.Glyph.mk Work.IntLib.SG.sQ :: s.stk Work.IntLib.SG.sQ := by
      have h1 : s11.stk Work.IntLib.SG.sQ = s10.stk Work.IntLib.SG.sQ := by simp [s11]
      rw [h1, h10_Q]
    have h11_R : s11.stk Work.IntLib.SG.sR =
        HvdH.Glyph.mk Work.IntLib.SG.sR :: s.stk Work.IntLib.SG.sR := by
      have h1 : s11.stk Work.IntLib.SG.sR = s10.stk Work.IntLib.SG.sR := by simp [s11]
      rw [h1, h10_R]
    have h11_S : s11.stk Work.IntLib.SG.sS =
        HvdH.Glyph.mk Work.IntLib.SG.sS :: s.stk Work.IntLib.SG.sS := by
      have h1 : s11.stk Work.IntLib.SG.sS = s10.stk Work.IntLib.SG.sS := by simp [s11]
      rw [h1, h10_S]
    have h11_oth : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.SG.sA → j ≠ Work.IntLib.SG.sB →
        j ≠ Work.IntLib.SG.sC → j ≠ Work.IntLib.SG.sP → j ≠ Work.IntLib.SG.sQ →
        j ≠ Work.IntLib.SG.sR → j ≠ Work.IntLib.SG.sS → s11.stk j = s.stk j := by
      intro j h0 hA hB hC hP hQ hR hS
      simp only [Work.IntLib.SG.sA, Work.IntLib.SG.sB, Work.IntLib.SG.sC, Work.IntLib.SG.sP,
        Work.IntLib.SG.sQ, Work.IntLib.SG.sR, Work.IntLib.SG.sS] at hA hB hC hP hQ hR hS
      have h1 : s11.stk j = s10.stk j := by simp [s11, hA]
      rw [h1]
      exact h10_oth j h0 hA hB hC hP hQ hR hS
    exact ⟨s11, m, hev, hmle, ⟨bs, hA', hbslen, hbsval⟩, h11_0, h11_B, h11_C, h11_P, h11_Q,
      h11_R, h11_S, h11_oth⟩
  · -- ## 7b. the parity is even: no padding
    have hpar' : decide (L.length % 2 = 1) = false := by
      cases h : decide (L.length % 2 = 1) <;> simp_all
    have e11 : Work.Layout.Ev main
        (.ite Work.IntLib.SG.rgZ (HvdH.Glyph.bit true)
          (.seq (.set Work.IntLib.SG.rgU (HvdH.Glyph.bit false))
            (.push Work.IntLib.SG.sA Work.IntLib.SG.rgU)) .skip) s10 s10 2 := by
      have hZ : s10.reg Work.IntLib.SG.rgZ ≠ HvdH.Glyph.bit true := by
        rw [h10_Z, hpar']; decide
      exact Work.Layout.Ev.iteF hZ (Work.Layout.ev_skip main s10)
    have f10 := Work.Layout.Ev.seq e10 e11
    have f9 := Work.Layout.Ev.seq e9 f10
    have f8 := Work.Layout.Ev.seq e8 f9
    have f7 := Work.Layout.Ev.seq e7 f8
    have f6 := Work.Layout.Ev.seq e6 f7
    have f5 := Work.Layout.Ev.seq e5 f6
    have f4 := Work.Layout.Ev.seq e4 f5
    have f3 := Work.Layout.Ev.seq e3 f4
    have f2 := Work.Layout.Ev.seq e2 f3
    have f1 := Work.Layout.Ev.seq e1 f2
    have hfull : Work.Layout.Ev main Work.IntLib.SG.sqrtSetup s s10 (7 * L.length + 40) :=
      f1.mono (by omega)
    obtain ⟨m, hev, hm⟩ := hfull
    have hmle : m ≤ 100 + HvdH.isz z * 100 := by
      rw [HvdH.isz]; omega
    have hbsF : bs.map HvdH.Glyph.bit = (L.map HvdH.Glyph.bit).reverse := by
      have hbs' : bs = L.reverse := by
        simp [bs, hpar']
      rw [hbs']; simp [List.map_reverse]
    have hA' : s10.stk Work.IntLib.SG.sA =
        bs.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sA :: s.stk Work.IntLib.SG.sA := by
      rw [h10_A, hbsF]
    exact ⟨s10, m, hev, hmle, ⟨bs, hA', hbslen, hbsval⟩, h10_0, h10_B, h10_C, h10_P, h10_Q,
      h10_R, h10_S, h10_oth⟩

end Work.IntLib.SqrtGcd
