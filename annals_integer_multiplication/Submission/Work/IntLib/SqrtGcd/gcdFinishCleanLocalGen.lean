import Mathlib
import Submission.Work.IntLib.SqrtGcd.gcdGenAux

/-!
# `gcdFinish ; gcdClean` with junk below the frame markers

`SqrtGcd/gcdFinishEval.lean` proves `gcdFinishCleanLocal` for a state whose seven scratch stacks
hold only their frame markers.  Here the same word is specified with arbitrary junk `bU … bS`
*below* those markers: the programs only ever touch glyphs above the markers (the `rLoop`s stop
there, `finishMove`/`finishEmit` are the `mLoop_eval` moves, the final `.pop`s remove the marker
itself), so the junk survives untouched.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH
open Work.IntLib.SG

/-- Stacks of a state whose stack `i` has been overwritten by `b`: the value is `b`. -/
theorem updStkGen (s : State) (r : Reg) (g : Glyph) (i : Stk) (b : List Glyph) :
    (⟨Function.update s.reg r g, Function.update s.stk i b⟩ : State).stk i = b := by
  show Function.update s.stk i b i = b
  rw [Function.update_self]

/-- Other stacks of a state whose stack `i` has been overwritten by `b`. -/
theorem updStkOGen (s : State) (r : Reg) (g : Glyph) (i j : Stk) (b : List Glyph) (h : j ≠ i) :
    (⟨Function.update s.reg r g, Function.update s.stk i b⟩ : State).stk j = s.stk j := by
  show Function.update s.stk i b j = s.stk j
  rw [Function.update_of_ne h]

/-- **`gcdFinish ; gcdClean` with junk below the markers.**  From a state whose stacks hold `ul`,
`vl`, `k` ticks and junk (`bU`, …, `bS`) below their markers, `gcdFinish` emits the canonical
encoding of the value of `ul` (with the raw content `R` below it) and `gcdClean` empties the seven
scratch stacks down to their junk, restoring everything else. -/
theorem gcdFinishCleanLocalGen (main : HvdH.Cmd) (ul vl : List Bool) (k : ℕ)
    (R : List HvdH.Glyph) (bU bV bG bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (h0 : s.stk 0 = R)
    (hU : s.stk sU = ul.map Glyph.bit ++ Glyph.mk sU :: bU)
    (hV : s.stk sV = vl.map Glyph.bit ++ Glyph.mk sV :: bV)
    (hG : s.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG)
    (hP : s.stk sP = Glyph.mk sP :: bP)
    (hQ : s.stk sQ = Glyph.mk sQ :: bQ)
    (hR : s.stk sR = Glyph.mk sR :: bR)
    (hS : s.stk sS = Glyph.mk sS :: bS) :
    ∃ s' m, HvdH.Eval main (HvdH.Cmd.seq gcdFinish gcdClean) s s' m ∧
      m ≤ 200 * (ul.length + vl.length + k + 1) ∧
      s'.stk 0 = (HvdH.Val.int ((Work.IntLib.ofBits ul : ℕ) : ℤ)).enc ++ R ∧
      s'.stk sU = bU ∧ s'.stk sV = bV ∧ s'.stk sG = bG ∧ s'.stk sP = bP ∧
      s'.stk sQ = bQ ∧ s'.stk sR = bR ∧ s'.stk sS = bS ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR →
        j ≠ sS → s'.stk j = s.stk j) := by
  -- ## step 1: move the region of `sU` onto `sP`
  obtain ⟨s1, m1, e1, hm1, t1P, t1U, fr1⟩ := finishMoveGen main ul bU bP s hU hP
  -- ## step 2: strip the high zeros
  obtain ⟨s2, m2, e2, hm2, t2P, fr2⟩ :=
    stripZerosRegionGen main sP ul.reverse bP s1 (by simpa using t1P)
  have t20 : s2.stk 0 = R := (fr2 0 (by decide)).trans ((fr1 0 (by decide) (by decide)).trans h0)
  have t2U : s2.stk sU = Glyph.mk sU :: bU := (fr2 sU (by decide)).trans t1U
  have t2V : s2.stk sV = vl.map Glyph.bit ++ Glyph.mk sV :: bV :=
    (fr2 sV (by decide)).trans ((fr1 sV (by decide) (by decide)).trans hV)
  have t2G : s2.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG :=
    (fr2 sG (by decide)).trans ((fr1 sG (by decide) (by decide)).trans hG)
  have t2Q : s2.stk sQ = Glyph.mk sQ :: bQ :=
    (fr2 sQ (by decide)).trans ((fr1 sQ (by decide) (by decide)).trans hQ)
  have t2R : s2.stk sR = Glyph.mk sR :: bR :=
    (fr2 sR (by decide)).trans ((fr1 sR (by decide) (by decide)).trans hR)
  have t2S : s2.stk sS = Glyph.mk sS :: bS :=
    (fr2 sS (by decide)).trans ((fr1 sS (by decide) (by decide)).trans hS)
  -- ## step 3: push `iend`
  let S3 : State := ⟨Function.update s2.reg rgU Glyph.iend,
    Function.update s2.stk 0 (Glyph.iend :: s2.stk 0)⟩
  have hS3 : S3 = ⟨Function.update s2.reg rgU Glyph.iend,
      Function.update s2.stk 0 (Glyph.iend :: s2.stk 0)⟩ := rfl
  have e3a : HvdH.Eval main (.set rgU Glyph.iend) s2
      ⟨Function.update s2.reg rgU Glyph.iend, s2.stk⟩ 1 := Eval.set rgU Glyph.iend s2
  have e3b : HvdH.Eval main (.push 0 rgU)
      ⟨Function.update s2.reg rgU Glyph.iend, s2.stk⟩ S3 1 := Eval.push 0 rgU _
  have t30 : S3.stk 0 = Glyph.iend :: R := by rw [hS3, updStkSelf, t20]
  have t3P : S3.stk sP = (dropLead (ul.reverse)).map Glyph.bit ++ Glyph.mk sP :: bP := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sP (by decide)]
    exact t2P
  have t3U : S3.stk sU = Glyph.mk sU :: bU := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sU (by decide)]
    exact t2U
  have t3V : S3.stk sV = vl.map Glyph.bit ++ Glyph.mk sV :: bV := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sV (by decide)]
    exact t2V
  have t3G : S3.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sG (by decide)]
    exact t2G
  have t3Q : S3.stk sQ = Glyph.mk sQ :: bQ := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sQ (by decide)]
    exact t2Q
  have t3R : S3.stk sR = Glyph.mk sR :: bR := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sR (by decide)]
    exact t2R
  have t3S : S3.stk sS = Glyph.mk sS :: bS := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sS (by decide)]
    exact t2S
  -- ## step 4: emit the stripped bits onto stack 0
  obtain ⟨s4, m4, e4, hm4, t40, t4P, fr4⟩ :=
    finishEmitGen main (dropLead (ul.reverse)) (S3.stk 0) bP S3 t3P rfl
  -- ## step 5: push `pos`
  let s5 : State := ⟨Function.update s4.reg rgU Glyph.pos,
    Function.update s4.stk 0 (Glyph.pos :: s4.stk 0)⟩
  have hs5 : s5 = ⟨Function.update s4.reg rgU Glyph.pos,
      Function.update s4.stk 0 (Glyph.pos :: s4.stk 0)⟩ := rfl
  obtain ⟨m5, e5, hm5, t50, fr5⟩ := finishPush main Glyph.pos (s4.stk 0) s4 rfl
  have t50' : s5.stk 0
      = Glyph.pos :: (((dropLead (ul.reverse)).map Glyph.bit).reverse ++ (Glyph.iend :: R)) := by
    rw [t50, t40, t30]
  have t5U : s5.stk sU = Glyph.mk sU :: bU :=
    (fr5 sU (by decide)).trans ((fr4 sU (by decide) (by decide)).trans t3U)
  have t5V : s5.stk sV = vl.map Glyph.bit ++ Glyph.mk sV :: bV :=
    (fr5 sV (by decide)).trans ((fr4 sV (by decide) (by decide)).trans t3V)
  have t5G : s5.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG :=
    (fr5 sG (by decide)).trans ((fr4 sG (by decide) (by decide)).trans t3G)
  have t5P : s5.stk sP = Glyph.mk sP :: bP := (fr5 sP (by decide)).trans t4P
  have t5Q : s5.stk sQ = Glyph.mk sQ :: bQ :=
    (fr5 sQ (by decide)).trans ((fr4 sQ (by decide) (by decide)).trans t3Q)
  have t5R : s5.stk sR = Glyph.mk sR :: bR :=
    (fr5 sR (by decide)).trans ((fr4 sR (by decide) (by decide)).trans t3R)
  have t5S : s5.stk sS = Glyph.mk sS :: bS :=
    (fr5 sS (by decide)).trans ((fr4 sS (by decide) (by decide)).trans t3S)
  -- ## `gcdClean`: the seven drops, then the seven pops
  let C1 : State := dSt sU (Glyph.mk sU) rgT bU s5
  have hC1 : C1 = dSt sU (Glyph.mk sU) rgT bU s5 := rfl
  have eC1 : HvdH.Eval main (SG.rLoop sU (Glyph.mk sU) none rgT) s5 C1 7 := by
    rw [hC1]
    refine dLoop_eval main sU (Glyph.mk sU) rgT (gMk_ne_eos sU) [] bU s5 ?_ (by simp)
    simpa using t5U
  have dV : C1.stk sV = vl.map Glyph.bit ++ Glyph.mk sV :: bV := by
    refine (dStO sU (Glyph.mk sU) rgT bU s5 sV (by decide)).trans ?_
    exact t5V
  let C2 : State := dSt sV (Glyph.mk sV) rgT bV C1
  have hC2 : C2 = dSt sV (Glyph.mk sV) rgT bV C1 := rfl
  have eC2 : HvdH.Eval main (SG.rLoop sV (Glyph.mk sV) none rgT) C1 C2
      (7 + (vl.map Glyph.bit).length * 5) := by
    rw [hC2]
    refine dLoop_eval main sV (Glyph.mk sV) rgT (gMk_ne_eos sV) (vl.map Glyph.bit) bV C1 ?_
      (mem_map_bit_ne_mk vl sV)
    simpa using dV
  have dG : C2.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG := by
    refine (dStO sV (Glyph.mk sV) rgT bV C1 sG (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT bU s5 sG (by decide)).trans ?_
    exact t5G
  let C3 : State := dSt sG (Glyph.mk sG) rgT bG C2
  have hC3 : C3 = dSt sG (Glyph.mk sG) rgT bG C2 := rfl
  have eC3 : HvdH.Eval main (SG.rLoop sG (Glyph.mk sG) none rgT) C2 C3
      (7 + (List.replicate k gTick).length * 5) := by
    rw [hC3]
    refine dLoop_eval main sG (Glyph.mk sG) rgT (gMk_ne_eos sG) (List.replicate k gTick) bG C2 ?_
      (by
        intro g hg
        rw [List.mem_replicate] at hg
        rw [hg.2]
        decide)
    simpa using dG
  have dP : C3.stk sP = Glyph.mk sP :: bP := by
    refine (dStO sG (Glyph.mk sG) rgT bG C2 sP (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT bV C1 sP (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT bU s5 sP (by decide)).trans ?_
    exact t5P
  let C4 : State := dSt sP (Glyph.mk sP) rgT bP C3
  have hC4 : C4 = dSt sP (Glyph.mk sP) rgT bP C3 := rfl
  have eC4 : HvdH.Eval main (SG.rLoop sP (Glyph.mk sP) none rgT) C3 C4 7 := by
    rw [hC4]
    refine dLoop_eval main sP (Glyph.mk sP) rgT (gMk_ne_eos sP) [] bP C3 ?_ (by simp)
    simpa using dP
  have dQ : C4.stk sQ = Glyph.mk sQ :: bQ := by
    refine (dStO sP (Glyph.mk sP) rgT bP C3 sQ (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT bG C2 sQ (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT bV C1 sQ (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT bU s5 sQ (by decide)).trans ?_
    exact t5Q
  let C5 : State := dSt sQ (Glyph.mk sQ) rgT bQ C4
  have hC5 : C5 = dSt sQ (Glyph.mk sQ) rgT bQ C4 := rfl
  have eC5 : HvdH.Eval main (SG.rLoop sQ (Glyph.mk sQ) none rgT) C4 C5 7 := by
    rw [hC5]
    refine dLoop_eval main sQ (Glyph.mk sQ) rgT (gMk_ne_eos sQ) [] bQ C4 ?_ (by simp)
    simpa using dQ
  have dR : C5.stk sR = Glyph.mk sR :: bR := by
    refine (dStO sQ (Glyph.mk sQ) rgT bQ C4 sR (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT bP C3 sR (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT bG C2 sR (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT bV C1 sR (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT bU s5 sR (by decide)).trans ?_
    exact t5R
  let C6 : State := dSt sR (Glyph.mk sR) rgT bR C5
  have hC6 : C6 = dSt sR (Glyph.mk sR) rgT bR C5 := rfl
  have eC6 : HvdH.Eval main (SG.rLoop sR (Glyph.mk sR) none rgT) C5 C6 7 := by
    rw [hC6]
    refine dLoop_eval main sR (Glyph.mk sR) rgT (gMk_ne_eos sR) [] bR C5 ?_ (by simp)
    simpa using dR
  have dS : C6.stk sS = Glyph.mk sS :: bS := by
    refine (dStO sR (Glyph.mk sR) rgT bR C5 sS (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT bQ C4 sS (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT bP C3 sS (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT bG C2 sS (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT bV C1 sS (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT bU s5 sS (by decide)).trans ?_
    exact t5S
  let C7 : State := dSt sS (Glyph.mk sS) rgT bS C6
  have hC7 : C7 = dSt sS (Glyph.mk sS) rgT bS C6 := rfl
  have eC7 : HvdH.Eval main (SG.rLoop sS (Glyph.mk sS) none rgT) C6 C7 7 := by
    rw [hC7]
    refine dLoop_eval main sS (Glyph.mk sS) rgT (gMk_ne_eos sS) [] bS C6 ?_ (by simp)
    simpa using dS
  -- ## the seven pops
  have pU : C7.stk sU = Glyph.mk sU :: bU := by
    refine (dStO sS (Glyph.mk sS) rgT bS C6 sU (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT bR C5 sU (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT bQ C4 sU (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT bP C3 sU (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT bG C2 sU (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT bV C1 sU (by decide)).trans ?_
    exact dStK sU (Glyph.mk sU) rgT bU s5
  let C8 : State := ⟨Function.update C7.reg rgT (Glyph.mk sU), Function.update C7.stk sU bU⟩
  have hC8 : C8 = ⟨Function.update C7.reg rgT (Glyph.mk sU), Function.update C7.stk sU bU⟩ := rfl
  have eC8 : HvdH.Eval main (.pop sU rgT) C7 C8 1 := by
    rw [hC8]
    exact Work.IntLib.Eval.pop_cons (s := C7) (k := sU) (r := rgT) (g := Glyph.mk sU) (rest := bU)
      (by simpa using pU)
  have pV : C8.stk sV = Glyph.mk sV :: bV := by
    refine (dStO sS (Glyph.mk sS) rgT bS C6 sV (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT bR C5 sV (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT bQ C4 sV (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT bP C3 sV (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT bG C2 sV (by decide)).trans ?_
    exact dStK sV (Glyph.mk sV) rgT bV C1
  let C9 : State := ⟨Function.update C8.reg rgT (Glyph.mk sV), Function.update C8.stk sV bV⟩
  have hC9 : C9 = ⟨Function.update C8.reg rgT (Glyph.mk sV), Function.update C8.stk sV bV⟩ := rfl
  have eC9 : HvdH.Eval main (.pop sV rgT) C8 C9 1 := by
    rw [hC9]
    exact Work.IntLib.Eval.pop_cons (s := C8) (k := sV) (r := rgT) (g := Glyph.mk sV) (rest := bV)
      (by simpa using pV)
  have pG : C9.stk sG = Glyph.mk sG :: bG := by
    refine (dStO sS (Glyph.mk sS) rgT bS C6 sG (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT bR C5 sG (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT bQ C4 sG (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT bP C3 sG (by decide)).trans ?_
    exact dStK sG (Glyph.mk sG) rgT bG C2
  let C10 : State := ⟨Function.update C9.reg rgT (Glyph.mk sG), Function.update C9.stk sG bG⟩
  have hC10 : C10 = ⟨Function.update C9.reg rgT (Glyph.mk sG), Function.update C9.stk sG bG⟩ := rfl
  have eC10 : HvdH.Eval main (.pop sG rgT) C9 C10 1 := by
    rw [hC10]
    exact Work.IntLib.Eval.pop_cons (s := C9) (k := sG) (r := rgT) (g := Glyph.mk sG) (rest := bG)
      (by simpa using pG)
  have pP : C10.stk sP = Glyph.mk sP :: bP := by
    refine (dStO sS (Glyph.mk sS) rgT bS C6 sP (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT bR C5 sP (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT bQ C4 sP (by decide)).trans ?_
    exact dStK sP (Glyph.mk sP) rgT bP C3
  let C11 : State := ⟨Function.update C10.reg rgT (Glyph.mk sP), Function.update C10.stk sP bP⟩
  have hC11 : C11 = ⟨Function.update C10.reg rgT (Glyph.mk sP),
      Function.update C10.stk sP bP⟩ := rfl
  have eC11 : HvdH.Eval main (.pop sP rgT) C10 C11 1 := by
    rw [hC11]
    exact Work.IntLib.Eval.pop_cons (s := C10) (k := sP) (r := rgT) (g := Glyph.mk sP) (rest := bP)
      (by simpa using pP)
  have pQ : C11.stk sQ = Glyph.mk sQ :: bQ := by
    refine (dStO sS (Glyph.mk sS) rgT bS C6 sQ (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT bR C5 sQ (by decide)).trans ?_
    exact dStK sQ (Glyph.mk sQ) rgT bQ C4
  let C12 : State := ⟨Function.update C11.reg rgT (Glyph.mk sQ), Function.update C11.stk sQ bQ⟩
  have hC12 : C12 = ⟨Function.update C11.reg rgT (Glyph.mk sQ),
      Function.update C11.stk sQ bQ⟩ := rfl
  have eC12 : HvdH.Eval main (.pop sQ rgT) C11 C12 1 := by
    rw [hC12]
    exact Work.IntLib.Eval.pop_cons (s := C11) (k := sQ) (r := rgT) (g := Glyph.mk sQ) (rest := bQ)
      (by simpa using pQ)
  have pR : C12.stk sR = Glyph.mk sR :: bR := by
    refine (dStO sS (Glyph.mk sS) rgT bS C6 sR (by decide)).trans ?_
    exact dStK sR (Glyph.mk sR) rgT bR C5
  let C13 : State := ⟨Function.update C12.reg rgT (Glyph.mk sR), Function.update C12.stk sR bR⟩
  have hC13 : C13 = ⟨Function.update C12.reg rgT (Glyph.mk sR),
      Function.update C12.stk sR bR⟩ := rfl
  have eC13 : HvdH.Eval main (.pop sR rgT) C12 C13 1 := by
    rw [hC13]
    exact Work.IntLib.Eval.pop_cons (s := C12) (k := sR) (r := rgT) (g := Glyph.mk sR) (rest := bR)
      (by simpa using pR)
  have pS : C13.stk sS = Glyph.mk sS :: bS := dStK sS (Glyph.mk sS) rgT bS C6
  let C14 : State := ⟨Function.update C13.reg rgT (Glyph.mk sS), Function.update C13.stk sS bS⟩
  have hC14 : C14 = ⟨Function.update C13.reg rgT (Glyph.mk sS),
      Function.update C13.stk sS bS⟩ := rfl
  have eC14 : HvdH.Eval main (.pop sS rgT) C13 C14 1 := by
    rw [hC14]
    exact Work.IntLib.Eval.pop_cons (s := C13) (k := sS) (r := rgT) (g := Glyph.mk sS) (rest := bS)
      (by simpa using pS)
  -- ## the final facts
  have hfinU : C14.stk sU = bU := by
    refine (updStkOGen C13 rgT (Glyph.mk sS) sS sU bS (by decide)).trans ?_
    refine (updStkOGen C12 rgT (Glyph.mk sR) sR sU bR (by decide)).trans ?_
    refine (updStkOGen C11 rgT (Glyph.mk sQ) sQ sU bQ (by decide)).trans ?_
    refine (updStkOGen C10 rgT (Glyph.mk sP) sP sU bP (by decide)).trans ?_
    refine (updStkOGen C9 rgT (Glyph.mk sG) sG sU bG (by decide)).trans ?_
    refine (updStkOGen C8 rgT (Glyph.mk sV) sV sU bV (by decide)).trans ?_
    exact updStkGen C7 rgT (Glyph.mk sU) sU bU
  have hfinV : C14.stk sV = bV := by
    refine (updStkOGen C13 rgT (Glyph.mk sS) sS sV bS (by decide)).trans ?_
    refine (updStkOGen C12 rgT (Glyph.mk sR) sR sV bR (by decide)).trans ?_
    refine (updStkOGen C11 rgT (Glyph.mk sQ) sQ sV bQ (by decide)).trans ?_
    refine (updStkOGen C10 rgT (Glyph.mk sP) sP sV bP (by decide)).trans ?_
    refine (updStkOGen C9 rgT (Glyph.mk sG) sG sV bG (by decide)).trans ?_
    exact updStkGen C8 rgT (Glyph.mk sV) sV bV
  have hfinG : C14.stk sG = bG := by
    refine (updStkOGen C13 rgT (Glyph.mk sS) sS sG bS (by decide)).trans ?_
    refine (updStkOGen C12 rgT (Glyph.mk sR) sR sG bR (by decide)).trans ?_
    refine (updStkOGen C11 rgT (Glyph.mk sQ) sQ sG bQ (by decide)).trans ?_
    refine (updStkOGen C10 rgT (Glyph.mk sP) sP sG bP (by decide)).trans ?_
    exact updStkGen C9 rgT (Glyph.mk sG) sG bG
  have hfinP : C14.stk sP = bP := by
    refine (updStkOGen C13 rgT (Glyph.mk sS) sS sP bS (by decide)).trans ?_
    refine (updStkOGen C12 rgT (Glyph.mk sR) sR sP bR (by decide)).trans ?_
    refine (updStkOGen C11 rgT (Glyph.mk sQ) sQ sP bQ (by decide)).trans ?_
    exact updStkGen C10 rgT (Glyph.mk sP) sP bP
  have hfinQ : C14.stk sQ = bQ := by
    refine (updStkOGen C13 rgT (Glyph.mk sS) sS sQ bS (by decide)).trans ?_
    refine (updStkOGen C12 rgT (Glyph.mk sR) sR sQ bR (by decide)).trans ?_
    exact updStkGen C11 rgT (Glyph.mk sQ) sQ bQ
  have hfinR : C14.stk sR = bR :=
    (updStkOGen C13 rgT (Glyph.mk sS) sS sR bS (by decide)).trans
      (updStkGen C12 rgT (Glyph.mk sR) sR bR)
  have hfinS : C14.stk sS = bS := updStkGen C13 rgT (Glyph.mk sS) sS bS
  -- ## the composition: `gcdFinish ; gcdClean`
  have hF1 : Work.Layout.Ev main (SG.rLoop sU (Glyph.mk sU) (some sP) rgT) s s1
      (12 * (ul.length + 1)) := by
    refine ⟨m1, e1, ?_⟩
    have h : (ul.map Glyph.bit).length = ul.length := List.length_map Glyph.bit
    rw [h] at hm1
    omega
  have hF2 : Work.Layout.Ev main (SG.stripZeros sP rgT) s1 s2 (8 * (ul.length + 1)) := by
    refine ⟨m2, e2, ?_⟩
    have h : (ul.reverse).length = ul.length := List.length_reverse
    rw [h] at hm2
    omega
  have hF3 : Work.Layout.Ev main (.set rgU Glyph.iend) s2
      ⟨Function.update s2.reg rgU Glyph.iend, s2.stk⟩ 1 := ⟨1, e3a, le_rfl⟩
  have hF4 : Work.Layout.Ev main (.push 0 rgU)
      ⟨Function.update s2.reg rgU Glyph.iend, s2.stk⟩ S3 1 := ⟨1, e3b, le_rfl⟩
  have hF5 : Work.Layout.Ev main (SG.rLoop sP (Glyph.mk sP) (some 0) rgT) S3 s4
      (12 * (ul.length + 1)) := by
    refine ⟨m4, e4, ?_⟩
    have h := hm4
    have h4 : ((dropLead (ul.reverse)).map Glyph.bit).length = (dropLead (ul.reverse)).length :=
      List.length_map Glyph.bit
    rw [h4] at h
    have h2 := length_dropLead_le ul.reverse
    have h3 : (ul.reverse).length = ul.length := List.length_reverse
    rw [h3] at h2
    omega
  have hF6 : Work.Layout.Ev main (.set rgU Glyph.pos) s4
      ⟨Function.update s4.reg rgU Glyph.pos, s4.stk⟩ 1 := ⟨1, Eval.set rgU Glyph.pos s4, le_rfl⟩
  have hF7 : Work.Layout.Ev main (.push 0 rgU)
      ⟨Function.update s4.reg rgU Glyph.pos, s4.stk⟩ s5 1 := ⟨1, Eval.push 0 rgU _, le_rfl⟩
  have hF7s : Work.Layout.Ev main (Work.Layout.seqs [.push 0 rgU])
      ⟨Function.update s4.reg rgU Glyph.pos, s4.stk⟩ s5 1 := hF7
  have hFinEq : gcdFinish = Work.Layout.seqs [SG.rLoop sU (Glyph.mk sU) (some sP) rgT,
      SG.stripZeros sP rgT, .set rgU Glyph.iend, .push 0 rgU,
      SG.rLoop sP (Glyph.mk sP) (some 0) rgT, .set rgU Glyph.pos, .push 0 rgU] := rfl
  have hFin : Work.Layout.Ev main gcdFinish s s5
      (12 * (ul.length + 1) + (8 * (ul.length + 1) + (1 + (1 + (12 * (ul.length + 1) + (1 + 1)))))) := by
    rw [hFinEq]
    exact Work.Layout.Ev.seqs_cons hF1 (Work.Layout.Ev.seqs_cons hF2
      (Work.Layout.Ev.seqs_cons hF3 (Work.Layout.Ev.seqs_cons hF4
        (Work.Layout.Ev.seqs_cons hF5 (Work.Layout.Ev.seqs_cons hF6 hF7s)))))
  have hC1 : Work.Layout.Ev main (SG.rLoop sU (Glyph.mk sU) none rgT) s5 C1 7 :=
    ⟨7, eC1, le_rfl⟩
  have hC2 : Work.Layout.Ev main (SG.rLoop sV (Glyph.mk sV) none rgT) C1 C2
      (20 * vl.length + 20) := by
    refine ⟨7 + (vl.map Glyph.bit).length * 5, eC2, ?_⟩
    have h : (vl.map Glyph.bit).length = vl.length := List.length_map Glyph.bit
    rw [h]
    omega
  have hC3 : Work.Layout.Ev main (SG.rLoop sG (Glyph.mk sG) none rgT) C2 C3
      (20 * k + 20) := by
    refine ⟨7 + (List.replicate k gTick).length * 5, eC3, ?_⟩
    have h : (List.replicate k gTick).length = k := List.length_replicate
    rw [h]
    omega
  have hC4 : Work.Layout.Ev main (SG.rLoop sP (Glyph.mk sP) none rgT) C3 C4 7 :=
    ⟨7, eC4, le_rfl⟩
  have hC5 : Work.Layout.Ev main (SG.rLoop sQ (Glyph.mk sQ) none rgT) C4 C5 7 :=
    ⟨7, eC5, le_rfl⟩
  have hC6 : Work.Layout.Ev main (SG.rLoop sR (Glyph.mk sR) none rgT) C5 C6 7 :=
    ⟨7, eC6, le_rfl⟩
  have hC7 : Work.Layout.Ev main (SG.rLoop sS (Glyph.mk sS) none rgT) C6 C7 7 :=
    ⟨7, eC7, le_rfl⟩
  have hC8 : Work.Layout.Ev main (.pop sU rgT) C7 C8 1 := ⟨1, eC8, le_rfl⟩
  have hC9 : Work.Layout.Ev main (.pop sV rgT) C8 C9 1 := ⟨1, eC9, le_rfl⟩
  have hC10 : Work.Layout.Ev main (.pop sG rgT) C9 C10 1 := ⟨1, eC10, le_rfl⟩
  have hC11 : Work.Layout.Ev main (.pop sP rgT) C10 C11 1 := ⟨1, eC11, le_rfl⟩
  have hC12 : Work.Layout.Ev main (.pop sQ rgT) C11 C12 1 := ⟨1, eC12, le_rfl⟩
  have hC13 : Work.Layout.Ev main (.pop sR rgT) C12 C13 1 := ⟨1, eC13, le_rfl⟩
  have hC14s : Work.Layout.Ev main (Work.Layout.seqs [.pop sS rgT]) C13 C14 1 :=
    ⟨1, eC14, le_rfl⟩
  have hClnEq : gcdClean = Work.Layout.seqs [SG.rLoop sU (Glyph.mk sU) none rgT,
      SG.rLoop sV (Glyph.mk sV) none rgT, SG.rLoop sG (Glyph.mk sG) none rgT,
      SG.rLoop sP (Glyph.mk sP) none rgT, SG.rLoop sQ (Glyph.mk sQ) none rgT,
      SG.rLoop sR (Glyph.mk sR) none rgT, SG.rLoop sS (Glyph.mk sS) none rgT,
      .pop sU rgT, .pop sV rgT, .pop sG rgT, .pop sP rgT, .pop sQ rgT, .pop sR rgT,
      .pop sS rgT] := rfl
  have hCln : Work.Layout.Ev main gcdClean s5 C14
      (7 + ((20 * vl.length + 20) + ((20 * k + 20) + (7 + (7 + (7 + (7 + (1 + (1 + (1 + (1 +
        (1 + (1 + 1))))))))))))) := by
    rw [hClnEq]
    exact Work.Layout.Ev.seqs_cons hC1 (Work.Layout.Ev.seqs_cons hC2
      (Work.Layout.Ev.seqs_cons hC3 (Work.Layout.Ev.seqs_cons hC4
        (Work.Layout.Ev.seqs_cons hC5 (Work.Layout.Ev.seqs_cons hC6
          (Work.Layout.Ev.seqs_cons hC7 (Work.Layout.Ev.seqs_cons hC8
            (Work.Layout.Ev.seqs_cons hC9 (Work.Layout.Ev.seqs_cons hC10
              (Work.Layout.Ev.seqs_cons hC11 (Work.Layout.Ev.seqs_cons hC12
                (Work.Layout.Ev.seqs_cons hC13 hC14s))))))))))))
  obtain ⟨n, hEval, hn⟩ := Work.Layout.Ev.seq hFin hCln
  have hgoal0 : (HvdH.Val.int ((Work.IntLib.ofBits ul : ℕ) : ℤ)).enc ++ R
      = Glyph.pos :: (((dropLead (ul.reverse)).map Glyph.bit).reverse ++ (Glyph.iend :: R)) := by
    rw [enc_ofBits, stripHigh_rev_map ul]
    simp
  have hC140 : C14.stk 0 = s5.stk 0 := by
    refine (updStkOGen C13 rgT (Glyph.mk sS) sS 0 bS (by decide)).trans ?_
    refine (updStkOGen C12 rgT (Glyph.mk sR) sR 0 bR (by decide)).trans ?_
    refine (updStkOGen C11 rgT (Glyph.mk sQ) sQ 0 bQ (by decide)).trans ?_
    refine (updStkOGen C10 rgT (Glyph.mk sP) sP 0 bP (by decide)).trans ?_
    refine (updStkOGen C9 rgT (Glyph.mk sG) sG 0 bG (by decide)).trans ?_
    refine (updStkOGen C8 rgT (Glyph.mk sV) sV 0 bV (by decide)).trans ?_
    refine (updStkOGen C7 rgT (Glyph.mk sU) sU 0 bU (by decide)).trans ?_
    refine (dStO sS (Glyph.mk sS) rgT bS C6 0 (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT bR C5 0 (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT bQ C4 0 (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT bP C3 0 (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT bG C2 0 (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT bV C1 0 (by decide)).trans ?_
    exact dStO sU (Glyph.mk sU) rgT bU s5 0 (by decide)
  have h0fin : C14.stk 0
      = (HvdH.Val.int ((Work.IntLib.ofBits ul : ℕ) : ℤ)).enc ++ R := by
    rw [hC140, t50', ← hgoal0]
  refine ⟨C14, n, hEval, by omega, h0fin, hfinU, hfinV, hfinG, hfinP, hfinQ, hfinR,
    hfinS, ?_⟩
  intro j hj0 hjU hjV hjG hjP hjQ hjR hjS
  refine Work.Layout.Eval.stk_frame hEval (fun hmem => ?_)
  have hsub : Work.Layout.cmdTouches (HvdH.Cmd.seq gcdFinish gcdClean) ⊆
      ({0, sU, sV, sG, sP, sQ, sR, sS} : Finset Stk) := by decide
  have hmem' := hsub hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
  tauto

end Work.IntLib.SqrtGcd
