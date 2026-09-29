import Mathlib
import Submission.Work.IntLib.SqrtGcd.gcdGenAux
import Submission.Work.IntLib.SqrtGcd.gcdPhaseAEval

/-!
# `gcdRun` with junk below the frame markers

`SqrtGcd/gcdFinishEval.lean` specifies `SG.gcdRun` (strip the common power of two, binary gcd on
the odd parts, rescale) for a state whose seven scratch stacks hold only their markers.  Here the
same word is specified with arbitrary junk below the markers: every phase of `gcdRun` works
strictly above the markers, so the junk is carried along unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH
open Work.IntLib.SG

/-- The head of a bit region (with junk below its marker) is its first bit. -/
theorem headD_eq_bitGen {U U' : List Bool} {x : Bool} {T : Glyph} {b : List Glyph}
    (h : U = x :: U') : (U.map Glyph.bit ++ T :: b).headD Glyph.eos = Glyph.bit x := by
  rw [h]; rfl

/-- The head of an empty bit region (with junk below its marker) is the marker. -/
theorem headD_eq_mkGen {U : List Bool} {T : Glyph} {b : List Glyph} (h : U = []) :
    (U.map Glyph.bit ++ T :: b).headD Glyph.eos = T := by
  rw [h]; rfl

/-! ## The branches of the run tail -/

/-- Branch A (the region of `sU` is empty): move the region of `sV` onto `sU` and rescale. -/
theorem gcdRunBranchAGen (main : HvdH.Cmd) (V : List Bool) (k : ℕ)
    (bU bV bG bR : List HvdH.Glyph) (s : HvdH.State)
    (hU : s.stk sU = Glyph.mk sU :: bU)
    (hV : s.stk sV = V.map Glyph.bit ++ Glyph.mk sV :: bV)
    (hG : s.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG)
    (hR : s.stk sR = Glyph.mk sR :: bR) :
    ∃ s' m, HvdH.Eval main (Work.Layout.seqs [moveSame sV sU sR rgT, gcdScale]) s s' m ∧
      m ≤ 200 * (k + V.length + 1) ∧
      s'.stk sU = (List.replicate k false ++ V).map Glyph.bit ++ Glyph.mk sU :: bU ∧
      s'.stk sV = Glyph.mk sV :: bV ∧
      s'.stk sG = Glyph.mk sG :: bG ∧
      s'.stk sR = Glyph.mk sR :: bR ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sR → s'.stk j = s.stk j) := by
  obtain ⟨s1, m1, hev1, hm1, hs1U, hs1V, hs1R, hfr1⟩ := moveSameVURGen main V bV bR s hV hR
  have hs1U' : s1.stk sU = V.map Glyph.bit ++ Glyph.mk sU :: bU := by
    rw [hs1U, hU]
  have hs1G : s1.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG := by
    rw [hfr1 sG (by decide) (by decide) (by decide)]
    exact hG
  obtain ⟨s2, m2, hev2, hm2, hs2U, hs2G, hfr2⟩ :=
    gcdScaleEvalGen main k V bU bG s1 hs1U' hs1G
  have hs2V : s2.stk sV = Glyph.mk sV :: bV := by
    rw [hfr2 sV (by decide) (by decide)]
    exact hs1V
  have hs2R : s2.stk sR = Glyph.mk sR :: bR := by
    rw [hfr2 sR (by decide) (by decide)]
    exact hs1R
  refine ⟨s2, m1 + m2, Eval.seq hev1 hev2, by omega, hs2U, hs2V, hs2G, hs2R, ?_⟩
  intro j ha hb hc hd
  exact (hfr2 j ha hc).trans (hfr1 j hb ha hd)

/-- Branch B2 (both regions nonempty): strip the low zeros, run the binary gcd, rescale. -/
theorem gcdRunBranchB2Gen (main : HvdH.Cmd) (U V : List Bool) (k : ℕ)
    (bU bV bG bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (hU : s.stk sU = U.map Glyph.bit ++ Glyph.mk sU :: bU)
    (hV : s.stk sV = V.map Glyph.bit ++ Glyph.mk sV :: bV)
    (hG : s.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG)
    (hP : s.stk sP = Glyph.mk sP :: bP) (hQ : s.stk sQ = Glyph.mk sQ :: bQ)
    (hR : s.stk sR = Glyph.mk sR :: bR) (hS : s.stk sS = Glyph.mk sS :: bS)
    (hoddU : Work.IntLib.ofBits (dropLead U) % 2 = 1)
    (hoddV : Work.IntLib.ofBits (dropLead V) % 2 = 1) :
    ∃ s' m, HvdH.Eval main (Work.Layout.seqs [gcdOdd, gcdMain, gcdScale]) s s' m ∧
      m ≤ 11000 * (U.length + V.length + k + 1) * (U.length + V.length + k + 1) + 11000 ∧
      (∃ ul : List Bool, s'.stk sU = (List.replicate k false ++ ul).map Glyph.bit
          ++ Glyph.mk sU :: bU ∧
        Work.IntLib.ofBits ul
          = Nat.gcd (Work.IntLib.ofBits (dropLead U)) (Work.IntLib.ofBits (dropLead V)) ∧
        ul.length ≤ max U.length V.length) ∧
      (∃ vl : List Bool, s'.stk sV = vl.map Glyph.bit ++ Glyph.mk sV :: bV ∧
        vl.length ≤ max U.length V.length) ∧
      s'.stk sG = Glyph.mk sG :: bG ∧ s'.stk sP = Glyph.mk sP :: bP ∧
      s'.stk sQ = Glyph.mk sQ :: bQ ∧
      s'.stk sR = Glyph.mk sR :: bR ∧ s'.stk sS = Glyph.mk sS :: bS ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  obtain ⟨s1, m1, hev1, hm1, hU1, hfr1⟩ := stripZerosRegionGen main sU U bU s hU
  have hV1 : s1.stk sV = V.map Glyph.bit ++ Glyph.mk sV :: bV := by
    rw [hfr1 sV (by decide)]
    exact hV
  obtain ⟨s2, m2, hev2, hm2, hV2, hfr2⟩ := stripZerosRegionGen main sV V bV s1 hV1
  have hP1 : s1.stk sP = Glyph.mk sP :: bP := by rw [hfr1 sP (by decide)]; exact hP
  have hQ1 : s1.stk sQ = Glyph.mk sQ :: bQ := by rw [hfr1 sQ (by decide)]; exact hQ
  have hR1 : s1.stk sR = Glyph.mk sR :: bR := by rw [hfr1 sR (by decide)]; exact hR
  have hS1 : s1.stk sS = Glyph.mk sS :: bS := by rw [hfr1 sS (by decide)]; exact hS
  have hP2 : s2.stk sP = Glyph.mk sP :: bP := by rw [hfr2 sP (by decide)]; exact hP1
  have hQ2 : s2.stk sQ = Glyph.mk sQ :: bQ := by rw [hfr2 sQ (by decide)]; exact hQ1
  have hR2 : s2.stk sR = Glyph.mk sR :: bR := by rw [hfr2 sR (by decide)]; exact hR1
  have hS2 : s2.stk sS = Glyph.mk sS :: bS := by rw [hfr2 sS (by decide)]; exact hS1
  have hG2 : s2.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG := by
    rw [hfr2 sG (by decide), hfr1 sG (by decide)]
    exact hG
  have hevOdd : HvdH.Eval main gcdOdd s s2 (m1 + m2) := Eval.seq hev1 hev2
  have hU2 : s2.stk sU = (dropLead U).map Glyph.bit ++ Glyph.mk sU :: bU := by
    rw [hfr2 sU (by decide)]
    exact hU1
  obtain ⟨s3, m3, hev3, hm3, ⟨ul', hUl', hUl'v, hUl'len⟩, ⟨vl', hVl', hVl'len⟩, hP3, hQ3, hR3,
    hS3, hG3, hfr3⟩ :=
    gcdMainEvalFull main (dropLead U) (dropLead V) bU bV bP bQ bR bS s2 hU2 hV2 hP2 hQ2 hR2 hS2
      hoddU hoddV
  have hG3' : s3.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG := by
    rw [hG3]; exact hG2
  obtain ⟨s4, m4, hev4, hm4, hU4, hG4, hfr4⟩ :=
    gcdScaleEvalGen main k ul' bU bG s3 hUl' hG3'
  have hevAll : HvdH.Eval main (Work.Layout.seqs [gcdOdd, gcdMain, gcdScale]) s s4
      (m1 + m2 + (m3 + m4)) := Eval.seq hevOdd (Eval.seq hev3 hev4)
  have hlen1 : ul'.length ≤ max U.length V.length :=
    le_trans hUl'len (max_le_max (length_dropLead_le U) (length_dropLead_le V))
  have hlen2 : vl'.length ≤ max U.length V.length :=
    le_trans hVl'len (max_le_max (length_dropLead_le U) (length_dropLead_le V))
  have hcost : m1 + m2 + (m3 + m4)
      ≤ 11000 * (U.length + V.length + k + 1) * (U.length + V.length + k + 1) + 11000 := by
    have hsum : (dropLead U).length + (dropLead V).length ≤ U.length + V.length := by
      have h1 := length_dropLead_le U
      have h2 := length_dropLead_le V
      omega
    have h3' : m3 ≤ 10000 * (U.length + V.length + 1) * (U.length + V.length + 1) + 10000 := by
      nlinarith only [hm3, hsum]
    have hsq : (U.length + V.length + 1) * (U.length + V.length + 1)
        ≤ (U.length + V.length + k + 1) * (U.length + V.length + k + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hL2 : U.length + V.length + k + 1
        ≤ (U.length + V.length + k + 1) * (U.length + V.length + k + 1) := by
      have : 1 ≤ U.length + V.length + k + 1 := by omega
      nlinarith
    have hlin : 2 * (U.length + 1) + 6 + (2 * (V.length + 1) + 6) + 100 * (k + 1)
        ≤ 1000 * (U.length + V.length + k + 1) * (U.length + V.length + k + 1) + 1000 := by
      nlinarith [hL2, Nat.zero_le U.length, Nat.zero_le V.length, Nat.zero_le k]
    nlinarith only [hm1, hm2, hm4, h3', hsq, hlin]
  refine ⟨s4, m1 + m2 + (m3 + m4), hevAll, hcost, ⟨ul', hU4, hUl'v, hlen1⟩,
    ⟨vl', ?_, hlen2⟩, hG4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr4 sV (by decide) (by decide)]; exact hVl'
  · rw [hfr4 sP (by decide) (by decide)]; exact hP3
  · rw [hfr4 sQ (by decide) (by decide)]; exact hQ3
  · rw [hfr4 sR (by decide) (by decide)]; exact hR3
  · rw [hfr4 sS (by decide) (by decide)]; exact hS3
  · intro j ha hb hc hd he hf hg
    exact (hfr4 j ha hc).trans ((hfr3 j ha hb hc hd he hf hg).trans
      ((hfr2 j hb).trans (hfr1 j ha)))

/-! ## The three tails of `gcdRun` -/

/-- The run tail when the region of `sU` is empty. -/
theorem gcdRunTailUemptyGen (main : HvdH.Cmd) (U V : List Bool) (k : ℕ)
    (bU bV bG bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (hU : s.stk sU = U.map Glyph.bit ++ Glyph.mk sU :: bU) (hUnil : U = [])
    (hV : s.stk sV = V.map Glyph.bit ++ Glyph.mk sV :: bV)
    (hG : s.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG)
    (hP : s.stk sP = Glyph.mk sP :: bP) (hQ : s.stk sQ = Glyph.mk sQ :: bQ)
    (hR : s.stk sR = Glyph.mk sR :: bR) (hS : s.stk sS = Glyph.mk sS :: bS) :
    ∃ s' m, HvdH.Eval main gcdRunTail s s' m ∧ m ≤ 300 * (V.length + k + 1) ∧
      s'.stk sU = (List.replicate k false ++ V).map Glyph.bit ++ Glyph.mk sU :: bU ∧
      s'.stk sV = Glyph.mk sV :: bV ∧ s'.stk sG = Glyph.mk sG :: bG ∧
      s'.stk sP = Glyph.mk sP :: bP ∧ s'.stk sQ = Glyph.mk sQ :: bQ ∧
      s'.stk sR = Glyph.mk sR :: bR ∧ s'.stk sS = Glyph.mk sS :: bS ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  have hhead : (s.stk sU).headD Glyph.eos = Glyph.mk sU := by
    rw [hU]
    exact headD_eq_mkGen hUnil
  have hreg : (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State).reg rgT
      = Glyph.mk sU := by
    rw [regPeek, hhead]
  obtain ⟨s', m', hev', hm', hU', hV', hG', hR', hfr'⟩ :=
    gcdRunBranchAGen main V k bU bV bG bR
      (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State)
      (by simp only [hU, hUnil, List.map_nil, List.nil_append]) hV hG hR
  have hP' : s'.stk sP = Glyph.mk sP :: bP := by
    rw [hfr' sP (by decide) (by decide) (by decide) (by decide)]
    exact hP
  have hQ' : s'.stk sQ = Glyph.mk sQ :: bQ := by
    rw [hfr' sQ (by decide) (by decide) (by decide) (by decide)]
    exact hQ
  have hS' : s'.stk sS = Glyph.mk sS :: bS := by
    rw [hfr' sS (by decide) (by decide) (by decide) (by decide)]
    exact hS
  have hmain : HvdH.Eval main gcdRunTail s s' (m' + 2) := by
    have h1 : HvdH.Eval main gcdRunTail s s' (1 + (m' + 1)) :=
      Eval.seq (evalPeek main sU rgT s) (Eval.iteT hreg hev')
    have hc : (1 : ℕ) + (m' + 1) = m' + 2 := by omega
    simpa [hc] using h1
  refine ⟨s', m' + 2, hmain, by omega, hU', hV', hG', hP', hQ', hR', hS', ?_⟩
  intro j ha hb hc _ _ hf _
  exact hfr' j ha hb hc hf

/-- The run tail when the region of `sU` is nonempty but that of `sV` is empty. -/
theorem gcdRunTailVemptyGen (main : HvdH.Cmd) (U V : List Bool) (b : Bool) (U' : List Bool)
    (k : ℕ) (bU bV bG bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (hU : s.stk sU = U.map Glyph.bit ++ Glyph.mk sU :: bU) (hUeq : U = b :: U')
    (hV : s.stk sV = V.map Glyph.bit ++ Glyph.mk sV :: bV) (hVnil : V = [])
    (hG : s.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG)
    (hP : s.stk sP = Glyph.mk sP :: bP) (hQ : s.stk sQ = Glyph.mk sQ :: bQ)
    (hR : s.stk sR = Glyph.mk sR :: bR) (hS : s.stk sS = Glyph.mk sS :: bS) :
    ∃ s' m, HvdH.Eval main gcdRunTail s s' m ∧ m ≤ 300 * (U.length + k + 1) ∧
      s'.stk sU = (List.replicate k false ++ U).map Glyph.bit ++ Glyph.mk sU :: bU ∧
      s'.stk sV = Glyph.mk sV :: bV ∧ s'.stk sG = Glyph.mk sG :: bG ∧
      s'.stk sP = Glyph.mk sP :: bP ∧ s'.stk sQ = Glyph.mk sQ :: bQ ∧
      s'.stk sR = Glyph.mk sR :: bR ∧ s'.stk sS = Glyph.mk sS :: bS ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  have hheadU : (s.stk sU).headD Glyph.eos = Glyph.bit b := by
    rw [hU]
    exact headD_eq_bitGen hUeq
  have hheadV : (s.stk sV).headD Glyph.eos = Glyph.mk sV := by
    rw [hV]
    exact headD_eq_mkGen hVnil
  have hne : (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State).reg rgT
      ≠ Glyph.mk sU := by
    rw [regPeek, hheadU]
    exact gBit_ne_mk b sU
  have hreg2 : (⟨Function.update (Function.update s.reg rgT ((s.stk sU).headD Glyph.eos)) rgU
        ((s.stk sV).headD Glyph.eos), s.stk⟩ : State).reg rgU = Glyph.mk sV := by
    rw [regPeek2, hheadV]
  obtain ⟨s', m', hev', hm', hU', hG', hfr'⟩ :=
    gcdScaleEvalGen main k U bU bG
      (⟨Function.update (Function.update s.reg rgT ((s.stk sU).headD Glyph.eos)) rgU
        ((s.stk sV).headD Glyph.eos), s.stk⟩ : State) hU hG
  have hmain : HvdH.Eval main gcdRunTail s s' (m' + 4) := by
    have h2 : HvdH.Eval main (Work.Layout.seqs [.peek sV rgU,
        .ite rgU (Glyph.mk sV) gcdScale (Work.Layout.seqs [gcdOdd, gcdMain, gcdScale])])
        (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State) s'
        (1 + (m' + 1)) :=
      Eval.seq (evalPeek2 main sU rgT s sV rgU) (Eval.iteT hreg2 hev')
    have h1 : HvdH.Eval main gcdRunTail s s' (1 + ((1 + (m' + 1)) + 1)) :=
      Eval.seq (evalPeek main sU rgT s) (Eval.iteF hne h2)
    have hc : (1 : ℕ) + ((1 + (m' + 1)) + 1) = m' + 4 := by omega
    simpa [hc] using h1
  have hV' : s'.stk sV = Glyph.mk sV :: bV := by
    rw [hfr' sV (by decide) (by decide)]
    simp only [hV, hVnil, List.map_nil, List.nil_append]
  refine ⟨s', m' + 4, hmain, by omega, hU', hV', hG', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr' sP (by decide) (by decide)]; exact hP
  · rw [hfr' sQ (by decide) (by decide)]; exact hQ
  · rw [hfr' sR (by decide) (by decide)]; exact hR
  · rw [hfr' sS (by decide) (by decide)]; exact hS
  · intro j ha hb hc hd he hf hg
    exact (hfr' j ha hc).trans (stkUpd s rgT ((s.stk sU).headD Glyph.eos) j)

/-- The run tail when both regions are nonempty. -/
theorem gcdRunTailBothGen (main : HvdH.Cmd) (U V : List Bool) (b c : Bool) (U' V' : List Bool)
    (k : ℕ) (bU bV bG bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (hU : s.stk sU = U.map Glyph.bit ++ Glyph.mk sU :: bU) (hUeq : U = b :: U')
    (hV : s.stk sV = V.map Glyph.bit ++ Glyph.mk sV :: bV) (hVeq : V = c :: V')
    (hG : s.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG)
    (hP : s.stk sP = Glyph.mk sP :: bP) (hQ : s.stk sQ = Glyph.mk sQ :: bQ)
    (hR : s.stk sR = Glyph.mk sR :: bR) (hS : s.stk sS = Glyph.mk sS :: bS)
    (hoddU : Work.IntLib.ofBits (dropLead U) % 2 = 1)
    (hoddV : Work.IntLib.ofBits (dropLead V) % 2 = 1) :
    ∃ s' m, HvdH.Eval main gcdRunTail s s' m ∧
      m ≤ 12000 * (U.length + V.length + k + 1) * (U.length + V.length + k + 1) + 12000 ∧
      (∃ ul : List Bool, s'.stk sU = (List.replicate k false ++ ul).map Glyph.bit
          ++ Glyph.mk sU :: bU ∧
        Work.IntLib.ofBits ul
          = Nat.gcd (Work.IntLib.ofBits (dropLead U)) (Work.IntLib.ofBits (dropLead V)) ∧
        ul.length ≤ max U.length V.length) ∧
      (∃ vl : List Bool, s'.stk sV = vl.map Glyph.bit ++ Glyph.mk sV :: bV ∧
        vl.length ≤ max U.length V.length) ∧
      s'.stk sG = Glyph.mk sG :: bG ∧ s'.stk sP = Glyph.mk sP :: bP ∧
      s'.stk sQ = Glyph.mk sQ :: bQ ∧
      s'.stk sR = Glyph.mk sR :: bR ∧ s'.stk sS = Glyph.mk sS :: bS ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  have hheadU : (s.stk sU).headD Glyph.eos = Glyph.bit b := by
    rw [hU]
    exact headD_eq_bitGen hUeq
  have hheadV : (s.stk sV).headD Glyph.eos = Glyph.bit c := by
    rw [hV]
    exact headD_eq_bitGen hVeq
  have hne : (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State).reg rgT
      ≠ Glyph.mk sU := by
    rw [regPeek, hheadU]
    exact gBit_ne_mk b sU
  have hne2 : (⟨Function.update (Function.update s.reg rgT ((s.stk sU).headD Glyph.eos)) rgU
        ((s.stk sV).headD Glyph.eos), s.stk⟩ : State).reg rgU ≠ Glyph.mk sV := by
    rw [regPeek2, hheadV]
    exact gBit_ne_mk c sV
  obtain ⟨s', m', hev', hm', hUl', hVl', hG', hP', hQ', hR', hS', hfr'⟩ :=
    gcdRunBranchB2Gen main U V k bU bV bG bP bQ bR bS
      (⟨Function.update (Function.update s.reg rgT ((s.stk sU).headD Glyph.eos)) rgU
        ((s.stk sV).headD Glyph.eos), s.stk⟩ : State)
      hU hV hG hP hQ hR hS hoddU hoddV
  have hmain : HvdH.Eval main gcdRunTail s s' (m' + 4) := by
    have h2 : HvdH.Eval main (Work.Layout.seqs [.peek sV rgU,
        .ite rgU (Glyph.mk sV) gcdScale (Work.Layout.seqs [gcdOdd, gcdMain, gcdScale])])
        (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State) s'
        (1 + (m' + 1)) :=
      Eval.seq (evalPeek2 main sU rgT s sV rgU) (Eval.iteF hne2 hev')
    have h1 : HvdH.Eval main gcdRunTail s s' (1 + ((1 + (m' + 1)) + 1)) :=
      Eval.seq (evalPeek main sU rgT s) (Eval.iteF hne h2)
    have hc : (1 : ℕ) + ((1 + (m' + 1)) + 1) = m' + 4 := by omega
    simpa [hc] using h1
  have hcost : m' + 4 ≤ 12000 * (U.length + V.length + k + 1) * (U.length + V.length + k + 1)
      + 12000 := by
    have h1 : 1 ≤ (U.length + V.length + k + 1) * (U.length + V.length + k + 1) := by
      have h2 : 1 ≤ U.length + V.length + k + 1 := by omega
      nlinarith
    nlinarith only [hm', h1]
  refine ⟨s', m' + 4, hmain, hcost, hUl', hVl', hG', hP', hQ', hR', hS', ?_⟩
  intro j ha hb hc hd he hf hg
  exact (hfr' j ha hb hc hd he hf hg).trans (stkUpd s rgT ((s.stk sU).headD Glyph.eos) j)

/-! ## The whole run phase -/

/-- **`gcdRun` with junk below the markers.** -/
theorem gcdRunEvalGen (main : HvdH.Cmd) (a b : ℤ) (bU bV bG bP bQ bR bS : List HvdH.Glyph)
    (s : HvdH.State)
    (hU : s.stk sU = a.natAbs.bits.map Glyph.bit ++ Glyph.mk sU :: bU)
    (hV : s.stk sV = b.natAbs.bits.map Glyph.bit ++ Glyph.mk sV :: bV)
    (hG : s.stk sG = Glyph.mk sG :: bG)
    (hP : s.stk sP = Glyph.mk sP :: bP) (hQ : s.stk sQ = Glyph.mk sQ :: bQ)
    (hR : s.stk sR = Glyph.mk sR :: bR) (hS : s.stk sS = Glyph.mk sS :: bS) :
    ∃ s' m, HvdH.Eval main gcdRun s s' m ∧
      m ≤ 60000 * (HvdH.isz a + HvdH.isz b + 1)
            * (HvdH.isz a + HvdH.isz b + 1) + 30000 ∧
      (∃ ul : List Bool, s'.stk sU = ul.map Glyph.bit ++ Glyph.mk sU :: bU ∧
        Work.IntLib.ofBits ul = Int.gcd a b ∧
        ul.length ≤ a.natAbs.size + b.natAbs.size) ∧
      (∃ vl : List Bool, s'.stk sV = vl.map Glyph.bit ++ Glyph.mk sV :: bV ∧
        vl.length ≤ a.natAbs.size + b.natAbs.size) ∧
      s'.stk sG = Glyph.mk sG :: bG ∧ s'.stk sP = Glyph.mk sP :: bP ∧
      s'.stk sQ = Glyph.mk sQ :: bQ ∧
      s'.stk sR = Glyph.mk sR :: bR ∧ s'.stk sS = Glyph.mk sS :: bS ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  obtain ⟨s1, m1, hev1, hm1, hU1, hV1, hG1, hfr1⟩ :=
    gcdPhaseAEval main a.natAbs.bits b.natAbs.bits [] bU bV bG s hU hV hG
  set k : ℕ := min ((a.natAbs.bits.takeWhile (fun b => !b)).length)
    ((b.natAbs.bits.takeWhile (fun b => !b)).length) with hk
  have hU1' : s1.stk sU = (a.natAbs.bits.drop k).map Glyph.bit ++ Glyph.mk sU :: bU := by
    rw [hk]; exact hU1
  have hV1' : s1.stk sV = (b.natAbs.bits.drop k).map Glyph.bit ++ Glyph.mk sV :: bV := by
    rw [hk]; exact hV1
  have hG1' : s1.stk sG = List.replicate k gTick ++ Glyph.mk sG :: bG := by
    rw [hk]; simpa using hG1
  have hP1 : s1.stk sP = Glyph.mk sP :: bP := by
    rw [hfr1 sP (by decide) (by decide) (by decide)]; exact hP
  have hQ1 : s1.stk sQ = Glyph.mk sQ :: bQ := by
    rw [hfr1 sQ (by decide) (by decide) (by decide)]; exact hQ
  have hR1 : s1.stk sR = Glyph.mk sR :: bR := by
    rw [hfr1 sR (by decide) (by decide) (by decide)]; exact hR
  have hS1 : s1.stk sS = Glyph.mk sS :: bS := by
    rw [hfr1 sS (by decide) (by decide) (by decide)]; exact hS
  have hkU : k ≤ nLead a.natAbs.bits := by rw [hk]; exact min_le_left _ _
  have hkV : k ≤ nLead b.natAbs.bits := by rw [hk]; exact min_le_right _ _
  have hisz : HvdH.isz a + HvdH.isz b + 1
      = (a.natAbs.size + b.natAbs.size) + 5 := by
    rw [Work.IntLib.isz_eq, Work.IntLib.isz_eq]; ring
  have hlenU : (a.natAbs.bits.drop k).length ≤ a.natAbs.size := by
    rw [List.length_drop, bits_len a.natAbs]
    exact Nat.sub_le _ _
  have hlenV : (b.natAbs.bits.drop k).length ≤ b.natAbs.size := by
    rw [List.length_drop, bits_len b.natAbs]
    exact Nat.sub_le _ _
  have hkU' : k ≤ a.natAbs.size :=
    le_trans hkU (le_trans (nLead_le_length (a.natAbs.bits)) (le_of_eq (bits_len a.natAbs)))
  have hkV' : k ≤ b.natAbs.size :=
    le_trans hkV (le_trans (nLead_le_length (b.natAbs.bits)) (le_of_eq (bits_len b.natAbs)))
  have hgcdInt : Int.gcd a b
      = Nat.gcd (Work.IntLib.ofBits (a.natAbs.bits)) (Work.IntLib.ofBits (b.natAbs.bits)) := by
    rw [Int.gcd_eq_natAbs, ofBits_bits_apply, ofBits_bits_apply]
  rcases hdU : a.natAbs.bits.drop k with _ | ⟨bU0, U'⟩
  · -- ### Case A: the region of `sU` is empty
    have hzeroU : Work.IntLib.ofBits (a.natAbs.bits) = 0 :=
      ofBits_eq_zero_of_drop_eq_nil _ k hkU hdU
    obtain ⟨s2, m2, hev2, hm2, hU2, hV2, hG2, hP2, hQ2, hR2, hS2, hfr2⟩ :=
      gcdRunTailUemptyGen main (a.natAbs.bits.drop k) (b.natAbs.bits.drop k) k bU bV bG bP bQ bR
        bS s1 hU1' hdU hV1' hG1' hP1 hQ1 hR1 hS1
    have hval : Work.IntLib.ofBits (List.replicate k false ++ b.natAbs.bits.drop k)
        = Int.gcd a b := by
      have h1 := ofBits_replicate_false_append k (b.natAbs.bits.drop k)
      have h2 : 2 ^ k * Work.IntLib.ofBits (b.natAbs.bits.drop k)
          = Work.IntLib.ofBits (b.natAbs.bits) := two_pow_mul_ofBits_drop _ k hkV
      have h3 : Work.IntLib.ofBits (b.natAbs.bits) = b.natAbs := ofBits_bits_apply b.natAbs
      calc Work.IntLib.ofBits (List.replicate k false ++ b.natAbs.bits.drop k)
          = 2 ^ k * Work.IntLib.ofBits (b.natAbs.bits.drop k) := h1
        _ = Work.IntLib.ofBits (b.natAbs.bits) := h2
        _ = b.natAbs := h3
        _ = Nat.gcd (Work.IntLib.ofBits (a.natAbs.bits)) (Work.IntLib.ofBits (b.natAbs.bits)) := by
              rw [hzeroU, Nat.gcd_zero_left, h3]
        _ = Int.gcd a b := hgcdInt.symm
    have hlen : (List.replicate k false ++ b.natAbs.bits.drop k).length
        ≤ a.natAbs.size + b.natAbs.size := by
      rw [List.length_append, List.length_replicate]
      omega
    have hevRun : HvdH.Eval main gcdRun s s2 (m1 + m2) := by
      rw [gcdRun_eq]; exact Eval.seq hev1 hev2
    refine ⟨s2, m1 + m2, hevRun, ?_, ⟨_, hU2, hval, hlen⟩, ⟨[], hV2, by simp⟩, hG2, hP2, hQ2,
      hR2, hS2, ?_⟩
    · have hsq : a.natAbs.size + b.natAbs.size + 5
          ≤ (a.natAbs.size + b.natAbs.size + 5) * (a.natAbs.size + b.natAbs.size + 5) :=
        le_mul_self_of_pos _ (by omega)
      have hAL : m1 + m2 ≤ 400 * (a.natAbs.size + b.natAbs.size + 5) := by omega
      rw [hisz]
      nlinarith only [hAL, hsq]
    · intro j ha hb hc hd he hf hg
      exact (hfr2 j ha hb hc hd he hf hg).trans (hfr1 j ha hb hc)
  · -- ### Cases B: the region of `sU` is `bU0 :: U'`
    rcases hdV : b.natAbs.bits.drop k with _ | ⟨cV, V'⟩
    · -- ### Case B1: the region of `sV` is empty
      have hzeroV : Work.IntLib.ofBits (b.natAbs.bits) = 0 :=
        ofBits_eq_zero_of_drop_eq_nil _ k hkV hdV
      obtain ⟨s2, m2, hev2, hm2, hU2, hV2, hG2, hP2, hQ2, hR2, hS2, hfr2⟩ :=
        gcdRunTailVemptyGen main (a.natAbs.bits.drop k) (b.natAbs.bits.drop k) bU0 U' k bU bV
          bG bP bQ bR bS s1 hU1' hdU hV1' hdV hG1' hP1 hQ1 hR1 hS1
      have hval : Work.IntLib.ofBits (List.replicate k false ++ a.natAbs.bits.drop k)
          = Int.gcd a b := by
        have h1 := ofBits_replicate_false_append k (a.natAbs.bits.drop k)
        have h2 : 2 ^ k * Work.IntLib.ofBits (a.natAbs.bits.drop k)
            = Work.IntLib.ofBits (a.natAbs.bits) := two_pow_mul_ofBits_drop _ k hkU
        have h3 : Work.IntLib.ofBits (a.natAbs.bits) = a.natAbs := ofBits_bits_apply a.natAbs
        calc Work.IntLib.ofBits (List.replicate k false ++ a.natAbs.bits.drop k)
            = 2 ^ k * Work.IntLib.ofBits (a.natAbs.bits.drop k) := h1
          _ = Work.IntLib.ofBits (a.natAbs.bits) := h2
          _ = a.natAbs := h3
          _ = Nat.gcd (Work.IntLib.ofBits (a.natAbs.bits)) (Work.IntLib.ofBits (b.natAbs.bits)) := by
                rw [hzeroV, Nat.gcd_zero_right, h3]
          _ = Int.gcd a b := hgcdInt.symm
      have hlen : (List.replicate k false ++ a.natAbs.bits.drop k).length
          ≤ a.natAbs.size + b.natAbs.size := by
        rw [List.length_append, List.length_replicate]
        omega
      have hevRun : HvdH.Eval main gcdRun s s2 (m1 + m2) := by
        rw [gcdRun_eq]; exact Eval.seq hev1 hev2
      refine ⟨s2, m1 + m2, hevRun, ?_, ⟨_, hU2, hval, hlen⟩, ⟨[], hV2, by simp⟩, hG2, hP2, hQ2,
        hR2, hS2, ?_⟩
      · have hsq : a.natAbs.size + b.natAbs.size + 5
            ≤ (a.natAbs.size + b.natAbs.size + 5) * (a.natAbs.size + b.natAbs.size + 5) :=
          le_mul_self_of_pos _ (by omega)
        have hAL : m1 + m2 ≤ 400 * (a.natAbs.size + b.natAbs.size + 5) := by omega
        rw [hisz]
        nlinarith only [hAL, hsq]
      · intro j ha hb hc hd he hf hg
        exact (hfr2 j ha hb hc hd he hf hg).trans (hfr1 j ha hb hc)
    · -- ### Case B2: both regions nonempty
      have hodds : Work.IntLib.ofBits (dropLead (a.natAbs.bits.drop k)) % 2 = 1 := by
        rw [dropLead_drop _ _ hkU]
        exact ofBits_dropLead_odd _ (dropLead_bits_ne_nil _
          (Work.IntLib.bits_ne_nil_iff.mp (by intro hc; rw [hc] at hdU; simp at hdU)))
      have hoddsV : Work.IntLib.ofBits (dropLead (b.natAbs.bits.drop k)) % 2 = 1 := by
        rw [dropLead_drop _ _ hkV]
        exact ofBits_dropLead_odd _ (dropLead_bits_ne_nil _
          (Work.IntLib.bits_ne_nil_iff.mp (by intro hc; rw [hc] at hdV; simp at hdV)))
      obtain ⟨s2, m2, hev2, hm2, ⟨ul', hU2, hUl'v, hUllen'⟩, ⟨vl', hV2, hVllen'⟩, hG2, hP2, hQ2,
        hR2, hS2, hfr2⟩ :=
        gcdRunTailBothGen main (a.natAbs.bits.drop k) (b.natAbs.bits.drop k) bU0 cV U' V' k bU bV
          bG bP bQ bR bS s1 hU1' hdU hV1' hdV hG1' hP1 hQ1 hR1 hS1 hodds hoddsV
      have hoddU' : Work.IntLib.ofBits (dropLead (a.natAbs.bits)) % 2 = 1 := by
        rw [← dropLead_drop _ _ hkU]
        exact hodds
      have hoddV' : Work.IntLib.ofBits (dropLead (b.natAbs.bits)) % 2 = 1 := by
        rw [← dropLead_drop _ _ hkV]
        exact hoddsV
      have hkmin : min (nLead a.natAbs.bits) (nLead b.natAbs.bits) = k := by
        rw [hk]
        rfl
      have hpu : dropLead (a.natAbs.bits.drop k) = dropLead a.natAbs.bits := dropLead_drop _ _ hkU
      have hpv : dropLead (b.natAbs.bits.drop k) = dropLead b.natAbs.bits := dropLead_drop _ _ hkV
      have hF3 := gcdTwoPowGcd (nLead a.natAbs.bits) (nLead b.natAbs.bits)
        (Work.IntLib.ofBits (dropLead a.natAbs.bits))
        (Work.IntLib.ofBits (dropLead b.natAbs.bits)) hoddU' hoddV'
      have hus : Work.IntLib.ofBits (a.natAbs.bits)
          = 2 ^ nLead a.natAbs.bits * Work.IntLib.ofBits (dropLead a.natAbs.bits) :=
        ofBits_eq_two_pow_mul_nLead _
      have hvs : Work.IntLib.ofBits (b.natAbs.bits)
          = 2 ^ nLead b.natAbs.bits * Work.IntLib.ofBits (dropLead b.natAbs.bits) :=
        ofBits_eq_two_pow_mul_nLead _
      have hgcd : Nat.gcd (Work.IntLib.ofBits (a.natAbs.bits))
            (Work.IntLib.ofBits (b.natAbs.bits))
          = 2 ^ k * Nat.gcd (Work.IntLib.ofBits (dropLead a.natAbs.bits))
              (Work.IntLib.ofBits (dropLead b.natAbs.bits)) := by
        rw [hus, hvs, hF3, hkmin]
      have h2 : Work.IntLib.ofBits ul'
          = Nat.gcd (Work.IntLib.ofBits (dropLead a.natAbs.bits))
              (Work.IntLib.ofBits (dropLead b.natAbs.bits)) := by
        rw [← hpu, ← hpv]
        exact hUl'v
      have hval : Work.IntLib.ofBits (List.replicate k false ++ ul') = Int.gcd a b := by
        have h1 := ofBits_replicate_false_append k ul'
        calc Work.IntLib.ofBits (List.replicate k false ++ ul')
            = 2 ^ k * Work.IntLib.ofBits ul' := h1
          _ = Nat.gcd (Work.IntLib.ofBits (a.natAbs.bits)) (Work.IntLib.ofBits (b.natAbs.bits)) := by
                rw [h2, hgcd]
          _ = Int.gcd a b := hgcdInt.symm
      have hlen : (List.replicate k false ++ ul').length ≤ a.natAbs.size + b.natAbs.size := by
        rw [List.length_append, List.length_replicate]
        have hmax : ul'.length
            ≤ max (a.natAbs.bits.drop k).length (b.natAbs.bits.drop k).length := hUllen'
        have hma : max (a.natAbs.bits.drop k).length (b.natAbs.bits.drop k).length
            ≤ a.natAbs.size + b.natAbs.size := by omega
        omega
      have hlenv : vl'.length ≤ a.natAbs.size + b.natAbs.size := by
        have hmax : vl'.length
            ≤ max (a.natAbs.bits.drop k).length (b.natAbs.bits.drop k).length := hVllen'
        have hma : max (a.natAbs.bits.drop k).length (b.natAbs.bits.drop k).length
            ≤ a.natAbs.size + b.natAbs.size := by omega
        omega
      have hevRun : HvdH.Eval main gcdRun s s2 (m1 + m2) := by
        rw [gcdRun_eq]; exact Eval.seq hev1 hev2
      refine ⟨s2, m1 + m2, hevRun, ?_, ⟨_, hU2, hval, hlen⟩, ⟨_, hV2, hlenv⟩, hG2, hP2, hQ2,
        hR2, hS2, ?_⟩
      · have hsq : a.natAbs.size + b.natAbs.size + 5
            ≤ (a.natAbs.size + b.natAbs.size + 5) * (a.natAbs.size + b.natAbs.size + 5) :=
          le_mul_self_of_pos _ (by omega)
        have hk1 : k + 1 ≤ a.natAbs.size + b.natAbs.size + 5 := by omega
        have hUV : (a.natAbs.bits.drop k).length + (b.natAbs.bits.drop k).length + k + 1
            ≤ 2 * (a.natAbs.size + b.natAbs.size + 5) := by omega
        have hm2' : m2 ≤ 12000 * (2 * (a.natAbs.size + b.natAbs.size + 5))
              * (2 * (a.natAbs.size + b.natAbs.size + 5)) + 12000 := by
          nlinarith only [hm2, hUV]
        rw [hisz]
        nlinarith only [hm1, hm2', hk1, hsq]
      · intro j ha hb hc hd he hf hg
        exact (hfr2 j ha hb hc hd he hf hg).trans (hfr1 j ha hb hc)

end Work.IntLib.SqrtGcd
