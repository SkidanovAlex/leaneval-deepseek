import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdProg
import Submission.Work.IntLib.SqrtGcd.gcdFinishEval
import Submission.Work.IntLib.SqrtGcd.gcdRunEvalGen
import Submission.Work.IntLib.SqrtGcd.gcdFinishCleanLocalGen

namespace Work.IntLib.SqrtGcd

open HvdH
open Work.IntLib.SG

/-- **The whole gcd word, with junk below the frame markers.**  `gcdRun` computes the gcd of `a`
and `b`, `gcdFinish` emits its encoding on stack 0 (on top of `R`) and `gcdClean` restores the
seven scratch stacks down to their junk.  This is `gcdFinishEval` with the empty scratch stacks
replaced by arbitrary junk `bU … bS` below the markers. -/
theorem gcdFinishEvalGen (main : HvdH.Cmd) (a b : ℤ) (R : List HvdH.Glyph)
    (bU bV bG bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (h0 : s.stk 0 = R)
    (hU : s.stk Work.IntLib.SG.sU = a.natAbs.bits.map HvdH.Glyph.bit
      ++ HvdH.Glyph.mk Work.IntLib.SG.sU :: bU)
    (hV : s.stk Work.IntLib.SG.sV = b.natAbs.bits.map HvdH.Glyph.bit
      ++ HvdH.Glyph.mk Work.IntLib.SG.sV :: bV)
    (hG : s.stk Work.IntLib.SG.sG = HvdH.Glyph.mk Work.IntLib.SG.sG :: bG)
    (hP : s.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP)
    (hQ : s.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ)
    (hR : s.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR)
    (hS : s.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS) :
    ∃ s' m, HvdH.Eval main
        (HvdH.Cmd.seq Work.IntLib.SG.gcdRun
          (HvdH.Cmd.seq Work.IntLib.SG.gcdFinish Work.IntLib.SG.gcdClean)) s s' m ∧
      m ≤ 100000 * (HvdH.isz a + HvdH.isz b + 1) * (HvdH.isz a + HvdH.isz b + 1) + 100000 ∧
      s'.stk 0 = (HvdH.Val.int (Int.gcd a b)).enc ++ R ∧
      s'.stk Work.IntLib.SG.sU = bU ∧ s'.stk Work.IntLib.SG.sV = bV ∧
      s'.stk Work.IntLib.SG.sG = bG ∧ s'.stk Work.IntLib.SG.sP = bP ∧
      s'.stk Work.IntLib.SG.sQ = bQ ∧ s'.stk Work.IntLib.SG.sR = bR ∧
      s'.stk Work.IntLib.SG.sS = bS ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ Work.IntLib.SG.sU → k ≠ Work.IntLib.SG.sV →
        k ≠ Work.IntLib.SG.sG → k ≠ Work.IntLib.SG.sP → k ≠ Work.IntLib.SG.sQ →
        k ≠ Work.IntLib.SG.sR → k ≠ Work.IntLib.SG.sS → s'.stk k = s.stk k) := by
  obtain ⟨s1, m1, hev1, hm1, ⟨ul, hUl, hUlv, hUllen⟩, ⟨vl, hVl, hVllen⟩, hG1, hP1, hQ1, hR1,
    hS1, hfr1⟩ :=
    gcdRunEvalGen main a b bU bV bG bP bQ bR bS s hU hV hG hP hQ hR hS
  have h01 : s1.stk 0 = R := by
    rw [hfr1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h0
  have hG1' : s1.stk sG = List.replicate 0 gTick ++ Glyph.mk sG :: bG := by simpa using hG1
  obtain ⟨s2, m2, hev2, hm2, h0', hU2, hV2, hG2, hP2, hQ2, hR2, hS2, hfr2⟩ :=
    gcdFinishCleanLocalGen main ul vl 0 R bU bV bG bP bQ bR bS s1 h01 hUl hVl hG1' hP1 hQ1 hR1
      hS1
  have h0'' : s2.stk 0 = (HvdH.Val.int (Int.gcd a b)).enc ++ R := by
    rw [hUlv] at h0'
    exact h0'
  refine ⟨s2, m1 + m2, Eval.seq hev1 hev2, ?_, h0'', hU2, hV2, hG2, hP2, hQ2, hR2, hS2, ?_⟩
  · have h2 : ul.length + vl.length ≤ 2 * (a.natAbs.size + b.natAbs.size) := by omega
    have hsz : HvdH.isz a + HvdH.isz b + 1 = a.natAbs.size + b.natAbs.size + 5 := by
      rw [Work.IntLib.isz_eq, Work.IntLib.isz_eq]; ring
    have hm2' : m2 ≤ 200 * (2 * (a.natAbs.size + b.natAbs.size) + 1) := by omega
    have hAB : a.natAbs.size + b.natAbs.size ≤ a.natAbs.size + b.natAbs.size + 5 := by omega
    have hsq : a.natAbs.size + b.natAbs.size + 5
        ≤ (a.natAbs.size + b.natAbs.size + 5) * (a.natAbs.size + b.natAbs.size + 5) :=
      le_mul_self_of_pos _ (by omega)
    rw [hsz] at hm1
    rw [hsz]
    nlinarith only [hm1, hm2', hAB, hsq]
  · intro j ha hb hc hd he hf hg hh
    exact (hfr2 j ha hb hc hd he hf hg hh).trans (hfr1 j hb hc hd he hf hg hh)

end Work.IntLib.SqrtGcd
