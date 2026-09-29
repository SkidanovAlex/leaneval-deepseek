import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdProg
import Submission.Work.IntLib.SqrtGcd.gcdAux
import Submission.Work.IntLib.SqrtGcd.gcdInvDefs
import Submission.Work.IntLib.SqrtGcd.gcdBodySpec2
import Submission.Work.IntLib.SqrtGcd.gcdStepSpec
import Submission.Work.IntLib.SqrtGcd.gcdPhaseAEval
import Submission.Work.IntLib.SqrtGcd.gcdScaleEval
import Submission.Work.IntLib.SqrtGcd.gcdTwoPowGcd
import Submission.Work.IntLib.SqrtGcd.oddPartSpec
import Submission.Work.IntLib.SqrtGcd.oddPartVal
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.dropWhile_rev_padBits_bits
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.eval_stripZeros

/-!
# The gcd word: `gcdRun ; gcdFinish ; gcdClean`

Assembly of the correctness proof of `SG.gcdProg` from its phases: the run phase `gcdRun`
(phase A strips the common power of `2`, then either the binary-gcd main loop `gcdMain` on the odd
parts or one of the degenerate cases, then `gcdScale` multiplies back), the emission `gcdFinish`
and the cleanup `gcdClean`.

Write `U := a.natAbs.bits`, `V := b.natAbs.bits` (least significant bit first) and
`k := min (nLead U) (nLead V)`, the common number of factors of `2`.  After phase A the regions of
`sU`, `sV` hold `U.drop k`, `V.drop k` and `sG` holds `k` ticks, and the three possible
continuations are:

* `U.drop k = []` (so `a = 0`): move `V.drop k` onto `sU` and rescale; the value becomes
  `2 ^ k * ofBits (V.drop k) = ofBits V = gcd a b`;
* `V.drop k = []` (so `b = 0`): rescale only; the value becomes `ofBits U = gcd a b`;
* both nonempty: `gcdOdd ; gcdMain ; gcdScale` on the odd parts, with the arithmetic identity
  `gcdTwoPowGcd`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Work.IntLib.SqrtGcd

open HvdH
open Work.IntLib.SG

/-! ## Elementary glyph and state facts -/

theorem gBit_ne_mk (b : Bool) (i : Stk) : Glyph.bit b ≠ Glyph.mk i := fun h => by cases h

theorem gMk_ne_eos (i : Stk) : Glyph.mk i ≠ Glyph.eos := fun h => by cases h

theorem gMk_ne_bit (i : Stk) (b : Bool) : Glyph.mk i ≠ Glyph.bit b := fun h => by cases h

theorem mem_map_bit_ne_mk (l : List Bool) (i : Stk) : ∀ g ∈ l.map Glyph.bit, g ≠ Glyph.mk i := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨b, -, rfl⟩ := hg
  exact gBit_ne_mk b i

theorem stkUpd (s : State) (r : Reg) (g : Glyph) (j : Stk) :
    (⟨Function.update s.reg r g, s.stk⟩ : State).stk j = s.stk j := rfl

theorem regUpd (s : State) (r : Reg) (g : Glyph) :
    (⟨Function.update s.reg r g, s.stk⟩ : State).reg r = g :=
  Function.update_self r g s.reg

theorem evalPeek (main : HvdH.Cmd) (i : Stk) (r : Reg) (s : State) :
    HvdH.Eval main (.peek i r) s
      ⟨Function.update s.reg r ((s.stk i).headD Glyph.eos), s.stk⟩ 1 :=
  Eval.peek i r s

theorem regPeek (s : State) (i : Stk) (r : Reg) :
    (⟨Function.update s.reg r ((s.stk i).headD Glyph.eos), s.stk⟩ : State).reg r
      = (s.stk i).headD Glyph.eos :=
  regUpd s r ((s.stk i).headD Glyph.eos)

theorem evalPeek2 (main : HvdH.Cmd) (i : Stk) (r : Reg) (s : State) (i2 : Stk) (r2 : Reg) :
    HvdH.Eval main (.peek i2 r2)
      (⟨Function.update s.reg r ((s.stk i).headD Glyph.eos), s.stk⟩ : State)
      (⟨Function.update (Function.update s.reg r ((s.stk i).headD Glyph.eos)) r2
          ((s.stk i2).headD Glyph.eos), s.stk⟩ : State) 1 :=
  Eval.peek i2 r2 _

theorem regPeek2 (s : State) (i : Stk) (r : Reg) (i2 : Stk) (r2 : Reg) :
    (⟨Function.update (Function.update s.reg r ((s.stk i).headD Glyph.eos)) r2
        ((s.stk i2).headD Glyph.eos), s.stk⟩ : State).reg r2 = (s.stk i2).headD Glyph.eos := by
  show Function.update (Function.update s.reg r ((s.stk i).headD Glyph.eos)) r2
      ((s.stk i2).headD Glyph.eos) r2 = (s.stk i2).headD Glyph.eos
  rw [Function.update_self]

theorem mStK (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (gs below : List Glyph) (s : State)
    (h : k ≠ d) : (mSt k T d r gs below s).stk k = T :: below := by simp [mSt, h]

theorem mStD (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (gs below : List Glyph) (s : State) :
    (mSt k T d r gs below s).stk d = gs.reverse ++ s.stk d := by simp [mSt]

theorem mStO (k : Stk) (T : Glyph) (d j : Stk) (r : Reg) (gs below : List Glyph) (s : State)
    (h1 : j ≠ k) (h2 : j ≠ d) : (mSt k T d r gs below s).stk j = s.stk j := by
  simp [mSt, h1, h2]

theorem bits_len (n : ℕ) : n.bits.length = n.size := Nat.size_eq_bits_len n

/-- A positive natural number is at most its square. -/
theorem le_mul_self_of_pos (n : ℕ) (h : 1 ≤ n) : n ≤ n * n := by
  have h1 : n * 1 ≤ n * n := Nat.mul_le_mul_left n h
  simpa using h1

theorem ofBits_bits_apply (n : ℕ) : Work.IntLib.ofBits n.bits = n := Work.IntLib.ofBits_bits n

/-- The head of a nonempty bit region is its first bit. -/
theorem headD_eq_bit {U U' : List Bool} {x : Bool} {T : Glyph} (h : U = x :: U') :
    (U.map Glyph.bit ++ [T]).headD Glyph.eos = Glyph.bit x := by
  rw [h]; rfl

/-- The head of an empty bit region is the marker. -/
theorem headD_eq_mk {U : List Bool} {T : Glyph} (h : U = []) :
    (U.map Glyph.bit ++ [T]).headD Glyph.eos = T := by
  rw [h]; rfl

/-- Appending `k` zero bits in front multiplies the value by `2 ^ k`. -/
theorem ofBits_replicate_false_append (k : ℕ) (l : List Bool) :
    Work.IntLib.ofBits (List.replicate k false ++ l) = 2 ^ k * Work.IntLib.ofBits l := by
  rw [Work.IntLib.ofBits_append, ofBits_replicate_false_gcdInvDefs, List.length_replicate, zero_add]

/-! ## Moving a region with `moveSame` -/

/-- `moveSame sV sU sR r` moves the bit region of `sV` onto `sU`, keeping the order of the bits;
`sR` must be empty and is restored. -/
theorem moveSameVUR (main : HvdH.Cmd) (V : List Bool) (s : HvdH.State)
    (hV : s.stk sV = V.map Glyph.bit ++ [Glyph.mk sV])
    (hR : s.stk sR = [Glyph.mk sR]) :
    ∃ s' m, HvdH.Eval main (moveSame sV sU sR rgT) s s' m ∧ m ≤ 20 * (V.length + 1) ∧
      s'.stk sU = V.map Glyph.bit ++ s.stk sU ∧
      s'.stk sV = [Glyph.mk sV] ∧
      s'.stk sR = [Glyph.mk sR] ∧
      (∀ j : Stk, j ≠ sV → j ≠ sU → j ≠ sR → s'.stk j = s.stk j) := by
  have h1 : HvdH.Eval main (SG.rLoop sV (Glyph.mk sV) (some sR) rgT) s
      (mSt sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) [] s) (7 + (V.map Glyph.bit).length * 5) :=
    mLoop_eval main sV (Glyph.mk sV) sR rgT (gMk_ne_eos sV) (by decide) (V.map Glyph.bit) [] s
      hV (mem_map_bit_ne_mk V sV)
  have hR1 : (mSt sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) [] s).stk sR
      = (V.reverse).map Glyph.bit ++ [Glyph.mk sR] := by
    rw [mStD, hR, List.map_reverse]
  have h2 : HvdH.Eval main (SG.rLoop sR (Glyph.mk sR) (some sU) rgT)
      (mSt sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) [] s)
      (mSt sR (Glyph.mk sR) sU rgT ((V.reverse).map Glyph.bit) []
        (mSt sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) [] s))
      (7 + ((V.reverse).map Glyph.bit).length * 5) :=
    mLoop_eval main sR (Glyph.mk sR) sU rgT (gMk_ne_eos sR) (by decide)
      ((V.reverse).map Glyph.bit) [] _ hR1 (mem_map_bit_ne_mk V.reverse sR)
  refine ⟨_, (7 + (V.map Glyph.bit).length * 5) + (7 + ((V.reverse).map Glyph.bit).length * 5),
    Eval.seq h1 h2, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_reverse]; omega
  · rw [mStD, mStO sV (Glyph.mk sV) sR sU rgT (V.map Glyph.bit) [] s (by decide) (by decide),
      List.map_reverse, List.reverse_reverse]
  · rw [mStO sR (Glyph.mk sR) sU sV rgT ((V.reverse).map Glyph.bit) [] _ (by decide) (by decide),
      mStK sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) [] s (by decide)]
  · rw [mStK sR (Glyph.mk sR) sU rgT ((V.reverse).map Glyph.bit) [] _ (by decide)]
  · intro j hjV hjU hjR
    rw [mStO sR (Glyph.mk sR) sU j rgT ((V.reverse).map Glyph.bit) [] _ hjR hjU]
    exact mStO sV (Glyph.mk sV) sR j rgT (V.map Glyph.bit) [] s hjV hjR

/-! ## The loop of the binary gcd, in the invariant `GSt` -/

/-- **The main loop `SG.gcdMain`.**  From a state satisfying the invariant `GSt` with the loop flag
at `gGo`, the loop terminates with the flag at `gStop`, both operands equal to their gcd, and a cost
bounded by the measure `u.size + v.size` times the cost of one iteration. -/
theorem gcdLoopGSt (main : HvdH.Cmd) (N : ℕ) (bU bV bP bQ bR bS : List HvdH.Glyph)
    (s₀ s : HvdH.State) (u v : ℕ) (hs : GSt N bU bV bP bQ bR bS s₀ s u v)
    (hF : s.reg rgF = gGo) :
    ∃ s' m, HvdH.Eval main (.loop rgF gGo gcdBody) s s' m ∧
      m ≤ (u.size + v.size) * (5000 * (N + 1) + 1) + 1 ∧
      ∃ u' v', GSt N bU bV bP bQ bR bS s₀ s' u' v' ∧ u' = v' ∧
        Nat.gcd u' v' = Nat.gcd u v ∧ s'.reg rgF = gStop := by
  have key : ∀ M : ℕ, ∀ (u v : ℕ) (s : HvdH.State), u.size + v.size ≤ M →
      GSt N bU bV bP bQ bR bS s₀ s u v → s.reg rgF = gGo →
      ∃ s' m, HvdH.Eval main (.loop rgF gGo gcdBody) s s' m ∧
        m ≤ M * (5000 * (N + 1) + 1) + 1 ∧
        ∃ u' v', GSt N bU bV bP bQ bR bS s₀ s' u' v' ∧ u' = v' ∧
          Nat.gcd u' v' = Nat.gcd u v ∧ s'.reg rgF = gStop := by
    intro M
    induction M using Nat.strong_induction_on with
    | _ M ih =>
      intro u v s hM hs hF
      obtain ⟨s1, m1, hE1, hm1, hreg1, hInv1⟩ :=
        gcdBodySpec2 main N bU bV bP bQ bR bS s₀ s u v hs hF
      by_cases huv : u = v
      · have hstop : s1.reg rgF = gStop := by rw [hreg1, if_pos huv]
        have hne : ¬ (s1.reg rgF = gGo) := by rw [hstop]; decide
        have hgnuv : gNext u v = (u, v) := by simp [gNext, huv]
        have hInv1' : GSt N bU bV bP bQ bR bS s₀ s1 u v := by
          rw [hgnuv] at hInv1
          simpa using hInv1
        have hC : 5000 * (N + 1) + 1 ≤ M * (5000 * (N + 1) + 1) := by
          have h2 : 1 ≤ M := by
            have hu : 0 < u := by have h := hs.hoddU; omega
            have hv : 0 < v := by have h := hs.hoddV; omega
            have h1 : 1 ≤ u.size := Nat.size_pos.mpr hu
            have h2 : 1 ≤ v.size := Nat.size_pos.mpr hv
            omega
          calc 5000 * (N + 1) + 1 = 1 * (5000 * (N + 1) + 1) := by ring
            _ ≤ M * (5000 * (N + 1) + 1) := Nat.mul_le_mul_right _ h2
        exact ⟨s1, m1 + 2, Eval.loopT hF hE1 (Eval.loopF hne), by omega, u, v, hInv1',
          huv, rfl, hstop⟩
      · have hreg1' : s1.reg rgF = gGo := by rw [hreg1, if_neg huv]
        have hgn : gNext u v = gcdStep u v := by simp [gNext, huv]
        have hgn1 : (gNext u v).1 = (gcdStep u v).1 := by rw [hgn]
        have hgn2 : (gNext u v).2 = (gcdStep u v).2 := by rw [hgn]
        have hInv1' : GSt N bU bV bP bQ bR bS s₀ s1 (gcdStep u v).1 (gcdStep u v).2 := by
          rw [hgn1, hgn2] at hInv1
          exact hInv1
        obtain ⟨hgcd, hodd1, hodd2, hsize⟩ := gcdStepSpec u v hs.hoddU hs.hoddV huv
        have hlt : (gcdStep u v).1.size + (gcdStep u v).2.size < M := by omega
        obtain ⟨s2, m2, hE2, hm2, u₂, v₂, hInv2, huv2, hgcd2, hstop2⟩ :=
          ih ((gcdStep u v).1.size + (gcdStep u v).2.size) hlt (gcdStep u v).1
            (gcdStep u v).2 s1 (le_refl _) hInv1' hreg1'
        have hM' : (gcdStep u v).1.size + (gcdStep u v).2.size + 1 ≤ M := by omega
        have hstep : ((gcdStep u v).1.size + (gcdStep u v).2.size + 1) * (5000 * (N + 1) + 1)
            ≤ M * (5000 * (N + 1) + 1) := Nat.mul_le_mul_right _ hM'
        have hdist : ((gcdStep u v).1.size + (gcdStep u v).2.size + 1) * (5000 * (N + 1) + 1)
            = ((gcdStep u v).1.size + (gcdStep u v).2.size) * (5000 * (N + 1) + 1)
              + (5000 * (N + 1) + 1) := by
          rw [Nat.add_mul, Nat.one_mul]
        exact ⟨s2, m1 + m2 + 1, Eval.loopT hF hE1 hE2, by omega, u₂, v₂, hInv2, huv2,
          by rw [hgcd2]; exact hgcd, hstop2⟩
  exact key (u.size + v.size) u v s (le_refl _) hs hF

/-- **`gcdMain` from plain stack hypotheses.**  Besides the value of the gcd it records that the
resulting bit regions have length at most the largest input length. -/
theorem gcdMainEvalFull (main : HvdH.Cmd) (us vs : List Bool)
    (bU bV bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (hU : s.stk sU = us.map Glyph.bit ++ Glyph.mk sU :: bU)
    (hV : s.stk sV = vs.map Glyph.bit ++ Glyph.mk sV :: bV)
    (hP : s.stk sP = Glyph.mk sP :: bP)
    (hQ : s.stk sQ = Glyph.mk sQ :: bQ)
    (hR : s.stk sR = Glyph.mk sR :: bR)
    (hS : s.stk sS = Glyph.mk sS :: bS)
    (hoddU : Work.IntLib.ofBits us % 2 = 1) (hoddV : Work.IntLib.ofBits vs % 2 = 1) :
    ∃ s' m, HvdH.Eval main gcdMain s s' m ∧
      m ≤ 10000 * (us.length + vs.length + 1) * (us.length + vs.length + 1) + 10000 ∧
      (∃ ul : List Bool, s'.stk sU = ul.map Glyph.bit ++ Glyph.mk sU :: bU ∧
        Work.IntLib.ofBits ul = Nat.gcd (Work.IntLib.ofBits us) (Work.IntLib.ofBits vs) ∧
        ul.length ≤ max us.length vs.length) ∧
      (∃ vl : List Bool, s'.stk sV = vl.map Glyph.bit ++ Glyph.mk sV :: bV ∧
        vl.length ≤ max us.length vs.length) ∧
      s'.stk sP = Glyph.mk sP :: bP ∧ s'.stk sQ = Glyph.mk sQ :: bQ ∧
      s'.stk sR = Glyph.mk sR :: bR ∧ s'.stk sS = Glyph.mk sS :: bS ∧
      s'.stk sG = s.stk sG ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  set N : ℕ := max us.length vs.length with hN
  have hUlN : us.length ≤ N := by rw [hN]; exact le_max_left _ _
  have hVlN : vs.length ≤ N := by rw [hN]; exact le_max_right _ _
  have hGSt : GSt N bU bV bP bQ bR bS s s (Work.IntLib.ofBits us) (Work.IntLib.ofBits vs) :=
    ⟨⟨us, hU, rfl, hUlN⟩, ⟨vs, hV, rfl, hVlN⟩, hoddU, hoddV, hP, hQ, hR, hS, rfl,
      fun j _ _ _ _ _ _ _ => rfl⟩
  let s₁ : State := ⟨Function.update s.reg rgF gGo, s.stk⟩
  have hE1 : HvdH.Eval main (.set rgF gGo) s s₁ 1 := Eval.set rgF gGo s
  have hGSt1 : GSt N bU bV bP bQ bR bS s s₁ (Work.IntLib.ofBits us) (Work.IntLib.ofBits vs) := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -, -⟩ := hGSt
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, rfl, fun j _ _ _ _ _ _ _ => rfl⟩
  have hF1 : s₁.reg rgF = gGo := by simp [s₁]
  obtain ⟨s2, m2, hE2, hm2, u', v', hInv2, huv', hgcd2, hstop2⟩ :=
    gcdLoopGSt main N bU bV bP bQ bR bS s s₁ (Work.IntLib.ofBits us) (Work.IntLib.ofBits vs)
      hGSt1 hF1
  obtain ⟨ul, hUl, hUlv, hUllen⟩ := hInv2.hU
  obtain ⟨vl, hVl, hVlv, hVllen⟩ := hInv2.hV
  have hgoalUl : Work.IntLib.ofBits ul
      = Nat.gcd (Work.IntLib.ofBits us) (Work.IntLib.ofBits vs) := by
    have h1 : Work.IntLib.ofBits ul
        = Nat.gcd (Work.IntLib.ofBits ul) (Work.IntLib.ofBits vl) := by
      rw [hUlv, hVlv, ← huv', Nat.gcd_self]
    rw [h1, hUlv, hVlv]
    exact hgcd2
  refine ⟨s2, 1 + m2, Eval.seq hE1 hE2, ?_, ⟨ul, hUl, hgoalUl, ?_⟩, ⟨vl, hVl, ?_⟩,
    hInv2.hP, hInv2.hQ, hInv2.hR, hInv2.hS, hInv2.hG, ?_⟩
  · have h1 : (Work.IntLib.ofBits us).size ≤ N :=
      le_trans (Nat.size_le.mpr (Work.IntLib.ofBits_lt_two_pow us)) hUlN
    have h2 : (Work.IntLib.ofBits vs).size ≤ N :=
      le_trans (Nat.size_le.mpr (Work.IntLib.ofBits_lt_two_pow vs)) hVlN
    have h3 : (Work.IntLib.ofBits us).size + (Work.IntLib.ofBits vs).size ≤ 2 * N := by omega
    have h4 := Nat.mul_le_mul_right (5000 * (N + 1) + 1) h3
    have h5 : N ≤ us.length + vs.length := by
      rw [hN]; exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    have h6 : 2 * N * (5000 * (N + 1) + 1) + 2
        ≤ 10000 * (us.length + vs.length + 1) * (us.length + vs.length + 1) + 10000 := by
      nlinarith [h5, Nat.zero_le N, Nat.zero_le (us.length + vs.length)]
    omega
  · rw [hN] at hUllen; exact hUllen
  · rw [hN] at hVllen; exact hVllen
  · intro j ha hb hc hd he hf hg
    exact hInv2.hfr j ha hb hc hd he hf hg


/-! ## Auxiliary facts for the finish/clean phases -/

theorem updStkSelf (s : State) (g : Glyph) (i : Stk) :
    (⟨Function.update s.reg rgU g, Function.update s.stk i (g :: s.stk i)⟩ : State).stk i
      = g :: s.stk i := by
  show Function.update s.stk i (g :: s.stk i) i = g :: s.stk i
  rw [Function.update_self]

theorem dStK (i : Stk) (T : Glyph) (r : Reg) (below : List Glyph) (s : State) :
    (dSt i T r below s).stk i = T :: below := by simp [dSt]

theorem dStO (i : Stk) (T : Glyph) (r : Reg) (below : List Glyph) (s : State) (j : Stk)
    (h : j ≠ i) : (dSt i T r below s).stk j = s.stk j := by simp [dSt, h]

theorem updStk (s : State) (r : Reg) (g : Glyph) (i : Stk) :
    (⟨Function.update s.reg r g, Function.update s.stk i []⟩ : State).stk i = [] := by
  show Function.update s.stk i [] i = []
  rw [Function.update_self]

theorem updStkO (s : State) (r : Reg) (g : Glyph) (i j : Stk) (h : j ≠ i) :
    (⟨Function.update s.reg r g, Function.update s.stk i []⟩ : State).stk j = s.stk j := by
  show Function.update s.stk i [] j = s.stk j
  rw [Function.update_of_ne h]

/-- The first step of `gcdFinish`: move the region of `sU` onto `sP`, reversed. -/
theorem finishMove (main : HvdH.Cmd) (ul : List Bool) (s : State)
    (hU : s.stk sU = ul.map Glyph.bit ++ [Glyph.mk sU])
    (hP : s.stk sP = [Glyph.mk sP]) :
    ∃ s' m, HvdH.Eval main (SG.rLoop sU (Glyph.mk sU) (some sP) rgT) s s' m ∧
      m = 7 + (ul.map Glyph.bit).length * 5 ∧
      s'.stk sP = (ul.reverse).map Glyph.bit ++ [Glyph.mk sP] ∧
      s'.stk sU = [Glyph.mk sU] ∧
      (∀ j : Stk, j ≠ sU → j ≠ sP → s'.stk j = s.stk j) := by
  refine ⟨mSt sU (Glyph.mk sU) sP rgT (ul.map Glyph.bit) [] s,
    7 + (ul.map Glyph.bit).length * 5,
    mLoop_eval main sU (Glyph.mk sU) sP rgT (gMk_ne_eos sU) (by decide) (ul.map Glyph.bit) [] s
      hU (mem_map_bit_ne_mk ul sU), rfl, ?_, ?_, ?_⟩
  · rw [mStD, hP, List.map_reverse]
  · rw [mStK sU (Glyph.mk sU) sP rgT (ul.map Glyph.bit) [] s (by decide)]
  · intro j hjU hjP
    exact mStO sU (Glyph.mk sU) sP j rgT (ul.map Glyph.bit) [] s hjU hjP

/-- The third/fifth step of `gcdFinish`: push a glyph on stack 0. -/
theorem finishPush (main : HvdH.Cmd) (g : Glyph) (S0 : List Glyph) (s : State)
    (h0 : s.stk 0 = S0) :
    ∃ m, HvdH.Eval main (Work.Layout.seqs [.set rgU g, .push 0 rgU]) s
        ⟨Function.update s.reg rgU g, Function.update s.stk 0 (g :: s.stk 0)⟩ m ∧ m = 2 ∧
      (⟨Function.update s.reg rgU g, Function.update s.stk 0 (g :: s.stk 0)⟩ : State).stk 0
          = g :: S0 ∧
      (∀ j : Stk, j ≠ 0 →
        (⟨Function.update s.reg rgU g, Function.update s.stk 0 (g :: s.stk 0)⟩ : State).stk j
          = s.stk j) := by
  refine ⟨2, ?_, rfl, ?_, ?_⟩
  · exact Eval.seq (Eval.set rgU g s) (Eval.push 0 rgU _)
  · show Function.update s.stk 0 (g :: s.stk 0) 0 = g :: S0
    rw [Function.update_self, h0]
  · intro j hj
    show Function.update s.stk 0 (g :: s.stk 0) j = s.stk j
    rw [Function.update_of_ne hj]

/-- The fourth step of `gcdFinish`: emit the stripped bits of `sP` onto stack 0. -/
theorem finishEmit (main : HvdH.Cmd) (L : List Bool) (S0 : List Glyph) (s : State)
    (hP : s.stk sP = L.map Glyph.bit ++ [Glyph.mk sP]) (h0 : s.stk 0 = S0) :
    ∃ s' m, HvdH.Eval main (SG.rLoop sP (Glyph.mk sP) (some 0) rgT) s s' m ∧
      m = 7 + (L.map Glyph.bit).length * 5 ∧
      s'.stk 0 = (L.map Glyph.bit).reverse ++ S0 ∧
      s'.stk sP = [Glyph.mk sP] ∧
      (∀ j : Stk, j ≠ sP → j ≠ 0 → s'.stk j = s.stk j) := by
  refine ⟨mSt sP (Glyph.mk sP) 0 rgT (L.map Glyph.bit) [] s,
    7 + (L.map Glyph.bit).length * 5,
    mLoop_eval main sP (Glyph.mk sP) 0 rgT (gMk_ne_eos sP) (by decide) (L.map Glyph.bit) [] s
      hP (mem_map_bit_ne_mk L sP), rfl, ?_, ?_, ?_⟩
  · rw [mStD, h0]
  · rw [mStK sP (Glyph.mk sP) 0 rgT (L.map Glyph.bit) [] s (by decide)]
  · intro j hjP hj0
    exact mStO sP (Glyph.mk sP) 0 j rgT (L.map Glyph.bit) [] s hjP hj0

theorem updStkOther (s : State) (g : Glyph) (i j : Stk) (h : j ≠ i) :
    (⟨Function.update s.reg rgU g, Function.update s.stk i (g :: s.stk i)⟩ : State).stk j
      = s.stk j := by
  show Function.update s.stk i (g :: s.stk i) j = s.stk j
  rw [Function.update_of_ne h]

theorem setStk (s : State) (r : Reg) (g : Glyph) (j : Stk) :
    (⟨Function.update s.reg r g, s.stk⟩ : State).stk j = s.stk j := rfl

theorem setReg (s : State) (r : Reg) (g : Glyph) :
    (⟨Function.update s.reg r g, s.stk⟩ : State).reg r = g := regUpd s r g

/-- Stripping the leading (high) zeros of `ul.reverse` and reversing gives the canonical bits. -/
theorem stripHigh_rev_map (ul : List Bool) :
    ((dropLead (ul.reverse)).map Glyph.bit).reverse
      = ((Work.IntLib.ofBits ul).bits).map Glyph.bit := by
  have h1 : (dropLead (ul.reverse)).map Glyph.bit
      = ((Work.IntLib.MulS.stripHigh ul).map Glyph.bit).reverse := by
    show ((ul.reverse).dropWhile (fun b => !b)).map Glyph.bit = _
    rw [← Work.IntLib.dropWhile_map_bit_rev ul.reverse, Work.IntLib.dropWhile_map_bit_rev_eq ul]
  calc ((dropLead (ul.reverse)).map Glyph.bit).reverse
      = (((Work.IntLib.MulS.stripHigh ul).map Glyph.bit).reverse).reverse := by rw [h1]
    _ = (Work.IntLib.MulS.stripHigh ul).map Glyph.bit := List.reverse_reverse _
    _ = ((Work.IntLib.ofBits ul).bits).map Glyph.bit := by
          rw [Work.IntLib.MulS.stripHigh_eq_bits]

/-- The encoding of the non-negative integer `ofBits ul`. -/
theorem enc_ofBits (ul : List Bool) :
    (HvdH.Val.int ((Work.IntLib.ofBits ul : ℕ) : ℤ)).enc
      = Glyph.pos :: (((Work.IntLib.ofBits ul).bits).map Glyph.bit ++ [Glyph.iend]) := by
  rw [Work.IntLib.enc_int, Work.IntLib.encodeNat_eq_bits]
  simp

/-! ## The run phase -/

/-- `gcdRun` with phase A split off. -/
def gcdRunTail : Cmd :=
  Work.Layout.seqs [ .peek sU rgT,
    .ite rgT (Glyph.mk sU)
      (Work.Layout.seqs [moveSame sV sU sR rgT, gcdScale])
      (Work.Layout.seqs [ .peek sV rgU,
        .ite rgU (Glyph.mk sV) gcdScale (Work.Layout.seqs [gcdOdd, gcdMain, gcdScale]) ]) ]

theorem gcdRun_eq : gcdRun = .seq gcdPhaseA gcdRunTail := rfl

/-- Branch A (the region of `sU` is empty): move the region of `sV` onto `sU` and rescale. -/
theorem gcdRunBranchA (main : HvdH.Cmd) (V : List Bool) (k : ℕ) (s : HvdH.State)
    (hU : s.stk sU = [Glyph.mk sU])
    (hV : s.stk sV = V.map Glyph.bit ++ [Glyph.mk sV])
    (hG : s.stk sG = List.replicate k gTick ++ [Glyph.mk sG])
    (hR : s.stk sR = [Glyph.mk sR]) :
    ∃ s' m, HvdH.Eval main (Work.Layout.seqs [moveSame sV sU sR rgT, gcdScale]) s s' m ∧
      m ≤ 200 * (k + V.length + 1) ∧
      s'.stk sU = (List.replicate k false ++ V).map Glyph.bit ++ [Glyph.mk sU] ∧
      s'.stk sV = [Glyph.mk sV] ∧
      s'.stk sG = [Glyph.mk sG] ∧
      s'.stk sR = [Glyph.mk sR] ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sR → s'.stk j = s.stk j) := by
  obtain ⟨s1, m1, hev1, hm1, hs1U, hs1V, hs1R, hfr1⟩ := moveSameVUR main V s hV hR
  have hs1U' : s1.stk sU = V.map Glyph.bit ++ Glyph.mk sU :: ([] : List Glyph) := by
    rw [hs1U, hU]
  have hs1G : s1.stk sG = List.replicate k gTick ++ [Glyph.mk sG] := by
    rw [hfr1 sG (by decide) (by decide) (by decide)]
    exact hG
  obtain ⟨s2, m2, hev2, hm2, hs2U, hs2G, hfr2⟩ := gcdScaleEval main k V [] s1 hs1U' hs1G
  have hs2V : s2.stk sV = [Glyph.mk sV] := by
    rw [hfr2 sV (by decide) (by decide)]
    exact hs1V
  have hs2R : s2.stk sR = [Glyph.mk sR] := by
    rw [hfr2 sR (by decide) (by decide)]
    exact hs1R
  refine ⟨s2, m1 + m2, Eval.seq hev1 hev2, by omega, hs2U, hs2V, hs2G, hs2R, ?_⟩
  intro j ha hb hc hd
  exact (hfr2 j ha hc).trans (hfr1 j hb ha hd)

/-- Stripping the low zero bits of one operand. -/
theorem stripZerosRegion (main : HvdH.Cmd) (i : Stk) (L : List Bool) (s : HvdH.State)
    (h : s.stk i = L.map Glyph.bit ++ [Glyph.mk i]) :
    ∃ s' m, HvdH.Eval main (SG.stripZeros i rgT) s s' m ∧ m ≤ 2 * (L.length + 1) + 6 ∧
      s'.stk i = (dropLead L).map Glyph.bit ++ [Glyph.mk i] ∧
      (∀ j : Stk, j ≠ i → s'.stk j = s.stk j) := by
  obtain ⟨s', n, hev, hn, hstk, hfr⟩ :=
    Work.IntLib.eval_stripZeros main i (Glyph.mk i) rgT L [] s (gMk_ne_eos i)
      (fun b => gBit_ne_mk b i) h
  refine ⟨s', n, hev, hn, ?_, hfr⟩
  rw [hstk, Work.IntLib.dropWhile_map_bit_rev L]
  rfl

/-- Branch B2 (both regions nonempty): strip the low zeros, run the binary gcd, rescale. -/
theorem gcdRunBranchB2 (main : HvdH.Cmd) (U V : List Bool) (k : ℕ) (s : HvdH.State)
    (hU : s.stk sU = U.map Glyph.bit ++ [Glyph.mk sU])
    (hV : s.stk sV = V.map Glyph.bit ++ [Glyph.mk sV])
    (hG : s.stk sG = List.replicate k gTick ++ [Glyph.mk sG])
    (hP : s.stk sP = [Glyph.mk sP]) (hQ : s.stk sQ = [Glyph.mk sQ])
    (hR : s.stk sR = [Glyph.mk sR]) (hS : s.stk sS = [Glyph.mk sS])
    (hoddU : Work.IntLib.ofBits (dropLead U) % 2 = 1)
    (hoddV : Work.IntLib.ofBits (dropLead V) % 2 = 1) :
    ∃ s' m, HvdH.Eval main (Work.Layout.seqs [gcdOdd, gcdMain, gcdScale]) s s' m ∧
      m ≤ 11000 * (U.length + V.length + k + 1) * (U.length + V.length + k + 1) + 11000 ∧
      (∃ ul : List Bool, s'.stk sU = (List.replicate k false ++ ul).map Glyph.bit
          ++ [Glyph.mk sU] ∧
        Work.IntLib.ofBits ul
          = Nat.gcd (Work.IntLib.ofBits (dropLead U)) (Work.IntLib.ofBits (dropLead V)) ∧
        ul.length ≤ max U.length V.length) ∧
      (∃ vl : List Bool, s'.stk sV = vl.map Glyph.bit ++ [Glyph.mk sV] ∧
        vl.length ≤ max U.length V.length) ∧
      s'.stk sG = [Glyph.mk sG] ∧ s'.stk sP = [Glyph.mk sP] ∧ s'.stk sQ = [Glyph.mk sQ] ∧
      s'.stk sR = [Glyph.mk sR] ∧ s'.stk sS = [Glyph.mk sS] ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  obtain ⟨s1, m1, hev1, hm1, hU1, hfr1⟩ := stripZerosRegion main sU U s hU
  have hV1 : s1.stk sV = V.map Glyph.bit ++ [Glyph.mk sV] := by
    rw [hfr1 sV (by decide)]
    exact hV
  obtain ⟨s2, m2, hev2, hm2, hV2, hfr2⟩ := stripZerosRegion main sV V s1 hV1
  have hP1 : s1.stk sP = [Glyph.mk sP] := by rw [hfr1 sP (by decide)]; exact hP
  have hQ1 : s1.stk sQ = [Glyph.mk sQ] := by rw [hfr1 sQ (by decide)]; exact hQ
  have hR1 : s1.stk sR = [Glyph.mk sR] := by rw [hfr1 sR (by decide)]; exact hR
  have hS1 : s1.stk sS = [Glyph.mk sS] := by rw [hfr1 sS (by decide)]; exact hS
  have hP2 : s2.stk sP = [Glyph.mk sP] := by rw [hfr2 sP (by decide)]; exact hP1
  have hQ2 : s2.stk sQ = [Glyph.mk sQ] := by rw [hfr2 sQ (by decide)]; exact hQ1
  have hR2 : s2.stk sR = [Glyph.mk sR] := by rw [hfr2 sR (by decide)]; exact hR1
  have hS2 : s2.stk sS = [Glyph.mk sS] := by rw [hfr2 sS (by decide)]; exact hS1
  have hG2 : s2.stk sG = List.replicate k gTick ++ [Glyph.mk sG] := by
    rw [hfr2 sG (by decide), hfr1 sG (by decide)]
    exact hG
  have hevOdd : HvdH.Eval main gcdOdd s s2 (m1 + m2) := Eval.seq hev1 hev2
  have hU2 : s2.stk sU = (dropLead U).map Glyph.bit ++ [Glyph.mk sU] := by
    rw [hfr2 sU (by decide)]
    exact hU1
  obtain ⟨s3, m3, hev3, hm3, ⟨ul', hUl', hUl'v, hUl'len⟩, ⟨vl', hVl', hVl'len⟩, hP3, hQ3, hR3,
    hS3, hG3, hfr3⟩ :=
    gcdMainEvalFull main (dropLead U) (dropLead V) [] [] [] [] [] [] s2 hU2 hV2 hP2 hQ2 hR2 hS2
      hoddU hoddV
  have hG3' : s3.stk sG = List.replicate k gTick ++ [Glyph.mk sG] := by
    rw [hG3]; exact hG2
  obtain ⟨s4, m4, hev4, hm4, hU4, hG4, hfr4⟩ :=
    gcdScaleEval main k ul' [] s3 hUl' hG3'
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
theorem gcdRunTailUempty (main : HvdH.Cmd) (U V : List Bool) (k : ℕ) (s : HvdH.State)
    (hU : s.stk sU = U.map Glyph.bit ++ [Glyph.mk sU]) (hUnil : U = [])
    (hV : s.stk sV = V.map Glyph.bit ++ [Glyph.mk sV])
    (hG : s.stk sG = List.replicate k gTick ++ [Glyph.mk sG])
    (hP : s.stk sP = [Glyph.mk sP]) (hQ : s.stk sQ = [Glyph.mk sQ])
    (hR : s.stk sR = [Glyph.mk sR]) (hS : s.stk sS = [Glyph.mk sS]) :
    ∃ s' m, HvdH.Eval main gcdRunTail s s' m ∧ m ≤ 300 * (V.length + k + 1) ∧
      s'.stk sU = (List.replicate k false ++ V).map Glyph.bit ++ [Glyph.mk sU] ∧
      s'.stk sV = [Glyph.mk sV] ∧ s'.stk sG = [Glyph.mk sG] ∧
      s'.stk sP = [Glyph.mk sP] ∧ s'.stk sQ = [Glyph.mk sQ] ∧
      s'.stk sR = [Glyph.mk sR] ∧ s'.stk sS = [Glyph.mk sS] ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  have hhead : (s.stk sU).headD Glyph.eos = Glyph.mk sU := by
    rw [hU]
    exact headD_eq_mk hUnil
  have hreg : (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State).reg rgT
      = Glyph.mk sU := by
    rw [regPeek, hhead]
  obtain ⟨s', m', hev', hm', hU', hV', hG', hR', hfr'⟩ :=
    gcdRunBranchA main V k
      (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State)
      (by simp only [hU, hUnil, List.map_nil, List.nil_append]) hV hG hR
  have hP' : s'.stk sP = [Glyph.mk sP] := by
    rw [hfr' sP (by decide) (by decide) (by decide) (by decide)]
    exact hP
  have hQ' : s'.stk sQ = [Glyph.mk sQ] := by
    rw [hfr' sQ (by decide) (by decide) (by decide) (by decide)]
    exact hQ
  have hS' : s'.stk sS = [Glyph.mk sS] := by
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
theorem gcdRunTailVempty (main : HvdH.Cmd) (U V : List Bool) (b : Bool) (U' : List Bool)
    (k : ℕ) (s : HvdH.State)
    (hU : s.stk sU = U.map Glyph.bit ++ [Glyph.mk sU]) (hUeq : U = b :: U')
    (hV : s.stk sV = V.map Glyph.bit ++ [Glyph.mk sV]) (hVnil : V = [])
    (hG : s.stk sG = List.replicate k gTick ++ [Glyph.mk sG])
    (hP : s.stk sP = [Glyph.mk sP]) (hQ : s.stk sQ = [Glyph.mk sQ])
    (hR : s.stk sR = [Glyph.mk sR]) (hS : s.stk sS = [Glyph.mk sS]) :
    ∃ s' m, HvdH.Eval main gcdRunTail s s' m ∧ m ≤ 300 * (U.length + k + 1) ∧
      s'.stk sU = (List.replicate k false ++ U).map Glyph.bit ++ [Glyph.mk sU] ∧
      s'.stk sV = [Glyph.mk sV] ∧ s'.stk sG = [Glyph.mk sG] ∧
      s'.stk sP = [Glyph.mk sP] ∧ s'.stk sQ = [Glyph.mk sQ] ∧
      s'.stk sR = [Glyph.mk sR] ∧ s'.stk sS = [Glyph.mk sS] ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  have hheadU : (s.stk sU).headD Glyph.eos = Glyph.bit b := by
    rw [hU]
    exact headD_eq_bit hUeq
  have hheadV : (s.stk sV).headD Glyph.eos = Glyph.mk sV := by
    rw [hV]
    exact headD_eq_mk hVnil
  have hne : (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State).reg rgT
      ≠ Glyph.mk sU := by
    rw [regPeek, hheadU]
    exact gBit_ne_mk b sU
  have hreg2 : (⟨Function.update (Function.update s.reg rgT ((s.stk sU).headD Glyph.eos)) rgU
        ((s.stk sV).headD Glyph.eos), s.stk⟩ : State).reg rgU = Glyph.mk sV := by
    rw [regPeek2, hheadV]
  obtain ⟨s', m', hev', hm', hU', hG', hfr'⟩ :=
    gcdScaleEval main k U []
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
  have hV' : s'.stk sV = [Glyph.mk sV] := by
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
theorem gcdRunTailBoth (main : HvdH.Cmd) (U V : List Bool) (b c : Bool) (U' V' : List Bool)
    (k : ℕ) (s : HvdH.State)
    (hU : s.stk sU = U.map Glyph.bit ++ [Glyph.mk sU]) (hUeq : U = b :: U')
    (hV : s.stk sV = V.map Glyph.bit ++ [Glyph.mk sV]) (hVeq : V = c :: V')
    (hG : s.stk sG = List.replicate k gTick ++ [Glyph.mk sG])
    (hP : s.stk sP = [Glyph.mk sP]) (hQ : s.stk sQ = [Glyph.mk sQ])
    (hR : s.stk sR = [Glyph.mk sR]) (hS : s.stk sS = [Glyph.mk sS])
    (hoddU : Work.IntLib.ofBits (dropLead U) % 2 = 1)
    (hoddV : Work.IntLib.ofBits (dropLead V) % 2 = 1) :
    ∃ s' m, HvdH.Eval main gcdRunTail s s' m ∧
      m ≤ 12000 * (U.length + V.length + k + 1) * (U.length + V.length + k + 1) + 12000 ∧
      (∃ ul : List Bool, s'.stk sU = (List.replicate k false ++ ul).map Glyph.bit
          ++ [Glyph.mk sU] ∧
        Work.IntLib.ofBits ul
          = Nat.gcd (Work.IntLib.ofBits (dropLead U)) (Work.IntLib.ofBits (dropLead V)) ∧
        ul.length ≤ max U.length V.length) ∧
      (∃ vl : List Bool, s'.stk sV = vl.map Glyph.bit ++ [Glyph.mk sV] ∧
        vl.length ≤ max U.length V.length) ∧
      s'.stk sG = [Glyph.mk sG] ∧ s'.stk sP = [Glyph.mk sP] ∧ s'.stk sQ = [Glyph.mk sQ] ∧
      s'.stk sR = [Glyph.mk sR] ∧ s'.stk sS = [Glyph.mk sS] ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  have hheadU : (s.stk sU).headD Glyph.eos = Glyph.bit b := by
    rw [hU]
    exact headD_eq_bit hUeq
  have hheadV : (s.stk sV).headD Glyph.eos = Glyph.bit c := by
    rw [hV]
    exact headD_eq_bit hVeq
  have hne : (⟨Function.update s.reg rgT ((s.stk sU).headD Glyph.eos), s.stk⟩ : State).reg rgT
      ≠ Glyph.mk sU := by
    rw [regPeek, hheadU]
    exact gBit_ne_mk b sU
  have hne2 : (⟨Function.update (Function.update s.reg rgT ((s.stk sU).headD Glyph.eos)) rgU
        ((s.stk sV).headD Glyph.eos), s.stk⟩ : State).reg rgU ≠ Glyph.mk sV := by
    rw [regPeek2, hheadV]
    exact gBit_ne_mk c sV
  obtain ⟨s', m', hev', hm', hUl', hVl', hG', hP', hQ', hR', hS', hfr'⟩ :=
    gcdRunBranchB2 main U V k
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


theorem gcdRunEval (main : HvdH.Cmd) (a b : ℤ) (s : HvdH.State)
    (hU : s.stk sU = a.natAbs.bits.map Glyph.bit ++ [Glyph.mk sU])
    (hV : s.stk sV = b.natAbs.bits.map Glyph.bit ++ [Glyph.mk sV])
    (hG : s.stk sG = [Glyph.mk sG])
    (hP : s.stk sP = [Glyph.mk sP]) (hQ : s.stk sQ = [Glyph.mk sQ])
    (hR : s.stk sR = [Glyph.mk sR]) (hS : s.stk sS = [Glyph.mk sS]) :
    ∃ s' m, HvdH.Eval main gcdRun s s' m ∧
      m ≤ 60000 * (HvdH.isz a + HvdH.isz b + 1)
            * (HvdH.isz a + HvdH.isz b + 1) + 30000 ∧
      (∃ ul : List Bool, s'.stk sU = ul.map Glyph.bit ++ [Glyph.mk sU] ∧
        Work.IntLib.ofBits ul = Int.gcd a b ∧
        ul.length ≤ a.natAbs.size + b.natAbs.size) ∧
      (∃ vl : List Bool, s'.stk sV = vl.map Glyph.bit ++ [Glyph.mk sV] ∧
        vl.length ≤ a.natAbs.size + b.natAbs.size) ∧
      s'.stk sG = [Glyph.mk sG] ∧ s'.stk sP = [Glyph.mk sP] ∧ s'.stk sQ = [Glyph.mk sQ] ∧
      s'.stk sR = [Glyph.mk sR] ∧ s'.stk sS = [Glyph.mk sS] ∧
      (∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
        s'.stk j = s.stk j) := by
  obtain ⟨s1, m1, hev1, hm1, hU1, hV1, hG1, hfr1⟩ :=
    gcdPhaseAEval main a.natAbs.bits b.natAbs.bits [] [] [] [] s hU hV hG
  set k : ℕ := min ((a.natAbs.bits.takeWhile (fun b => !b)).length)
    ((b.natAbs.bits.takeWhile (fun b => !b)).length) with hk
  have hU1' : s1.stk sU = (a.natAbs.bits.drop k).map Glyph.bit ++ [Glyph.mk sU] := by
    rw [hk]; exact hU1
  have hV1' : s1.stk sV = (b.natAbs.bits.drop k).map Glyph.bit ++ [Glyph.mk sV] := by
    rw [hk]; exact hV1
  have hG1' : s1.stk sG = List.replicate k gTick ++ [Glyph.mk sG] := by
    rw [hk]; simpa using hG1
  have hP1 : s1.stk sP = [Glyph.mk sP] := by
    rw [hfr1 sP (by decide) (by decide) (by decide)]; exact hP
  have hQ1 : s1.stk sQ = [Glyph.mk sQ] := by
    rw [hfr1 sQ (by decide) (by decide) (by decide)]; exact hQ
  have hR1 : s1.stk sR = [Glyph.mk sR] := by
    rw [hfr1 sR (by decide) (by decide) (by decide)]; exact hR
  have hS1 : s1.stk sS = [Glyph.mk sS] := by
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
      gcdRunTailUempty main (a.natAbs.bits.drop k) (b.natAbs.bits.drop k) k s1 hU1' hdU hV1'
        hG1' hP1 hQ1 hR1 hS1
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
        gcdRunTailVempty main (a.natAbs.bits.drop k) (b.natAbs.bits.drop k) bU0 U' k s1 hU1'
          hdU hV1' hdV hG1' hP1 hQ1 hR1 hS1
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
        gcdRunTailBoth main (a.natAbs.bits.drop k) (b.natAbs.bits.drop k) bU0 cV U' V' k s1 hU1'
          hdU hV1' hdV hG1' hP1 hQ1 hR1 hS1 hodds hoddsV
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


/-- **The `gcdFinish ; gcdClean` phases.**  From a state whose stacks hold `ul`, `vl`, `k` ticks and
empty scratch regions, `gcdFinish` emits the canonical encoding of the value of `ul` (with the raw
content `R` below it) and `gcdClean` empties the seven scratch stacks, restoring everything else. -/
theorem gcdFinishCleanLocal (main : HvdH.Cmd) (ul vl : List Bool) (k : ℕ)
    (R : List HvdH.Glyph) (s : HvdH.State) (h0 : s.stk 0 = R)
    (hU : s.stk sU = ul.map Glyph.bit ++ [Glyph.mk sU])
    (hV : s.stk sV = vl.map Glyph.bit ++ [Glyph.mk sV])
    (hG : s.stk sG = List.replicate k gTick ++ [Glyph.mk sG])
    (hP : s.stk sP = [Glyph.mk sP]) (hQ : s.stk sQ = [Glyph.mk sQ])
    (hR : s.stk sR = [Glyph.mk sR]) (hS : s.stk sS = [Glyph.mk sS]) :
    ∃ s' m, HvdH.Eval main (HvdH.Cmd.seq gcdFinish gcdClean) s s' m ∧
      m ≤ 200 * (ul.length + vl.length + k + 1) ∧
      s'.stk 0 = (HvdH.Val.int ((Work.IntLib.ofBits ul : ℕ) : ℤ)).enc ++ R ∧
      s'.stk sU = [] ∧ s'.stk sV = [] ∧ s'.stk sG = [] ∧ s'.stk sP = [] ∧
      s'.stk sQ = [] ∧ s'.stk sR = [] ∧ s'.stk sS = [] ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR →
        j ≠ sS → s'.stk j = s.stk j) := by
  -- ## step 1: move the region of `sU` onto `sP`
  obtain ⟨s1, m1, e1, hm1, t1P, t1U, fr1⟩ := finishMove main ul s hU hP
  -- ## step 2: strip the high zeros
  obtain ⟨s2, m2, e2, hm2, t2P, fr2⟩ :=
    stripZerosRegion main sP ul.reverse s1 (by simpa using t1P)
  have t20 : s2.stk 0 = R := (fr2 0 (by decide)).trans ((fr1 0 (by decide) (by decide)).trans h0)
  have t2U : s2.stk sU = [Glyph.mk sU] := (fr2 sU (by decide)).trans t1U
  have t2V : s2.stk sV = vl.map Glyph.bit ++ [Glyph.mk sV] :=
    (fr2 sV (by decide)).trans ((fr1 sV (by decide) (by decide)).trans hV)
  have t2G : s2.stk sG = List.replicate k gTick ++ [Glyph.mk sG] :=
    (fr2 sG (by decide)).trans ((fr1 sG (by decide) (by decide)).trans hG)
  have t2Q : s2.stk sQ = [Glyph.mk sQ] :=
    (fr2 sQ (by decide)).trans ((fr1 sQ (by decide) (by decide)).trans hQ)
  have t2R : s2.stk sR = [Glyph.mk sR] :=
    (fr2 sR (by decide)).trans ((fr1 sR (by decide) (by decide)).trans hR)
  have t2S : s2.stk sS = [Glyph.mk sS] :=
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
  have t3P : S3.stk sP = (dropLead (ul.reverse)).map Glyph.bit ++ [Glyph.mk sP] := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sP (by decide)]
    exact t2P
  have t3U : S3.stk sU = [Glyph.mk sU] := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sU (by decide)]
    exact t2U
  have t3V : S3.stk sV = vl.map Glyph.bit ++ [Glyph.mk sV] := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sV (by decide)]
    exact t2V
  have t3G : S3.stk sG = List.replicate k gTick ++ [Glyph.mk sG] := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sG (by decide)]
    exact t2G
  have t3Q : S3.stk sQ = [Glyph.mk sQ] := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sQ (by decide)]
    exact t2Q
  have t3R : S3.stk sR = [Glyph.mk sR] := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sR (by decide)]
    exact t2R
  have t3S : S3.stk sS = [Glyph.mk sS] := by
    rw [hS3, updStkOther s2 Glyph.iend 0 sS (by decide)]
    exact t2S
  -- ## step 4: emit the stripped bits onto stack 0
  obtain ⟨s4, m4, e4, hm4, t40, t4P, fr4⟩ :=
    finishEmit main (dropLead (ul.reverse)) (S3.stk 0) S3 t3P rfl
  -- ## step 5: push `pos`
  let s5 : State := ⟨Function.update s4.reg rgU Glyph.pos,
    Function.update s4.stk 0 (Glyph.pos :: s4.stk 0)⟩
  have hs5 : s5 = ⟨Function.update s4.reg rgU Glyph.pos,
      Function.update s4.stk 0 (Glyph.pos :: s4.stk 0)⟩ := rfl
  obtain ⟨m5, e5, hm5, t50, fr5⟩ := finishPush main Glyph.pos (s4.stk 0) s4 rfl
  have t50' : s5.stk 0
      = Glyph.pos :: (((dropLead (ul.reverse)).map Glyph.bit).reverse ++ (Glyph.iend :: R)) := by
    rw [t50, t40, t30]
  have t5U : s5.stk sU = [Glyph.mk sU] :=
    (fr5 sU (by decide)).trans ((fr4 sU (by decide) (by decide)).trans t3U)
  have t5V : s5.stk sV = vl.map Glyph.bit ++ [Glyph.mk sV] :=
    (fr5 sV (by decide)).trans ((fr4 sV (by decide) (by decide)).trans t3V)
  have t5G : s5.stk sG = List.replicate k gTick ++ [Glyph.mk sG] :=
    (fr5 sG (by decide)).trans ((fr4 sG (by decide) (by decide)).trans t3G)
  have t5P : s5.stk sP = [Glyph.mk sP] := (fr5 sP (by decide)).trans t4P
  have t5Q : s5.stk sQ = [Glyph.mk sQ] :=
    (fr5 sQ (by decide)).trans ((fr4 sQ (by decide) (by decide)).trans t3Q)
  have t5R : s5.stk sR = [Glyph.mk sR] :=
    (fr5 sR (by decide)).trans ((fr4 sR (by decide) (by decide)).trans t3R)
  have t5S : s5.stk sS = [Glyph.mk sS] :=
    (fr5 sS (by decide)).trans ((fr4 sS (by decide) (by decide)).trans t3S)
  -- ## `gcdClean`: the seven drops, then the seven pops
  let C1 : State := dSt sU (Glyph.mk sU) rgT [] s5
  have hC1 : C1 = dSt sU (Glyph.mk sU) rgT [] s5 := rfl
  have eC1 : HvdH.Eval main (SG.rLoop sU (Glyph.mk sU) none rgT) s5 C1 7 := by
    rw [hC1]
    refine dLoop_eval main sU (Glyph.mk sU) rgT (gMk_ne_eos sU) [] [] s5 ?_ (by simp)
    simpa using t5U
  have dV : C1.stk sV = vl.map Glyph.bit ++ [Glyph.mk sV] := by
    refine (dStO sU (Glyph.mk sU) rgT [] s5 sV (by decide)).trans ?_
    exact t5V
  let C2 : State := dSt sV (Glyph.mk sV) rgT [] C1
  have hC2 : C2 = dSt sV (Glyph.mk sV) rgT [] C1 := rfl
  have eC2 : HvdH.Eval main (SG.rLoop sV (Glyph.mk sV) none rgT) C1 C2
      (7 + (vl.map Glyph.bit).length * 5) := by
    rw [hC2]
    refine dLoop_eval main sV (Glyph.mk sV) rgT (gMk_ne_eos sV) (vl.map Glyph.bit) [] C1 ?_
      (mem_map_bit_ne_mk vl sV)
    simpa using dV
  have dG : C2.stk sG = List.replicate k gTick ++ [Glyph.mk sG] := by
    refine (dStO sV (Glyph.mk sV) rgT [] C1 sG (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT [] s5 sG (by decide)).trans ?_
    exact t5G
  let C3 : State := dSt sG (Glyph.mk sG) rgT [] C2
  have hC3 : C3 = dSt sG (Glyph.mk sG) rgT [] C2 := rfl
  have eC3 : HvdH.Eval main (SG.rLoop sG (Glyph.mk sG) none rgT) C2 C3
      (7 + (List.replicate k gTick).length * 5) := by
    rw [hC3]
    refine dLoop_eval main sG (Glyph.mk sG) rgT (gMk_ne_eos sG) (List.replicate k gTick) [] C2 ?_
      (by
        intro g hg
        rw [List.mem_replicate] at hg
        rw [hg.2]
        decide)
    simpa using dG
  have dP : C3.stk sP = [Glyph.mk sP] := by
    refine (dStO sG (Glyph.mk sG) rgT [] C2 sP (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT [] C1 sP (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT [] s5 sP (by decide)).trans ?_
    exact t5P
  let C4 : State := dSt sP (Glyph.mk sP) rgT [] C3
  have hC4 : C4 = dSt sP (Glyph.mk sP) rgT [] C3 := rfl
  have eC4 : HvdH.Eval main (SG.rLoop sP (Glyph.mk sP) none rgT) C3 C4 7 := by
    rw [hC4]
    refine dLoop_eval main sP (Glyph.mk sP) rgT (gMk_ne_eos sP) [] [] C3 ?_ (by simp)
    simpa using dP
  have dQ : C4.stk sQ = [Glyph.mk sQ] := by
    refine (dStO sP (Glyph.mk sP) rgT [] C3 sQ (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT [] C2 sQ (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT [] C1 sQ (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT [] s5 sQ (by decide)).trans ?_
    exact t5Q
  let C5 : State := dSt sQ (Glyph.mk sQ) rgT [] C4
  have hC5 : C5 = dSt sQ (Glyph.mk sQ) rgT [] C4 := rfl
  have eC5 : HvdH.Eval main (SG.rLoop sQ (Glyph.mk sQ) none rgT) C4 C5 7 := by
    rw [hC5]
    refine dLoop_eval main sQ (Glyph.mk sQ) rgT (gMk_ne_eos sQ) [] [] C4 ?_ (by simp)
    simpa using dQ
  have dR : C5.stk sR = [Glyph.mk sR] := by
    refine (dStO sQ (Glyph.mk sQ) rgT [] C4 sR (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT [] C3 sR (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT [] C2 sR (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT [] C1 sR (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT [] s5 sR (by decide)).trans ?_
    exact t5R
  let C6 : State := dSt sR (Glyph.mk sR) rgT [] C5
  have hC6 : C6 = dSt sR (Glyph.mk sR) rgT [] C5 := rfl
  have eC6 : HvdH.Eval main (SG.rLoop sR (Glyph.mk sR) none rgT) C5 C6 7 := by
    rw [hC6]
    refine dLoop_eval main sR (Glyph.mk sR) rgT (gMk_ne_eos sR) [] [] C5 ?_ (by simp)
    simpa using dR
  have dS : C6.stk sS = [Glyph.mk sS] := by
    refine (dStO sR (Glyph.mk sR) rgT [] C5 sS (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT [] C4 sS (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT [] C3 sS (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT [] C2 sS (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT [] C1 sS (by decide)).trans ?_
    refine (dStO sU (Glyph.mk sU) rgT [] s5 sS (by decide)).trans ?_
    exact t5S
  let C7 : State := dSt sS (Glyph.mk sS) rgT [] C6
  have hC7 : C7 = dSt sS (Glyph.mk sS) rgT [] C6 := rfl
  have eC7 : HvdH.Eval main (SG.rLoop sS (Glyph.mk sS) none rgT) C6 C7 7 := by
    rw [hC7]
    refine dLoop_eval main sS (Glyph.mk sS) rgT (gMk_ne_eos sS) [] [] C6 ?_ (by simp)
    simpa using dS
  -- ## the seven pops
  have pU : C7.stk sU = [Glyph.mk sU] := by
    refine (dStO sS (Glyph.mk sS) rgT [] C6 sU (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT [] C5 sU (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT [] C4 sU (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT [] C3 sU (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT [] C2 sU (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT [] C1 sU (by decide)).trans ?_
    exact dStK sU (Glyph.mk sU) rgT [] s5
  let C8 : State := ⟨Function.update C7.reg rgT (Glyph.mk sU), Function.update C7.stk sU []⟩
  have hC8 : C8 = ⟨Function.update C7.reg rgT (Glyph.mk sU), Function.update C7.stk sU []⟩ := rfl
  have eC8 : HvdH.Eval main (.pop sU rgT) C7 C8 1 := by
    rw [hC8]
    exact Work.IntLib.Eval.pop_cons (s := C7) (k := sU) (r := rgT) (g := Glyph.mk sU) (rest := [])
      (by simpa using pU)
  have pV : C8.stk sV = [Glyph.mk sV] := by
    refine (dStO sS (Glyph.mk sS) rgT [] C6 sV (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT [] C5 sV (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT [] C4 sV (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT [] C3 sV (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT [] C2 sV (by decide)).trans ?_
    exact dStK sV (Glyph.mk sV) rgT [] C1
  let C9 : State := ⟨Function.update C8.reg rgT (Glyph.mk sV), Function.update C8.stk sV []⟩
  have hC9 : C9 = ⟨Function.update C8.reg rgT (Glyph.mk sV), Function.update C8.stk sV []⟩ := rfl
  have eC9 : HvdH.Eval main (.pop sV rgT) C8 C9 1 := by
    rw [hC9]
    exact Work.IntLib.Eval.pop_cons (s := C8) (k := sV) (r := rgT) (g := Glyph.mk sV) (rest := [])
      (by simpa using pV)
  have pG : C9.stk sG = [Glyph.mk sG] := by
    refine (dStO sS (Glyph.mk sS) rgT [] C6 sG (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT [] C5 sG (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT [] C4 sG (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT [] C3 sG (by decide)).trans ?_
    exact dStK sG (Glyph.mk sG) rgT [] C2
  let C10 : State := ⟨Function.update C9.reg rgT (Glyph.mk sG), Function.update C9.stk sG []⟩
  have hC10 : C10 = ⟨Function.update C9.reg rgT (Glyph.mk sG), Function.update C9.stk sG []⟩ := rfl
  have eC10 : HvdH.Eval main (.pop sG rgT) C9 C10 1 := by
    rw [hC10]
    exact Work.IntLib.Eval.pop_cons (s := C9) (k := sG) (r := rgT) (g := Glyph.mk sG) (rest := [])
      (by simpa using pG)
  have pP : C10.stk sP = [Glyph.mk sP] := by
    refine (dStO sS (Glyph.mk sS) rgT [] C6 sP (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT [] C5 sP (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT [] C4 sP (by decide)).trans ?_
    exact dStK sP (Glyph.mk sP) rgT [] C3
  let C11 : State := ⟨Function.update C10.reg rgT (Glyph.mk sP), Function.update C10.stk sP []⟩
  have hC11 : C11 = ⟨Function.update C10.reg rgT (Glyph.mk sP), Function.update C10.stk sP []⟩ := rfl
  have eC11 : HvdH.Eval main (.pop sP rgT) C10 C11 1 := by
    rw [hC11]
    exact Work.IntLib.Eval.pop_cons (s := C10) (k := sP) (r := rgT) (g := Glyph.mk sP) (rest := [])
      (by simpa using pP)
  have pQ : C11.stk sQ = [Glyph.mk sQ] := by
    refine (dStO sS (Glyph.mk sS) rgT [] C6 sQ (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT [] C5 sQ (by decide)).trans ?_
    exact dStK sQ (Glyph.mk sQ) rgT [] C4
  let C12 : State := ⟨Function.update C11.reg rgT (Glyph.mk sQ), Function.update C11.stk sQ []⟩
  have hC12 : C12 = ⟨Function.update C11.reg rgT (Glyph.mk sQ), Function.update C11.stk sQ []⟩ := rfl
  have eC12 : HvdH.Eval main (.pop sQ rgT) C11 C12 1 := by
    rw [hC12]
    exact Work.IntLib.Eval.pop_cons (s := C11) (k := sQ) (r := rgT) (g := Glyph.mk sQ) (rest := [])
      (by simpa using pQ)
  have pR : C12.stk sR = [Glyph.mk sR] := by
    refine (dStO sS (Glyph.mk sS) rgT [] C6 sR (by decide)).trans ?_
    exact dStK sR (Glyph.mk sR) rgT [] C5
  let C13 : State := ⟨Function.update C12.reg rgT (Glyph.mk sR), Function.update C12.stk sR []⟩
  have hC13 : C13 = ⟨Function.update C12.reg rgT (Glyph.mk sR), Function.update C12.stk sR []⟩ := rfl
  have eC13 : HvdH.Eval main (.pop sR rgT) C12 C13 1 := by
    rw [hC13]
    exact Work.IntLib.Eval.pop_cons (s := C12) (k := sR) (r := rgT) (g := Glyph.mk sR) (rest := [])
      (by simpa using pR)
  have pS : C13.stk sS = [Glyph.mk sS] := dStK sS (Glyph.mk sS) rgT [] C6
  let C14 : State := ⟨Function.update C13.reg rgT (Glyph.mk sS), Function.update C13.stk sS []⟩
  have hC14 : C14 = ⟨Function.update C13.reg rgT (Glyph.mk sS), Function.update C13.stk sS []⟩ := rfl
  have eC14 : HvdH.Eval main (.pop sS rgT) C13 C14 1 := by
    rw [hC14]
    exact Work.IntLib.Eval.pop_cons (s := C13) (k := sS) (r := rgT) (g := Glyph.mk sS) (rest := [])
      (by simpa using pS)
  -- ## the final facts
  have hfinU : C14.stk sU = [] := by
    refine (updStkO C13 rgT (Glyph.mk sS) sS sU (by decide)).trans ?_
    refine (updStkO C12 rgT (Glyph.mk sR) sR sU (by decide)).trans ?_
    refine (updStkO C11 rgT (Glyph.mk sQ) sQ sU (by decide)).trans ?_
    refine (updStkO C10 rgT (Glyph.mk sP) sP sU (by decide)).trans ?_
    refine (updStkO C9 rgT (Glyph.mk sG) sG sU (by decide)).trans ?_
    refine (updStkO C8 rgT (Glyph.mk sV) sV sU (by decide)).trans ?_
    exact updStk C7 rgT (Glyph.mk sU) sU
  have hfinV : C14.stk sV = [] := by
    refine (updStkO C13 rgT (Glyph.mk sS) sS sV (by decide)).trans ?_
    refine (updStkO C12 rgT (Glyph.mk sR) sR sV (by decide)).trans ?_
    refine (updStkO C11 rgT (Glyph.mk sQ) sQ sV (by decide)).trans ?_
    refine (updStkO C10 rgT (Glyph.mk sP) sP sV (by decide)).trans ?_
    refine (updStkO C9 rgT (Glyph.mk sG) sG sV (by decide)).trans ?_
    exact updStk C8 rgT (Glyph.mk sV) sV
  have hfinG : C14.stk sG = [] := by
    refine (updStkO C13 rgT (Glyph.mk sS) sS sG (by decide)).trans ?_
    refine (updStkO C12 rgT (Glyph.mk sR) sR sG (by decide)).trans ?_
    refine (updStkO C11 rgT (Glyph.mk sQ) sQ sG (by decide)).trans ?_
    refine (updStkO C10 rgT (Glyph.mk sP) sP sG (by decide)).trans ?_
    exact updStk C9 rgT (Glyph.mk sG) sG
  have hfinP : C14.stk sP = [] := by
    refine (updStkO C13 rgT (Glyph.mk sS) sS sP (by decide)).trans ?_
    refine (updStkO C12 rgT (Glyph.mk sR) sR sP (by decide)).trans ?_
    refine (updStkO C11 rgT (Glyph.mk sQ) sQ sP (by decide)).trans ?_
    exact updStk C10 rgT (Glyph.mk sP) sP
  have hfinQ : C14.stk sQ = [] := by
    refine (updStkO C13 rgT (Glyph.mk sS) sS sQ (by decide)).trans ?_
    refine (updStkO C12 rgT (Glyph.mk sR) sR sQ (by decide)).trans ?_
    exact updStk C11 rgT (Glyph.mk sQ) sQ
  have hfinR : C14.stk sR = [] :=
    (updStkO C13 rgT (Glyph.mk sS) sS sR (by decide)).trans (updStk C12 rgT (Glyph.mk sR) sR)
  have hfinS : C14.stk sS = [] := updStk C13 rgT (Glyph.mk sS) sS
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
    refine (updStkO C13 rgT (Glyph.mk sS) sS 0 (by decide)).trans ?_
    refine (updStkO C12 rgT (Glyph.mk sR) sR 0 (by decide)).trans ?_
    refine (updStkO C11 rgT (Glyph.mk sQ) sQ 0 (by decide)).trans ?_
    refine (updStkO C10 rgT (Glyph.mk sP) sP 0 (by decide)).trans ?_
    refine (updStkO C9 rgT (Glyph.mk sG) sG 0 (by decide)).trans ?_
    refine (updStkO C8 rgT (Glyph.mk sV) sV 0 (by decide)).trans ?_
    refine (updStkO C7 rgT (Glyph.mk sU) sU 0 (by decide)).trans ?_
    refine (dStO sS (Glyph.mk sS) rgT [] C6 0 (by decide)).trans ?_
    refine (dStO sR (Glyph.mk sR) rgT [] C5 0 (by decide)).trans ?_
    refine (dStO sQ (Glyph.mk sQ) rgT [] C4 0 (by decide)).trans ?_
    refine (dStO sP (Glyph.mk sP) rgT [] C3 0 (by decide)).trans ?_
    refine (dStO sG (Glyph.mk sG) rgT [] C2 0 (by decide)).trans ?_
    refine (dStO sV (Glyph.mk sV) rgT [] C1 0 (by decide)).trans ?_
    exact dStO sU (Glyph.mk sU) rgT [] s5 0 (by decide)
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

/-! ## The whole word -/

theorem gcdFinishEval (main : HvdH.Cmd) (a b : ℤ) (R : List HvdH.Glyph) (s : HvdH.State)
    (h0 : s.stk 0 = R)
    (hU : s.stk Work.IntLib.SG.sU = a.natAbs.bits.map HvdH.Glyph.bit
      ++ [HvdH.Glyph.mk Work.IntLib.SG.sU])
    (hV : s.stk Work.IntLib.SG.sV = b.natAbs.bits.map HvdH.Glyph.bit
      ++ [HvdH.Glyph.mk Work.IntLib.SG.sV])
    (hG : s.stk Work.IntLib.SG.sG = [HvdH.Glyph.mk Work.IntLib.SG.sG])
    (hP : s.stk Work.IntLib.SG.sP = [HvdH.Glyph.mk Work.IntLib.SG.sP])
    (hQ : s.stk Work.IntLib.SG.sQ = [HvdH.Glyph.mk Work.IntLib.SG.sQ])
    (hR : s.stk Work.IntLib.SG.sR = [HvdH.Glyph.mk Work.IntLib.SG.sR])
    (hS : s.stk Work.IntLib.SG.sS = [HvdH.Glyph.mk Work.IntLib.SG.sS]) :
    ∃ s' m, HvdH.Eval main
        (HvdH.Cmd.seq Work.IntLib.SG.gcdRun
          (HvdH.Cmd.seq Work.IntLib.SG.gcdFinish Work.IntLib.SG.gcdClean)) s s' m ∧
      m ≤ 100000 * (HvdH.isz a + HvdH.isz b + 1) * (HvdH.isz a + HvdH.isz b + 1) + 100000 ∧
      s'.stk 0 = (HvdH.Val.int (Int.gcd a b)).enc ++ R ∧
      s'.stk Work.IntLib.SG.sU = [] ∧ s'.stk Work.IntLib.SG.sV = [] ∧
      s'.stk Work.IntLib.SG.sG = [] ∧ s'.stk Work.IntLib.SG.sP = [] ∧
      s'.stk Work.IntLib.SG.sQ = [] ∧ s'.stk Work.IntLib.SG.sR = [] ∧
      s'.stk Work.IntLib.SG.sS = [] ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ Work.IntLib.SG.sU → k ≠ Work.IntLib.SG.sV →
        k ≠ Work.IntLib.SG.sG → k ≠ Work.IntLib.SG.sP → k ≠ Work.IntLib.SG.sQ →
        k ≠ Work.IntLib.SG.sR → k ≠ Work.IntLib.SG.sS → s'.stk k = s.stk k) := by
  obtain ⟨s1, m1, hev1, hm1, ⟨ul, hUl, hUlv, hUllen⟩, ⟨vl, hVl, hVllen⟩, hG1, hP1, hQ1, hR1, hS1,
    hfr1⟩ := gcdRunEval main a b s hU hV hG hP hQ hR hS
  have h01 : s1.stk 0 = R := by
    rw [hfr1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h0
  have hG1' : s1.stk sG = List.replicate 0 gTick ++ [Glyph.mk sG] := by simpa using hG1
  obtain ⟨s2, m2, hev2, hm2, h0', hU2, hV2, hG2, hP2, hQ2, hR2, hS2, hfr2⟩ :=
    gcdFinishCleanLocal main ul vl 0 R s1 h01 hUl hVl hG1' hP1 hQ1 hR1 hS1
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
