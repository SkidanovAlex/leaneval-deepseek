import Submission.Work.IntLib.SqrtGcd.sqrtLoopKit
import Submission.Work.IntLib.SqrtGcd.sqrtWorkStep

/-!
# The square-root loop, with the scratch regions restored exactly

This is `Work.IntLib.SqrtGcd.sqrtLoopEval` (from the colleague's `sqrtLoopEval.lean`) restated in a
form usable at the call site of `SG.sqrtProg`: the four scratch stacks `sP … sS` are returned
*exactly* as `marker :: old`, not merely "some bit list above the marker".  The finish is a move of
the root region through `sP`, so a pre-existing region there would end up inside the emitted number
and the specification would be unusable.

The proof is copied verbatim from `sqrtLoopEval.lean`; only the one-step lemma is imported from the
standalone module `sqrtWorkStep.lean` instead of the temporary copy inside that file, and the four
surplus existentials in the conclusion are dropped (the proof already knows the exact content).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd.Len

open HvdH Work.Layout Work.IntLib
open Work.IntLib.SG

/-- `rgF` is not touched by `sqrtWork` (it is the loop flag of the outer loop). -/
theorem rgF_notin_sqrtWork : rgF ∉ cmdTouchesR sqrtWork := by decide

/-- The stop branch of `sqrtBody`: the radicand is exhausted, so the loop flag becomes `gStop`.
Cost `3`, and the stacks are unchanged. -/
theorem sqrtBodyStopEv (main : Cmd) (s : State) (bA : List Glyph)
    (hA : s.stk sA = Glyph.mk sA :: bA) :
    ∃ s', Ev main sqrtBody s s' 3 ∧ s'.stk = s.stk ∧ s'.reg rgF = gStop := by
  let u1 : State := ⟨Function.update s.reg rgT ((s.stk sA).headD Glyph.eos), s.stk⟩
  let u2 : State := ⟨Function.update u1.reg rgF gStop, u1.stk⟩
  have e1 : Ev main (.peek sA rgT) s u1 1 := ev_peek main sA rgT s
  have hu1 : u1.reg rgT = Glyph.mk sA := by
    simp only [u1]
    rw [Function.update_self, hA]
    rfl
  have e2 : Ev main (.set rgF gStop) u1 u2 1 := by
    have h := ev_set main rgF gStop u1
    simpa only [u2] using h
  refine ⟨u2, Ev.seq e1 (Ev.iteT hu1 e2), ?_, ?_⟩
  · simp only [u2, u1]
  · simp only [u2, Function.update_self]

/-- The go branch of `sqrtBody`: two radicand bits are present, `rgF` is set to `gGo` and the
restoring step `sqrtWork` runs. -/
theorem sqrtBodyGoEv (main : Cmd) (s₀ s : State) (bA bB bC bP bQ bR bS : List Glyph)
    (x y : Bool) (rest rb rc : List Bool) (rem r : ℕ)
    (hA : s.stk sA = (x :: y :: rest).map Glyph.bit ++ Glyph.mk sA :: bA)
    (hB : s.stk sB = rb.map Glyph.bit ++ Glyph.mk sB :: bB)
    (hC : s.stk sC = rc.map Glyph.bit ++ Glyph.mk sC :: bC)
    (hP : s.stk sP = Glyph.mk sP :: bP)
    (hQ : s.stk sQ = Glyph.mk sQ :: bQ)
    (hR : s.stk sR = Glyph.mk sR :: bR)
    (hS : s.stk sS = Glyph.mk sS :: bS)
    (hfr : Frame7 s₀ s)
    (hBv : ofBits rb = rem) (hCv : ofBits rc = r) :
    ∃ (s' : State) (rbl rcl : List Bool),
      Ev main sqrtBody s s' (503 + 200 * rb.length + 200 * rc.length) ∧
      s'.stk sA = rest.map Glyph.bit ++ Glyph.mk sA :: bA ∧
      s'.stk sB = rbl.map Glyph.bit ++ Glyph.mk sB :: bB ∧
      s'.stk sC = rcl.map Glyph.bit ++ Glyph.mk sC :: bC ∧
      ofBits rcl = 2 * r + (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 1 else 0) ∧
      ofBits rbl = 4 * rem + (2 * x.toNat + y.toNat)
          - (if 4 * r + 1 ≤ 4 * rem + (2 * x.toNat + y.toNat) then 4 * r + 1 else 0) ∧
      rcl.length = rc.length + 1 ∧
      rbl.length ≤ max rb.length rc.length + 2 ∧
      s'.stk sP = Glyph.mk sP :: bP ∧ s'.stk sQ = Glyph.mk sQ :: bQ ∧
      s'.stk sR = Glyph.mk sR :: bR ∧ s'.stk sS = Glyph.mk sS :: bS ∧
      s'.reg rgF = gGo ∧ Frame7 s₀ s' := by
  let u1 : State := ⟨Function.update s.reg rgT ((s.stk sA).headD Glyph.eos), s.stk⟩
  have e1 : Ev main (.peek sA rgT) s u1 1 := ev_peek main sA rgT s
  have hu1rT : u1.reg rgT = Glyph.bit x := by
    simp only [u1]
    rw [Function.update_self, hA]
    rfl
  have hne : ¬ (u1.reg rgT = Glyph.mk sA) := by
    rw [hu1rT]; intro h; cases h
  let u2 : State := ⟨Function.update u1.reg rgF gGo, u1.stk⟩
  have e2 : Ev main (.set rgF gGo) u1 u2 1 := by
    have h := ev_set main rgF gGo u1
    simpa only [u2] using h
  have hu2F : u2.reg rgF = gGo := by simp only [u2, Function.update_self]
  have hu2stk : u2.stk = s.stk := by simp only [u2, u1]
  have hu2Frame : Frame7 s₀ u2 := fun j ha hb hc hd he hf hg => by
    rw [hu2stk]; exact hfr j ha hb hc hd he hf hg
  obtain ⟨u3, m3, rbl, rcl, he3, hm3, hA3, hB3, hC3, hCv3, hBv3, hClen3, hBlen3, hP3, hQ3, hR3,
    hS3, hfr3⟩ :=
    Work.IntLib.SqrtGcd.sqrtWorkStep main s₀ u2 bA bB bC bP bQ bR bS x y rest rb rc rem r
      (by rw [hu2stk]; exact hA) (by rw [hu2stk]; exact hB) (by rw [hu2stk]; exact hC)
      (by rw [hu2stk]; exact hP) (by rw [hu2stk]; exact hQ) (by rw [hu2stk]; exact hR)
      (by rw [hu2stk]; exact hS) hu2Frame hBv hCv
  have e3 : Ev main sqrtWork u2 u3 (500 + 200 * rb.length + 200 * rc.length) := ⟨m3, he3, hm3⟩
  have hreg3 : u3.reg rgF = gGo := (Ev.reg_frame e3 (r := rgF) rgF_notin_sqrtWork).trans hu2F
  exact ⟨u3, rbl, rcl, (Ev.seq e1 (Ev.iteF hne (Ev.seq e2 e3))).mono (by omega), hA3, hB3,
    hC3, hCv3, hBv3, hClen3, hBlen3, hP3, hQ3, hR3, hS3, hreg3, hfr3⟩

/-! ## The loop -/

/-- The restoring loop: `k + 1` iterations starting from a state satisfying the invariant with
`rest.length = 2 * k`.  The first `k` iterations consume one pair of radicand bits each; the last
one discovers that the radicand is exhausted and stops the loop. -/
theorem sqrtLoopRunsAux (main : Cmd) (bs : List Bool) (bA bB bC bP bQ bR bS : List Glyph)
    (s₀ : State) :
    ∀ (k : ℕ) (rest rb rc : List Bool) (S rem r : ℕ) (s : State),
      Inv bs bA bB bC bP bQ bR bS s₀ s rest rb rc S rem r →
      rest.length = 2 * k →
      s.reg rgF = gGo →
      ∃ (s' : State) (C : ℕ) (rl bl : List Bool),
        loopRuns main rgF gGo sqrtBody (k + 1) s s' C ∧
        C ≤ 500 * (bs.length + 2) * (2 * k + 1) + 4 ∧
        s'.stk sA = Glyph.mk sA :: bA ∧
        s'.stk sB = bl.map Glyph.bit ++ Glyph.mk sB :: bB ∧
        s'.stk sC = rl.map Glyph.bit ++ Glyph.mk sC :: bC ∧
        ofBits rl = Nat.sqrt (SG.bval bs) ∧
        s'.stk sP = Glyph.mk sP :: bP ∧ s'.stk sQ = Glyph.mk sQ :: bQ ∧
        s'.stk sR = Glyph.mk sR :: bR ∧ s'.stk sS = Glyph.mk sS :: bS ∧
        s'.reg rgF ≠ gGo ∧ Frame7 s₀ s' := by
  intro k
  induction k with
  | zero =>
      intro rest rb rc S rem r s hInv hlen hreg
      have hrest : rest = [] := List.length_eq_zero_iff.mp (by omega)
      subst hrest
      obtain ⟨s', hEv, hstk, hreg'⟩ := sqrtBodyStopEv main s bA hInv.hA
      have hbval : SG.bval bs = S := by
        have h := hInv.hrel
        simp only [List.length_nil, pow_zero, one_mul] at h
        rw [show SG.bval ([] : List Bool) = 0 from rfl, zero_add] at h
        exact h
      refine ⟨s', 4, rc, rb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact loopRuns.one hreg hEv
      · simp only [Nat.mul_zero, Nat.add_zero]; omega
      · rw [hstk]; exact hInv.hA
      · rw [hstk]; exact hInv.hB
      · rw [hstk]; exact hInv.hC
      · rw [hInv.hCv, hbval]
        exact Nat.eq_sqrt'.mpr ⟨hInv.hlo, hInv.hhi⟩
      · rw [hstk]; exact hInv.hP
      · rw [hstk]; exact hInv.hQ
      · rw [hstk]; exact hInv.hR
      · rw [hstk]; exact hInv.hS
      · rw [hreg']; intro hc; cases hc
      · intro j ha hb hc hd he hf hg
        rw [hstk]; exact hInv.hfr j ha hb hc hd he hf hg
  | succ k ih =>
      intro rest rb rc S rem r s hInv hlen hreg
      rcases rest with _ | ⟨x, rest1⟩
      · simp only [List.length_nil] at hlen; omega
      rcases rest1 with _ | ⟨y, rest'⟩
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      have hlen' : rest'.length = 2 * k := by
        simp only [List.length_cons] at hlen; omega
      obtain ⟨s1, rbl, rcl, hEv, hA1, hB1, hC1, hCv1, hBv1, hClen1, hBlen1, hP1, hQ1, hR1,
        hS1, hregF1, hfr1⟩ :=
        sqrtBodyGoEv main s₀ s bA bB bC bP bQ bR bS x y rest' rb rc rem r
          hInv.hA hInv.hB hInv.hC hInv.hP hInv.hQ hInv.hR hInv.hS hInv.hfr hInv.hBv hInv.hCv
      have hhlo : rb.length ≤ bs.length := by
        have h := hInv.hbl; simp only [List.length_cons] at h; omega
      have hhcl : rc.length ≤ bs.length := by
        have h := hInv.hcl; simp only [List.length_cons] at h; omega
      have hss := sqrtStepSpec S r rem x y hInv.hrem hInv.hlo hInv.hhi
      dsimp only at hss
      have hrel' : SG.bval bs
          = SG.bval rest' + 2 ^ rest'.length * (SG.sqrtStep S r rem x y).1 := by
        have h := hInv.hrel
        rw [SG.bval_cons_cons] at h
        have hpow : 2 ^ (x :: y :: rest').length * S = 4 * 2 ^ rest'.length * S := by
          rw [show (x :: y :: rest').length = rest'.length + 2 by simp, pow_add]
          ring
        rw [hpow] at h
        rw [hss.1]
        have hfac : 2 ^ rest'.length * (4 * S + (2 * x.toNat + y.toNat))
            = 2 ^ rest'.length * (2 * x.toNat + y.toNat) + 4 * 2 ^ rest'.length * S := by
          ring
        rw [hfac]
        omega
      have hbl' : rbl.length + rest'.length ≤ bs.length := by
        have hb := hInv.hbl
        have hc := hInv.hcl
        simp only [List.length_cons] at hb hc
        have hmx : max rb.length rc.length + 2 + rest'.length ≤ bs.length := by
          rcases le_total rb.length rc.length with h | h
          · rw [max_eq_right h]; omega
          · rw [max_eq_left h]; omega
        omega
      have hcl' : rcl.length + rest'.length ≤ bs.length := by
        have hc := hInv.hcl
        simp only [List.length_cons] at hc
        omega
      have hpair : rest'.length % 2 = 0 := by rw [hlen']; omega
      have hInv1 : Inv bs bA bB bC bP bQ bR bS s₀ s1 rest' rbl rcl
          (SG.sqrtStep S r rem x y).1 (SG.sqrtStep S r rem x y).2.2
          (SG.sqrtStep S r rem x y).2.1 :=
        { hA := hA1
          hB := hB1
          hC := hC1
          hP := hP1
          hQ := hQ1
          hR := hR1
          hS := hS1
          hfr := hfr1
          hBv := by rw [hBv1, sqrtStep_trd]
          hCv := by rw [hCv1, sqrtStep_snd]
          hrel := hrel'
          hlo := hss.2.1
          hhi := hss.2.2.1
          hrem := hss.2.2.2
          hbl := hbl'
          hcl := hcl'
          hpar := hpair }
      obtain ⟨s2, C2, rl2, bl2, hRuns2, hC2, hA2, hB2, hC2', hval2, hP2, hQ2, hR2, hS2,
        hreg2, hfr2⟩ :=
        ih rest' rbl rcl (SG.sqrtStep S r rem x y).1 (SG.sqrtStep S r rem x y).2.2
          (SG.sqrtStep S r rem x y).2.1 s1 hInv1 hlen' hregF1
      have h1 : loopRuns main rgF gGo sqrtBody 1 s s1
          (503 + 200 * rb.length + 200 * rc.length + 1) := loopRuns.one hreg hEv
      refine ⟨s2, (503 + 200 * rb.length + 200 * rc.length + 1) + C2, rl2, bl2, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine loopRuns.cast (by omega) (loopRuns.concat (k + 1) h1 hRuns2)
      · have h2 : C2 ≤ 500 * (bs.length + 2) * (2 * k + 1) + 4 := hC2
        have hb : 0 ≤ bs.length := Nat.zero_le _
        have h1b : 503 + 200 * rb.length + 200 * rc.length + 1
            ≤ 500 * (bs.length + 2) * 2 := by
          nlinarith [hhlo, hhcl, hb]
        nlinarith [h1b, h2, hb]
      · exact hA2
      · exact hB2
      · exact hC2'
      · exact hval2
      · exact hP2
      · exact hQ2
      · exact hR2
      · exact hS2
      · exact hreg2
      · exact hfr2

/-! ## The square-root word -/

theorem sqrtLoopEvalLen (main : HvdH.Cmd) (bs : List Bool)
    (bA bB bC bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (hA : s.stk Work.IntLib.SG.sA = bs.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sA :: bA)
    (hB : s.stk Work.IntLib.SG.sB = HvdH.Glyph.mk Work.IntLib.SG.sB :: bB)
    (hC : s.stk Work.IntLib.SG.sC = HvdH.Glyph.mk Work.IntLib.SG.sC :: bC)
    (hP : s.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP)
    (hQ : s.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ)
    (hR : s.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR)
    (hS : s.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS)
    (heven : bs.length % 2 = 0) :
    ∃ s' m, HvdH.Eval main Work.IntLib.SG.sqrtLoop s s' m ∧
      m ≤ 100000 * (bs.length + 1) * (bs.length + 1) + 100000 ∧
      s'.stk Work.IntLib.SG.sA = HvdH.Glyph.mk Work.IntLib.SG.sA :: bA ∧
      (∃ rl : List Bool, s'.stk Work.IntLib.SG.sC = rl.map HvdH.Glyph.bit
          ++ HvdH.Glyph.mk Work.IntLib.SG.sC :: bC ∧
        Work.IntLib.ofBits rl = Nat.sqrt (Work.IntLib.SG.bval bs)) ∧
      (∃ ml : List Bool, s'.stk Work.IntLib.SG.sB = ml.map HvdH.Glyph.bit
          ++ HvdH.Glyph.mk Work.IntLib.SG.sB :: bB) ∧
      s'.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP ∧
      s'.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ ∧
      s'.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR ∧
      s'.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.SG.sA → j ≠ Work.IntLib.SG.sB → j ≠ Work.IntLib.SG.sC →
        j ≠ Work.IntLib.SG.sP → j ≠ Work.IntLib.SG.sQ → j ≠ Work.IntLib.SG.sR →
        j ≠ Work.IntLib.SG.sS → s'.stk j = s.stk j) := by
  let u : State := ⟨Function.update s.reg rgF gGo, s.stk⟩
  have huStk : u.stk = s.stk := by simp only [u]
  have huF : u.reg rgF = gGo := by simp only [u, Function.update_self]
  have hInvU : Inv bs bA bB bC bP bQ bR bS s u bs [] [] 0 0 0 :=
    { hA := by rw [huStk]; exact hA
      hB := by rw [huStk]; exact hB
      hC := by rw [huStk]; exact hC
      hP := by rw [huStk]; exact hP
      hQ := by rw [huStk]; exact hQ
      hR := by rw [huStk]; exact hR
      hS := by rw [huStk]; exact hS
      hfr := fun j ha hb hc hd he hf hg => by rw [huStk]
      hBv := rfl
      hCv := rfl
      hrel := by simp
      hlo := by simp
      hhi := by simp
      hrem := by simp
      hbl := by simp
      hcl := by simp
      hpar := heven }
  have hk : bs.length = 2 * (bs.length / 2) := by
    have h := Nat.div_add_mod bs.length 2
    omega
  obtain ⟨s', C, rl, bl, hRuns, hCb, hA', hB', hC', hval', hP', hQ', hR', hS', hregn, hfr'⟩ :=
    sqrtLoopRunsAux main bs bA bB bC bP bQ bR bS s (bs.length / 2) bs [] [] 0 0 0 u
      hInvU hk huF
  obtain ⟨m, hEvalLoop, hmle⟩ := loopRuns.eval' hRuns hregn
  have hEvAll : Ev main sqrtLoop s s' (1 + (C + 1)) := by
    rw [show sqrtLoop = .seq (.set rgF gGo) (.loop rgF gGo sqrtBody) from rfl]
    exact Ev.seq (ev_set main rgF gGo s) ⟨m, hEvalLoop, hmle⟩
  obtain ⟨m', hEval', hm'⟩ := hEvAll
  refine ⟨s', m', hEval', ?_, hA', ⟨rl, hC', hval'⟩, ⟨bl, hB'⟩,
    hP', hQ', hR',
    hS', fun j ha hb hc hd he hf hg => hfr' j ha hb hc hd he hf hg⟩
  have h2 : 2 * (bs.length / 2) + 1 ≤ bs.length + 1 := by
    have h := Nat.div_mul_le_self bs.length 2
    omega
  have hC1 : C ≤ 500 * (bs.length + 2) * (bs.length + 1) + 4 := by
    have hmul : 500 * (bs.length + 2) * (2 * (bs.length / 2) + 1)
        ≤ 500 * (bs.length + 2) * (bs.length + 1) := mul_le_mul_right h2 (500 * (bs.length + 2))
    linarith
  have h3 : bs.length + 2 ≤ 2 * (bs.length + 1) := by omega
  have h6 : 500 * (bs.length + 2) * (bs.length + 1)
      ≤ 100000 * (bs.length + 1) * (bs.length + 1) := by
    have hA : 500 * (bs.length + 2) ≤ 1000 * (bs.length + 1) := by
      calc 500 * (bs.length + 2) ≤ 500 * (2 * (bs.length + 1)) := mul_le_mul_right h3 500
        _ = 1000 * (bs.length + 1) := by ring
    have hB : 500 * (bs.length + 2) * (bs.length + 1)
        ≤ 1000 * (bs.length + 1) * (bs.length + 1) := mul_le_mul_left hA (bs.length + 1)
    have hC : 1000 * (bs.length + 1) * (bs.length + 1)
        ≤ 100000 * (bs.length + 1) * (bs.length + 1) :=
      mul_le_mul_left (mul_le_mul_left (by norm_num : (1000:ℕ) ≤ 100000) (bs.length + 1))
        (bs.length + 1)
    linarith
  linarith


end Work.IntLib.SqrtGcd.Len
