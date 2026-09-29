import Mathlib
import Submission.Work.IntLib.SqrtGcd.SqrtProg
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.SqrtGcd.sqrtFinishTail

/-!
# `sqrtFinishEval`: emitting the root of the square root

The last two procedures of `Work.IntLib.SG.sqrtProg` are

* `sqrtFinish` — moves the root region (`sC`, above its marker) through the scratch region `sP`
  (reversing it, hence most significant bit first), strips the leading zero bits, and emits the
  canonical encoding `pos :: (ofBits rl).bits ++ [iend]` of the root on stack 0;
* `sqrtClean` — drops the seven scratch regions `1..7` and pops their markers, restoring each
  stack to the list that sat below its marker.

The `sqrtFinish` half is split off as `sqrtFinishAux`; the pieces it is built from are
`moveRegionRevEval` (the `SG.mLoop_eval` read-off) and `Work.IntLib.SqrtGcd.sqrtFinishTail` (the
strip/emit tail).  The `sqrtClean` half `sqrtCleanAux` is stated with an *arbitrary* region on
`sB`, which is the form needed at the call site inside `sqrtProg`: after the restoring loop the
leftover remainder `S - r ^ 2` is in general non-empty there (see `sqrtInvDefs.Inv.hB`), while the
final lemma `sqrtFinishEval` below is stated with that region empty, as requested.  The general
variant `sqrtFinishEvalGen` keeps the arbitrary region, so it can be used directly after the loop.

As a by-product this file provides `moveRegionRevEval`, `dropRegionRevEval`, `popTopEval` and the
glyph/inequality helpers, all of them independent of `sqrtFinish`/`sqrtClean`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

/-! ## glyph and index helpers -/

theorem mk_ne_eos' (k : HvdH.Stk) : HvdH.Glyph.mk k ≠ HvdH.Glyph.eos := fun h => by cases h

theorem bit_ne_mk' (b : Bool) (k : HvdH.Stk) : HvdH.Glyph.bit b ≠ HvdH.Glyph.mk k :=
  fun h => by cases h

theorem mem_map_bit_ne_mk' (l : List Bool) (k : HvdH.Stk) :
    ∀ g ∈ l.map HvdH.Glyph.bit, g ≠ HvdH.Glyph.mk k := by
  intro g hg
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
  exact bit_ne_mk' b k

/-! ## generic read-offs -/

theorem moveRegionRevEval (main : HvdH.Cmd) (k d : HvdH.Stk) (T : HvdH.Glyph) (r : HvdH.Reg)
    (gs below : List HvdH.Glyph) (s : HvdH.State)
    (hT : T ≠ HvdH.Glyph.eos) (hdk : d ≠ k) (hgs : ∀ g ∈ gs, g ≠ T)
    (hstk : s.stk k = gs ++ T :: below) :
    ∃ s' m, HvdH.Eval main (Work.IntLib.SG.rLoop k T (some d) r) s s' m ∧
      m ≤ 7 + gs.length * 5 ∧
      s'.stk d = gs.reverse ++ s.stk d ∧ s'.stk k = T :: below ∧
      (∀ j : HvdH.Stk, j ≠ k → j ≠ d → s'.stk j = s.stk j) := by
  refine ⟨_, _, Work.IntLib.SG.mLoop_eval main k T d r hT hdk gs below s hstk hgs, le_rfl, ?_, ?_, ?_⟩
  · simp [Work.IntLib.SG.mSt]
  · simp [Work.IntLib.SG.mSt, Ne.symm hdk]
  · intro j hj1 hj2; simp [Work.IntLib.SG.mSt, hj1, hj2]

theorem dropRegionRevEval (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (r : HvdH.Reg)
    (gs below : List HvdH.Glyph) (s : HvdH.State)
    (hT : T ≠ HvdH.Glyph.eos) (hgs : ∀ g ∈ gs, g ≠ T)
    (hstk : s.stk k = gs ++ T :: below) :
    ∃ s' m, HvdH.Eval main (Work.IntLib.SG.rLoop k T none r) s s' m ∧
      m ≤ 7 + gs.length * 5 ∧
      s'.stk k = T :: below ∧
      (∀ j : HvdH.Stk, j ≠ k → s'.stk j = s.stk j) := by
  refine ⟨_, _, Work.IntLib.SG.dLoop_eval main k T r hT gs below s hstk hgs, le_rfl, ?_, ?_⟩
  · simp [Work.IntLib.SG.dSt]
  · intro j hj; simp [Work.IntLib.SG.dSt, hj]

theorem popTopEval (main : HvdH.Cmd) (k : HvdH.Stk) (r : HvdH.Reg) (T : HvdH.Glyph)
    (b : List HvdH.Glyph) (s : HvdH.State) (hstk : s.stk k = T :: b) :
    ∃ s' m, HvdH.Eval main (HvdH.Cmd.pop k r) s s' m ∧ m ≤ 1 ∧ s'.stk k = b ∧
      (∀ j : HvdH.Stk, j ≠ k → s'.stk j = s.stk j) := by
  refine ⟨_, _, HvdH.Eval.pop k r s, le_rfl, ?_, ?_⟩
  · simp only [Function.update_self, hstk, List.tail_cons]
  · intro j hj; exact Function.update_of_ne hj _ _

/-! ## the `sqrtClean` phase -/

theorem sqrtCleanAux (main : HvdH.Cmd) (R : List HvdH.Glyph) (bl : List Bool)
    (bA bB bC bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (h0 : s.stk 0 = R)
    (hA : s.stk Work.IntLib.SG.sA = HvdH.Glyph.mk Work.IntLib.SG.sA :: bA)
    (hB : s.stk Work.IntLib.SG.sB
      = bl.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sB :: bB)
    (hC : s.stk Work.IntLib.SG.sC = HvdH.Glyph.mk Work.IntLib.SG.sC :: bC)
    (hP : s.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP)
    (hQ : s.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ)
    (hR : s.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR)
    (hS : s.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS) :
    ∃ s' m, HvdH.Eval main Work.IntLib.SG.sqrtClean s s' m ∧
      m ≤ 100 + bl.length * 10 ∧
      s'.stk 0 = R ∧
      s'.stk Work.IntLib.SG.sA = bA ∧ s'.stk Work.IntLib.SG.sB = bB ∧
      s'.stk Work.IntLib.SG.sC = bC ∧ s'.stk Work.IntLib.SG.sP = bP ∧
      s'.stk Work.IntLib.SG.sQ = bQ ∧ s'.stk Work.IntLib.SG.sR = bR ∧
      s'.stk Work.IntLib.SG.sS = bS ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ Work.IntLib.SG.sA → k ≠ Work.IntLib.SG.sB →
        k ≠ Work.IntLib.SG.sC → k ≠ Work.IntLib.SG.sP → k ≠ Work.IntLib.SG.sQ →
        k ≠ Work.IntLib.SG.sR → k ≠ Work.IntLib.SG.sS → s'.stk k = s.stk k) := by
  -- ## seven drops
  obtain ⟨s1, m1, e1, hm1, k1, f1⟩ :=
    dropRegionRevEval main Work.IntLib.SG.sA (HvdH.Glyph.mk Work.IntLib.SG.sA)
      Work.IntLib.SG.rgT [] bA s (mk_ne_eos' _) (by simp) (by simpa using hA)
  obtain ⟨s2, m2, e2, hm2, k2, f2⟩ :=
    dropRegionRevEval main Work.IntLib.SG.sB (HvdH.Glyph.mk Work.IntLib.SG.sB)
      Work.IntLib.SG.rgT (bl.map HvdH.Glyph.bit) bB s1 (mk_ne_eos' _)
      (mem_map_bit_ne_mk' bl _) ((f1 Work.IntLib.SG.sB (by decide)).trans hB)
  obtain ⟨s3, m3, e3, hm3, k3, f3⟩ :=
    dropRegionRevEval main Work.IntLib.SG.sC (HvdH.Glyph.mk Work.IntLib.SG.sC)
      Work.IntLib.SG.rgT [] bC s2 (mk_ne_eos' _) (by simp)
      ((f2 Work.IntLib.SG.sC (by decide)).trans
        ((f1 Work.IntLib.SG.sC (by decide)).trans hC))
  obtain ⟨s4, m4, e4, hm4, k4, f4⟩ :=
    dropRegionRevEval main Work.IntLib.SG.sP (HvdH.Glyph.mk Work.IntLib.SG.sP)
      Work.IntLib.SG.rgT [] bP s3 (mk_ne_eos' _) (by simp)
      ((f3 Work.IntLib.SG.sP (by decide)).trans ((f2 Work.IntLib.SG.sP (by decide)).trans
        ((f1 Work.IntLib.SG.sP (by decide)).trans hP)))
  obtain ⟨s5, m5, e5, hm5, k5, f5⟩ :=
    dropRegionRevEval main Work.IntLib.SG.sQ (HvdH.Glyph.mk Work.IntLib.SG.sQ)
      Work.IntLib.SG.rgT [] bQ s4 (mk_ne_eos' _) (by simp)
      ((f4 Work.IntLib.SG.sQ (by decide)).trans ((f3 Work.IntLib.SG.sQ (by decide)).trans
        ((f2 Work.IntLib.SG.sQ (by decide)).trans ((f1 Work.IntLib.SG.sQ (by decide)).trans hQ))))
  obtain ⟨s6, m6, e6, hm6, k6, f6⟩ :=
    dropRegionRevEval main Work.IntLib.SG.sR (HvdH.Glyph.mk Work.IntLib.SG.sR)
      Work.IntLib.SG.rgT [] bR s5 (mk_ne_eos' _) (by simp)
      ((f5 Work.IntLib.SG.sR (by decide)).trans ((f4 Work.IntLib.SG.sR (by decide)).trans
        ((f3 Work.IntLib.SG.sR (by decide)).trans ((f2 Work.IntLib.SG.sR (by decide)).trans
          ((f1 Work.IntLib.SG.sR (by decide)).trans hR)))))
  obtain ⟨s7, m7, e7, hm7, k7, f7⟩ :=
    dropRegionRevEval main Work.IntLib.SG.sS (HvdH.Glyph.mk Work.IntLib.SG.sS)
      Work.IntLib.SG.rgT [] bS s6 (mk_ne_eos' _) (by simp)
      ((f6 Work.IntLib.SG.sS (by decide)).trans ((f5 Work.IntLib.SG.sS (by decide)).trans
        ((f4 Work.IntLib.SG.sS (by decide)).trans ((f3 Work.IntLib.SG.sS (by decide)).trans
          ((f2 Work.IntLib.SG.sS (by decide)).trans ((f1 Work.IntLib.SG.sS (by decide)).trans hS))))))
  -- ## contents of the seven stacks after the drops
  have gA : s7.stk Work.IntLib.SG.sA = HvdH.Glyph.mk Work.IntLib.SG.sA :: bA := by
    rw [f7 Work.IntLib.SG.sA (by decide), f6 Work.IntLib.SG.sA (by decide),
        f5 Work.IntLib.SG.sA (by decide), f4 Work.IntLib.SG.sA (by decide),
        f3 Work.IntLib.SG.sA (by decide), f2 Work.IntLib.SG.sA (by decide)]
    exact k1
  have gB : s7.stk Work.IntLib.SG.sB = HvdH.Glyph.mk Work.IntLib.SG.sB :: bB := by
    rw [f7 Work.IntLib.SG.sB (by decide), f6 Work.IntLib.SG.sB (by decide),
        f5 Work.IntLib.SG.sB (by decide), f4 Work.IntLib.SG.sB (by decide),
        f3 Work.IntLib.SG.sB (by decide)]
    exact k2
  have gC : s7.stk Work.IntLib.SG.sC = HvdH.Glyph.mk Work.IntLib.SG.sC :: bC := by
    rw [f7 Work.IntLib.SG.sC (by decide), f6 Work.IntLib.SG.sC (by decide),
        f5 Work.IntLib.SG.sC (by decide), f4 Work.IntLib.SG.sC (by decide)]
    exact k3
  have gP : s7.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP := by
    rw [f7 Work.IntLib.SG.sP (by decide), f6 Work.IntLib.SG.sP (by decide),
        f5 Work.IntLib.SG.sP (by decide)]
    exact k4
  have gQ : s7.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ := by
    rw [f7 Work.IntLib.SG.sQ (by decide), f6 Work.IntLib.SG.sQ (by decide)]
    exact k5
  have gR : s7.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR := by
    rw [f7 Work.IntLib.SG.sR (by decide)]
    exact k6
  have gS : s7.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS := k7
  -- ## seven pops
  obtain ⟨s8, m8, e8, hm8, k8, f8⟩ :=
    popTopEval main Work.IntLib.SG.sA Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sA) bA s7 gA
  obtain ⟨s9, m9, e9, hm9, k9, f9⟩ :=
    popTopEval main Work.IntLib.SG.sB Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sB) bB s8
      ((f8 Work.IntLib.SG.sB (by decide)).trans gB)
  obtain ⟨s10, m10, e10, hm10, k10, f10⟩ :=
    popTopEval main Work.IntLib.SG.sC Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sC) bC s9
      ((f9 Work.IntLib.SG.sC (by decide)).trans ((f8 Work.IntLib.SG.sC (by decide)).trans gC))
  obtain ⟨s11, m11, e11, hm11, k11, f11⟩ :=
    popTopEval main Work.IntLib.SG.sP Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sP) bP s10
      ((f10 Work.IntLib.SG.sP (by decide)).trans ((f9 Work.IntLib.SG.sP (by decide)).trans
        ((f8 Work.IntLib.SG.sP (by decide)).trans gP)))
  obtain ⟨s12, m12, e12, hm12, k12, f12⟩ :=
    popTopEval main Work.IntLib.SG.sQ Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sQ) bQ s11
      ((f11 Work.IntLib.SG.sQ (by decide)).trans ((f10 Work.IntLib.SG.sQ (by decide)).trans
        ((f9 Work.IntLib.SG.sQ (by decide)).trans ((f8 Work.IntLib.SG.sQ (by decide)).trans gQ))))
  obtain ⟨s13, m13, e13, hm13, k13, f13⟩ :=
    popTopEval main Work.IntLib.SG.sR Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sR) bR s12
      ((f12 Work.IntLib.SG.sR (by decide)).trans ((f11 Work.IntLib.SG.sR (by decide)).trans
        ((f10 Work.IntLib.SG.sR (by decide)).trans ((f9 Work.IntLib.SG.sR (by decide)).trans
          ((f8 Work.IntLib.SG.sR (by decide)).trans gR)))))
  obtain ⟨s14, m14, e14, hm14, k14, f14⟩ :=
    popTopEval main Work.IntLib.SG.sS Work.IntLib.SG.rgT (HvdH.Glyph.mk Work.IntLib.SG.sS) bS s13
      ((f13 Work.IntLib.SG.sS (by decide)).trans ((f12 Work.IntLib.SG.sS (by decide)).trans
        ((f11 Work.IntLib.SG.sS (by decide)).trans ((f10 Work.IntLib.SG.sS (by decide)).trans
          ((f9 Work.IntLib.SG.sS (by decide)).trans ((f8 Work.IntLib.SG.sS (by decide)).trans gS))))))
  -- ## the composite evaluation
  simp only [List.length_nil, List.length_map, Nat.mul_zero, Nat.add_zero] at hm1 hm2 hm3 hm4 hm5 hm6 hm7
  have h1314 := HvdH.Eval.seq e13 e14
  have h1214 := HvdH.Eval.seq e12 h1314
  have h1114 := HvdH.Eval.seq e11 h1214
  have h1014 := HvdH.Eval.seq e10 h1114
  have h914 := HvdH.Eval.seq e9 h1014
  have h814 := HvdH.Eval.seq e8 h914
  have h714 := HvdH.Eval.seq e7 h814
  have h614 := HvdH.Eval.seq e6 h714
  have h514 := HvdH.Eval.seq e5 h614
  have h414 := HvdH.Eval.seq e4 h514
  have h314 := HvdH.Eval.seq e3 h414
  have h214 := HvdH.Eval.seq e2 h314
  have h114 := HvdH.Eval.seq e1 h214
  have hzero : s14.stk 0 = R := by
    rw [f14 0 (by decide), f13 0 (by decide), f12 0 (by decide), f11 0 (by decide),
        f10 0 (by decide), f9 0 (by decide), f8 0 (by decide), f7 0 (by decide),
        f6 0 (by decide), f5 0 (by decide), f4 0 (by decide), f3 0 (by decide),
        f2 0 (by decide), f1 0 (by decide)]
    exact h0
  have hframe : ∀ k : HvdH.Stk, k ≠ 0 → k ≠ Work.IntLib.SG.sA → k ≠ Work.IntLib.SG.sB →
      k ≠ Work.IntLib.SG.sC → k ≠ Work.IntLib.SG.sP → k ≠ Work.IntLib.SG.sQ →
      k ≠ Work.IntLib.SG.sR → k ≠ Work.IntLib.SG.sS → s14.stk k = s.stk k := by
    intro k hk0 hkA hkB hkC hkP hkQ hkR hkS
    rw [f14 k hkS, f13 k hkR, f12 k hkQ, f11 k hkP, f10 k hkC, f9 k hkB, f8 k hkA,
        f7 k hkS, f6 k hkR, f5 k hkQ, f4 k hkP, f3 k hkC, f2 k hkB, f1 k hkA]
  -- ## transport the seven contents past the later pops
  have cA : s14.stk Work.IntLib.SG.sA = bA := by
    rw [f14 Work.IntLib.SG.sA (by decide), f13 Work.IntLib.SG.sA (by decide),
        f12 Work.IntLib.SG.sA (by decide), f11 Work.IntLib.SG.sA (by decide),
        f10 Work.IntLib.SG.sA (by decide), f9 Work.IntLib.SG.sA (by decide)]
    exact k8
  have cB : s14.stk Work.IntLib.SG.sB = bB := by
    rw [f14 Work.IntLib.SG.sB (by decide), f13 Work.IntLib.SG.sB (by decide),
        f12 Work.IntLib.SG.sB (by decide), f11 Work.IntLib.SG.sB (by decide),
        f10 Work.IntLib.SG.sB (by decide)]
    exact k9
  have cC : s14.stk Work.IntLib.SG.sC = bC := by
    rw [f14 Work.IntLib.SG.sC (by decide), f13 Work.IntLib.SG.sC (by decide),
        f12 Work.IntLib.SG.sC (by decide), f11 Work.IntLib.SG.sC (by decide)]
    exact k10
  have cP : s14.stk Work.IntLib.SG.sP = bP := by
    rw [f14 Work.IntLib.SG.sP (by decide), f13 Work.IntLib.SG.sP (by decide),
        f12 Work.IntLib.SG.sP (by decide)]
    exact k11
  have cQ : s14.stk Work.IntLib.SG.sQ = bQ := by
    rw [f14 Work.IntLib.SG.sQ (by decide), f13 Work.IntLib.SG.sQ (by decide)]
    exact k12
  have cR : s14.stk Work.IntLib.SG.sR = bR := by
    rw [f14 Work.IntLib.SG.sR (by decide)]
    exact k13
  exact ⟨s14, m1 + (m2 + (m3 + (m4 + (m5 + (m6 + (m7 + (m8 + (m9 + (m10 + (m11 + (m12 + (m13 + (m14))))))))))))),
    h114, by omega, hzero, cA, cB, cC, cP, cQ, cR, k14, hframe⟩

/-! ## `sqrtFinish` -/

/-- `sqrtFinish` on a state whose stack `sC` carries the root bits `rl` (least significant first)
above its marker and whose `sP` is empty: emits the root as a value on top of stack 0. -/
theorem sqrtFinishAux (main : HvdH.Cmd) (rl : List Bool) (R : List HvdH.Glyph)
    (bC bP : List HvdH.Glyph) (s : HvdH.State)
    (h0 : s.stk 0 = R)
    (hC : s.stk Work.IntLib.SG.sC
      = rl.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sC :: bC)
    (hP : s.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP) :
    ∃ s' m, HvdH.Eval main Work.IntLib.SG.sqrtFinish s s' m ∧
      m ≤ 17 * rl.length + 37 ∧
      s'.stk 0 = (HvdH.Val.int ((Work.IntLib.ofBits rl : ℕ) : ℤ)).enc ++ R ∧
      s'.stk Work.IntLib.SG.sC = HvdH.Glyph.mk Work.IntLib.SG.sC :: bC ∧
      s'.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.SG.sC → j ≠ Work.IntLib.SG.sP →
        s'.stk j = s.stk j) := by
  -- `sqrtFinish` = move `sC -> sP`, then the tail proved in `sqrtFinishTail`
  obtain ⟨s1, m1, he1, hb1, hd1, hk1, hfr1⟩ :=
    moveRegionRevEval main Work.IntLib.SG.sC Work.IntLib.SG.sP (HvdH.Glyph.mk Work.IntLib.SG.sC)
      Work.IntLib.SG.rgT (rl.map HvdH.Glyph.bit) bC s (by decide) (by decide)
      (by intro g hg
          obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
          exact fun h => by cases h) hC
  have h01 : s1.stk 0 = R := (hfr1 0 (by decide) (by decide)).trans h0
  have hP1 : s1.stk Work.IntLib.SG.sP
      = (rl.map HvdH.Glyph.bit).reverse ++ HvdH.Glyph.mk Work.IntLib.SG.sP :: bP := by
    rw [hd1, hP]
  obtain ⟨s2, m2, he2, hb2, h02, hP2, hfr2⟩ := sqrtFinishTail main rl R bP s1 h01 hP1
  rw [List.length_map] at hb1
  refine ⟨s2, m1 + m2, HvdH.Eval.seq he1 he2, by omega, h02, ?_, hP2, ?_⟩
  · rw [hfr2 Work.IntLib.SG.sC (by decide) (by decide), hk1]
  · intro j hj0 hjC hjP
    exact (hfr2 j hj0 hjP).trans (hfr1 j hjC hjP)

/-! ## The requested statement -/

/-- `sqrtFinish ;; sqrtClean` emits the root `ofBits rl` on stack 0 and restores the seven scratch
stacks to the lists below their markers. -/
theorem sqrtFinishEval (main : HvdH.Cmd) (rl : List Bool) (R : List HvdH.Glyph)
    (bA bB bC bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (h0 : s.stk 0 = R)
    (hA : s.stk Work.IntLib.SG.sA = HvdH.Glyph.mk Work.IntLib.SG.sA :: bA)
    (hB : s.stk Work.IntLib.SG.sB = HvdH.Glyph.mk Work.IntLib.SG.sB :: bB)
    (hC : s.stk Work.IntLib.SG.sC = rl.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sC :: bC)
    (hP : s.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP)
    (hQ : s.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ)
    (hR : s.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR)
    (hS : s.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS) :
    ∃ s' m, HvdH.Eval main
        (HvdH.Cmd.seq Work.IntLib.SG.sqrtFinish Work.IntLib.SG.sqrtClean) s s' m ∧
      m ≤ 100 + (rl.length + 1) * 100 ∧
      s'.stk 0 = (HvdH.Val.int ((Work.IntLib.ofBits rl : ℕ) : ℤ)).enc ++ R ∧
      s'.stk Work.IntLib.SG.sA = bA ∧ s'.stk Work.IntLib.SG.sB = bB ∧
      s'.stk Work.IntLib.SG.sC = bC ∧ s'.stk Work.IntLib.SG.sP = bP ∧
      s'.stk Work.IntLib.SG.sQ = bQ ∧ s'.stk Work.IntLib.SG.sR = bR ∧
      s'.stk Work.IntLib.SG.sS = bS ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ Work.IntLib.SG.sA → k ≠ Work.IntLib.SG.sB →
        k ≠ Work.IntLib.SG.sC → k ≠ Work.IntLib.SG.sP → k ≠ Work.IntLib.SG.sQ →
        k ≠ Work.IntLib.SG.sR → k ≠ Work.IntLib.SG.sS → s'.stk k = s.stk k) := by
  obtain ⟨s1, m1, he1, hb1, h01, hC1, hP1, hfr1⟩ := sqrtFinishAux main rl R bC bP s h0 hC hP
  have hA1 : s1.stk Work.IntLib.SG.sA = HvdH.Glyph.mk Work.IntLib.SG.sA :: bA := by
    rw [hfr1 Work.IntLib.SG.sA (by decide) (by decide) (by decide)]; exact hA
  have hB1 : s1.stk Work.IntLib.SG.sB = HvdH.Glyph.mk Work.IntLib.SG.sB :: bB := by
    rw [hfr1 Work.IntLib.SG.sB (by decide) (by decide) (by decide)]; exact hB
  have hQ1 : s1.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ := by
    rw [hfr1 Work.IntLib.SG.sQ (by decide) (by decide) (by decide)]; exact hQ
  have hR1 : s1.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR := by
    rw [hfr1 Work.IntLib.SG.sR (by decide) (by decide) (by decide)]; exact hR
  have hS1 : s1.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS := by
    rw [hfr1 Work.IntLib.SG.sS (by decide) (by decide) (by decide)]; exact hS
  obtain ⟨s2, m2, he2, hb2, h02, hA2, hB2, hC2, hP2, hQ2, hR2, hS2, hfr2⟩ :=
    sqrtCleanAux main ((HvdH.Val.int ((Work.IntLib.ofBits rl : ℕ) : ℤ)).enc ++ R)
      ([] : List Bool) bA bB bC bP bQ bR bS s1 h01 hA1 hB1 hC1 hP1 hQ1 hR1 hS1
  rw [List.length_nil, Nat.zero_mul, Nat.add_zero] at hb2
  refine ⟨s2, m1 + m2, HvdH.Eval.seq he1 he2, by omega, h02, hA2, hB2, hC2, hP2, hQ2,
    hR2, hS2, ?_⟩
  intro k hk0 hkA hkB hkC hkP hkQ hkR hkS
  exact (hfr2 k hk0 hkA hkB hkC hkP hkQ hkR hkS).trans (hfr1 k hk0 hkC hkP)

/-! ## The variant needed at the call site: a non-empty remainder region on `sB` -/

/-- Same as `sqrtFinishEval` but the region of stack `sB` above its marker is an arbitrary bit list
`bl` instead of being empty; this is the hypothesis available after the restoring loop
(`sqrtInvDefs.Inv.hB`), where `bl` is the leftover remainder `S - r ^ 2`.  The cost bound grows by
`100 * bl.length`. -/
theorem sqrtFinishEvalGen (main : HvdH.Cmd) (rl bl : List Bool) (R : List HvdH.Glyph)
    (bA bB bC bP bQ bR bS : List HvdH.Glyph) (s : HvdH.State)
    (h0 : s.stk 0 = R)
    (hA : s.stk Work.IntLib.SG.sA = HvdH.Glyph.mk Work.IntLib.SG.sA :: bA)
    (hB : s.stk Work.IntLib.SG.sB
      = bl.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sB :: bB)
    (hC : s.stk Work.IntLib.SG.sC = rl.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sC :: bC)
    (hP : s.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP)
    (hQ : s.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ)
    (hR : s.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR)
    (hS : s.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS) :
    ∃ s' m, HvdH.Eval main
        (HvdH.Cmd.seq Work.IntLib.SG.sqrtFinish Work.IntLib.SG.sqrtClean) s s' m ∧
      m ≤ 100 + (rl.length + bl.length + 1) * 100 ∧
      s'.stk 0 = (HvdH.Val.int ((Work.IntLib.ofBits rl : ℕ) : ℤ)).enc ++ R ∧
      s'.stk Work.IntLib.SG.sA = bA ∧ s'.stk Work.IntLib.SG.sB = bB ∧
      s'.stk Work.IntLib.SG.sC = bC ∧ s'.stk Work.IntLib.SG.sP = bP ∧
      s'.stk Work.IntLib.SG.sQ = bQ ∧ s'.stk Work.IntLib.SG.sR = bR ∧
      s'.stk Work.IntLib.SG.sS = bS ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ Work.IntLib.SG.sA → k ≠ Work.IntLib.SG.sB →
        k ≠ Work.IntLib.SG.sC → k ≠ Work.IntLib.SG.sP → k ≠ Work.IntLib.SG.sQ →
        k ≠ Work.IntLib.SG.sR → k ≠ Work.IntLib.SG.sS → s'.stk k = s.stk k) := by
  obtain ⟨s1, m1, he1, hb1, h01, hC1, hP1, hfr1⟩ := sqrtFinishAux main rl R bC bP s h0 hC hP
  have hA1 : s1.stk Work.IntLib.SG.sA = HvdH.Glyph.mk Work.IntLib.SG.sA :: bA := by
    rw [hfr1 Work.IntLib.SG.sA (by decide) (by decide) (by decide)]; exact hA
  have hQ1 : s1.stk Work.IntLib.SG.sQ = HvdH.Glyph.mk Work.IntLib.SG.sQ :: bQ := by
    rw [hfr1 Work.IntLib.SG.sQ (by decide) (by decide) (by decide)]; exact hQ
  have hR1 : s1.stk Work.IntLib.SG.sR = HvdH.Glyph.mk Work.IntLib.SG.sR :: bR := by
    rw [hfr1 Work.IntLib.SG.sR (by decide) (by decide) (by decide)]; exact hR
  have hS1 : s1.stk Work.IntLib.SG.sS = HvdH.Glyph.mk Work.IntLib.SG.sS :: bS := by
    rw [hfr1 Work.IntLib.SG.sS (by decide) (by decide) (by decide)]; exact hS
  have hB1 : s1.stk Work.IntLib.SG.sB
      = bl.map HvdH.Glyph.bit ++ HvdH.Glyph.mk Work.IntLib.SG.sB :: bB := by
    rw [hfr1 Work.IntLib.SG.sB (by decide) (by decide) (by decide)]
    exact hB
  obtain ⟨s2, m2, he2, hb2, h02, hA2, hB2, hC2, hP2, hQ2, hR2, hS2, hfr2⟩ :=
    sqrtCleanAux main ((HvdH.Val.int ((Work.IntLib.ofBits rl : ℕ) : ℤ)).enc ++ R)
      bl bA bB bC bP bQ bR bS s1 h01 hA1 hB1 hC1 hP1 hQ1 hR1 hS1
  refine ⟨s2, m1 + m2, HvdH.Eval.seq he1 he2, by omega, h02, hA2, hB2, hC2, hP2, hQ2,
    hR2, hS2, ?_⟩
  intro k hk0 hkA hkB hkC hkP hkQ hkR hkS
  exact (hfr2 k hk0 hkA hkB hkC hkP hkQ hkR hkS).trans (hfr1 k hk0 hkC hkP)


end Work.IntLib.SqrtGcd
