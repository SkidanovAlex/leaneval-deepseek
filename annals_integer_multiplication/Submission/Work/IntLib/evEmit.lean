import Mathlib
import Submission.Work.IntLib.evEmitDefs
import Submission.Work.IntLib.evEmit_vals
import Submission.Work.IntLib.evEmit_fin

/-!
# `IntLib` / `evEmit`: emitting `V = ofBits LO + 2^(LO.length) * ofBits W` on stack 0

Assembly of `Work.IntLib.evEmit` from the three phases of `evEmitProg`
(`Submission/Work/IntLib/evEmitDefs.lean`):

* `evEmit_clean` clears the junk regions and the frame markers of the eleven stacks of `evL1`;
* `evEmit_vals` runs `evValProg`, leaving `(bits of V reversed) ++ pos` above the marker of
  `evS2` and restoring `aW`, `aO`, `evS1`;
* `evEmit_fin` drains `evS2` onto stack 0.

The stacks not touched by the value phase are handled by the frame lemma `Layout.Ev.frame`
(with `evL1_not_mem_touches`), the remaining four by the frame facts of the individual phases.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

theorem evEmit :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph) (W LO : List Bool) (V : ℕ)
      (Vr Rcb Rcw : List HvdH.Glyph) (Y : HvdH.Stk → List HvdH.Glyph),
      X Work.IntLib.aW = W.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.aW :: Y Work.IntLib.aW →
      X Work.IntLib.aO = LO.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.aO :: Y Work.IntLib.aO →
      X Work.IntLib.aV = Vr ++ Work.IntLib.Shift.gmk Work.IntLib.aV :: Y Work.IntLib.aV →
      X Work.IntLib.aCB = Rcb ++ Work.IntLib.Shift.gmk Work.IntLib.aCB :: Y Work.IntLib.aCB →
      X Work.IntLib.aCW = Rcw ++ Work.IntLib.Shift.gmk Work.IntLib.aCW :: Y Work.IntLib.aCW →
      (∀ h ∈ Vr, h ≠ Work.IntLib.Shift.gmk Work.IntLib.aV) →
      (∀ h ∈ Rcb, h ≠ Work.IntLib.Shift.gmk Work.IntLib.aCB) →
      (∀ h ∈ Rcw, h ≠ Work.IntLib.Shift.gmk Work.IntLib.aCW) →
      X 0 = Y 0 →
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ Work.IntLib.aW → k ≠ Work.IntLib.aO → k ≠ Work.IntLib.aV →
        k ≠ Work.IntLib.aCB → k ≠ Work.IntLib.aCW → X k = Work.IntLib.Shift.gmk k :: Y k) →
      Work.IntLib.ofBits LO + 2 ^ LO.length * Work.IntLib.ofBits W = V →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧
        n ≤ K * (LO.length + W.length + Vr.length + Rcb.length + Rcw.length + 24) ∧
        s'.stk 0 = HvdH.Val.enc (.int (V : ℤ)) ++ Y 0 ∧
        (∀ j : HvdH.Stk, j ≠ 0 → s'.stk j = Y j) := by
  refine ⟨evEmitProg, 20, ?_⟩
  intro main g X W LO V Vr Rcb Rcw Y hW hO hV hCB hCW hVr hRcb hRcw h0 hOther hVal
  -- phase 1: clearing the junk regions and the markers of the eleven stacks of `evL1`
  obtain ⟨s1, n1, hev1, hn1, hclear, hkept⟩ :=
    evEmit_clean main g X Vr Rcb Rcw Y hVr hRcb hRcw hV hCB hCW hOther
  -- phase 2: push `iend` on stack 0
  have hs1_0 : s1.stk 0 = Y 0 := by rw [hkept 0 (by decide), h0]
  obtain ⟨s2, n2, hev2, hn2, hs2_0, hs2_oth⟩ := ev_pushConst main 0 Glyph.iend evR s1
  have hs2_0' : s2.stk 0 = Glyph.iend :: Y 0 := by rw [hs2_0, hs1_0]
  have hs2_aW : s2.stk aW = W.map Glyph.bit ++ Shift.gmk aW :: Y aW := by
    rw [hs2_oth aW (by decide), hkept aW (by decide)]
    exact hW
  have hs2_aO : s2.stk aO = LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Y aO := by
    rw [hs2_oth aO (by decide), hkept aO (by decide)]
    exact hO
  have hs2_S1 : s2.stk evS1 = Shift.gmk evS1 :: Y evS1 := by
    rw [hs2_oth evS1 (by decide), hkept evS1 (by decide)]
    exact hOther evS1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs2_S2 : s2.stk evS2 = Shift.gmk evS2 :: Y evS2 := by
    rw [hs2_oth evS2 (by decide), hkept evS2 (by decide)]
    exact hOther evS2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- phase 3: the value
  obtain ⟨s3, n3, hev3, hn3, hs3_aO, hs3_aW, hs3_S1, hs3_S2, hs3_oth⟩ :=
    evEmit_vals main s2.reg s2.stk W LO V Y hs2_aW hs2_aO hs2_S1 hs2_S2 hVal
  have hs3_0 : s3.stk 0 = Glyph.iend :: Y 0 := by
    rw [hs3_oth 0 (by decide) (by decide) (by decide) (by decide)]
    exact hs2_0'
  -- phase 4: drain `evS2` onto stack 0
  obtain ⟨s4, n4, hev4, hn4, hs4_0, hs4_S2, hs4_oth⟩ :=
    evEmit_fin main s3.reg s3.stk V Y hs3_0 hs3_S2
  have hValEv : Work.Layout.Ev main evValProg s2 s3 n3 := hev3
  have hFinEv : Work.Layout.Ev main (drainUntil evS2 0 (Shift.gmk evS2) evR) s3 s4 n4 := hev4
  have hrest : Work.Layout.Ev main
      (Work.Layout.seqs [pushConst 0 Glyph.iend evR, evValProg,
        drainUntil evS2 0 (Shift.gmk evS2) evR]) s1 s4 (n2 + (n3 + n4)) :=
    Work.Layout.Ev.seqs_cons hev2 (Work.Layout.Ev.seqs_cons hValEv hFinEv)
  have hAll : Work.Layout.Ev main evEmitProg ⟨g, X⟩ s4 (n1 + (n2 + (n3 + n4))) := by
    rw [evEmitProg]
    exact Work.Layout.Ev.seqs_cons hev1 hrest
  refine ⟨s4, n1 + (n2 + (n3 + n4)), hAll, ?_, hs4_0, ?_⟩
  · -- cost
    have hVeq : V = Work.IntLib.ofBits (LO ++ W) := by
      rw [Work.IntLib.ofBits_append]
      exact hVal.symm
    have hVlt : V < 2 ^ (LO.length + W.length) := by
      rw [hVeq]
      have h := Work.IntLib.ofBits_lt_two_pow (LO ++ W)
      rwa [List.length_append] at h
    have hVsz : V.size ≤ LO.length + W.length := Nat.size_le.mpr hVlt
    omega
  · -- all the other stacks are restored
    intro j hj
    by_cases hjL : j ∈ evL1
    · have hfr : s4.stk j = s1.stk j :=
        Work.Layout.Ev.frame hrest (le_rfl) (evL1_not_mem_touches j hjL)
      exact hfr.trans (hclear j hjL)
    · have hj4 : j = aW ∨ j = aO ∨ j = evS1 ∨ j = evS2 := by
        revert hj hjL
        fin_cases j <;> decide
      rcases hj4 with h | h | h | h
      · rw [h]; exact (hs4_oth aW (by decide) (by decide)).trans hs3_aW
      · rw [h]; exact (hs4_oth aO (by decide) (by decide)).trans hs3_aO
      · rw [h]; exact (hs4_oth evS1 (by decide) (by decide)).trans hs3_S1
      · rw [h]; exact hs4_S2

end Work.IntLib
