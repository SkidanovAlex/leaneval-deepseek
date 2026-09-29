import Mathlib
import Submission.Work.IntLib.SqrtGcd.gcdFinishEval
import Submission.Work.IntLib.SqrtGcd.gcdScaleEval

/-!
# Junk-tolerant versions of the gcd helpers

The `gcdRun ; gcdFinish ; gcdClean` word of `SqrtGcd/gcdFinishEval.lean` is specified there with
*empty* stacks below the frame markers.  The present file sets up the five small region moves that
the general specification needs, with arbitrary junk (`bU`, `bV`, `bG`, `bP`, `bR`, `b`) below the
markers: the region moves `moveSameVUR`, `stripZerosRegion`, `finishMove`, `finishEmit` and the
scaling `gcdScaleEval`.

Each proof is the proof of the corresponding lemma of `gcdFinishEval.lean` / `gcdScaleEval.lean`
with the `below` arguments of `SG.mLoop_eval` / `eval_stripZeros` / `gcdScaleLoop` instantiated by
the junk lists.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH
open Work.IntLib.SG

/-- `moveSame sV sU sR rgT` with junk `bV` below the marker of `sV` and junk `bR` below that of
`sR`: the region of `sV` is appended to whatever `sU` holds, and both source stacks keep their
markers with their junk. -/
theorem moveSameVURGen (main : HvdH.Cmd) (V : List Bool) (bV bR : List HvdH.Glyph)
    (s : HvdH.State)
    (hV : s.stk sV = V.map Glyph.bit ++ Glyph.mk sV :: bV)
    (hR : s.stk sR = Glyph.mk sR :: bR) :
    ∃ s' m, HvdH.Eval main (moveSame sV sU sR rgT) s s' m ∧ m ≤ 20 * (V.length + 1) ∧
      s'.stk sU = V.map Glyph.bit ++ s.stk sU ∧
      s'.stk sV = Glyph.mk sV :: bV ∧
      s'.stk sR = Glyph.mk sR :: bR ∧
      (∀ j : Stk, j ≠ sV → j ≠ sU → j ≠ sR → s'.stk j = s.stk j) := by
  have h1 : HvdH.Eval main (SG.rLoop sV (Glyph.mk sV) (some sR) rgT) s
      (mSt sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) bV s) (7 + (V.map Glyph.bit).length * 5) :=
    SG.mLoop_eval main sV (Glyph.mk sV) sR rgT (gMk_ne_eos sV) (by decide) (V.map Glyph.bit) bV s
      hV (mem_map_bit_ne_mk V sV)
  have hR1 : (mSt sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) bV s).stk sR
      = (V.reverse).map Glyph.bit ++ Glyph.mk sR :: bR := by
    rw [mStD, hR, List.map_reverse]
  have h2 : HvdH.Eval main (SG.rLoop sR (Glyph.mk sR) (some sU) rgT)
      (mSt sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) bV s)
      (mSt sR (Glyph.mk sR) sU rgT ((V.reverse).map Glyph.bit) bR
        (mSt sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) bV s))
      (7 + ((V.reverse).map Glyph.bit).length * 5) :=
    SG.mLoop_eval main sR (Glyph.mk sR) sU rgT (gMk_ne_eos sR) (by decide)
      ((V.reverse).map Glyph.bit) bR _ hR1 (mem_map_bit_ne_mk V.reverse sR)
  refine ⟨_, (7 + (V.map Glyph.bit).length * 5) + (7 + ((V.reverse).map Glyph.bit).length * 5),
    Eval.seq h1 h2, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_reverse]; omega
  · rw [mStD, mStO sV (Glyph.mk sV) sR sU rgT (V.map Glyph.bit) bV s (by decide) (by decide),
      List.map_reverse, List.reverse_reverse]
  · rw [mStO sR (Glyph.mk sR) sU sV rgT ((V.reverse).map Glyph.bit) bR _ (by decide) (by decide),
      mStK sV (Glyph.mk sV) sR rgT (V.map Glyph.bit) bV s (by decide)]
  · rw [mStK sR (Glyph.mk sR) sU rgT ((V.reverse).map Glyph.bit) bR _ (by decide)]
  · intro j hjV hjU hjR
    rw [mStO sR (Glyph.mk sR) sU j rgT ((V.reverse).map Glyph.bit) bR _ hjR hjU]
    exact mStO sV (Glyph.mk sV) sR j rgT (V.map Glyph.bit) bV s hjV hjR

/-- `stripZerosRegion` with junk `b` below the marker. -/
theorem stripZerosRegionGen (main : HvdH.Cmd) (i : Stk) (L : List Bool) (b : List Glyph)
    (s : HvdH.State) (h : s.stk i = L.map Glyph.bit ++ Glyph.mk i :: b) :
    ∃ s' m, HvdH.Eval main (SG.stripZeros i rgT) s s' m ∧ m ≤ 2 * (L.length + 1) + 6 ∧
      s'.stk i = (dropLead L).map Glyph.bit ++ Glyph.mk i :: b ∧
      (∀ j : Stk, j ≠ i → s'.stk j = s.stk j) := by
  obtain ⟨s', n, hev, hn, hstk, hfr⟩ :=
    Work.IntLib.eval_stripZeros main i (Glyph.mk i) rgT L b s (gMk_ne_eos i)
      (fun b' => gBit_ne_mk b' i) h
  refine ⟨s', n, hev, hn, ?_, hfr⟩
  rw [hstk, Work.IntLib.dropWhile_map_bit_rev L]
  rfl

/-- `gcdScaleEval` with junk `bG` below the marker of the counter `sG`. -/
theorem gcdScaleEvalGen (main : HvdH.Cmd) (k : ℕ) (us : List Bool) (bU bG : List HvdH.Glyph)
    (s : HvdH.State)
    (hU : s.stk sU = us.map HvdH.Glyph.bit ++ HvdH.Glyph.mk sU :: bU)
    (hG : s.stk sG = List.replicate k gTick ++ HvdH.Glyph.mk sG :: bG) :
    ∃ s' m, HvdH.Eval main gcdScale s s' m ∧ m ≤ 100 * (k + 1) ∧
      s'.stk sU = (List.replicate k false ++ us).map HvdH.Glyph.bit
        ++ HvdH.Glyph.mk sU :: bU ∧
      s'.stk sG = HvdH.Glyph.mk sG :: bG ∧
      (∀ j : HvdH.Stk, j ≠ sU → j ≠ sG → s'.stk j = s.stk j) := by
  let s0 : State := ⟨Function.update s.reg rgF gGo, s.stk⟩
  have e0 : Work.Layout.Ev main (.set rgF gGo) s s0 1 := by
    have h := Work.Layout.ev_set main rgF gGo s
    simpa [s0] using h
  have hF0 : s0.reg rgF = gGo := by simp [s0]
  obtain ⟨s', m', hm', hle', hsU', hsG', _⟩ :=
    gcdScaleLoop main k us bU bG s0 (by simpa [s0] using hU) (by simpa [s0] using hG) hF0
  obtain ⟨n, hn, hnle⟩ := Work.Layout.Ev.seq e0 ⟨m', hm', le_rfl⟩
  have hsub : Work.Layout.cmdTouches gcdScale ⊆ ({sU, sG} : Finset Stk) := by decide
  refine ⟨s', n, hn, by omega, hsU', hsG', ?_⟩
  intro j hjU hjG
  refine Work.Layout.Eval.stk_frame hn ?_
  intro hmem
  exact (by simp [Finset.mem_insert, Finset.mem_singleton, hjU, hjG] : j ∉ ({sU, sG} : Finset Stk))
    (hsub hmem)

/-- `finishMove` with junk `bU` below the marker of `sU` and junk `bP` below that of `sP`. -/
theorem finishMoveGen (main : HvdH.Cmd) (ul : List Bool) (bU bP : List Glyph) (s : State)
    (hU : s.stk sU = ul.map Glyph.bit ++ Glyph.mk sU :: bU)
    (hP : s.stk sP = Glyph.mk sP :: bP) :
    ∃ s' m, HvdH.Eval main (SG.rLoop sU (Glyph.mk sU) (some sP) rgT) s s' m ∧
      m = 7 + (ul.map Glyph.bit).length * 5 ∧
      s'.stk sP = (ul.reverse).map Glyph.bit ++ Glyph.mk sP :: bP ∧
      s'.stk sU = Glyph.mk sU :: bU ∧
      (∀ j : Stk, j ≠ sU → j ≠ sP → s'.stk j = s.stk j) := by
  refine ⟨mSt sU (Glyph.mk sU) sP rgT (ul.map Glyph.bit) bU s,
    7 + (ul.map Glyph.bit).length * 5,
    SG.mLoop_eval main sU (Glyph.mk sU) sP rgT (gMk_ne_eos sU) (by decide) (ul.map Glyph.bit) bU s
      hU (mem_map_bit_ne_mk ul sU), rfl, ?_, ?_, ?_⟩
  · rw [mStD, hP, List.map_reverse]
  · rw [mStK sU (Glyph.mk sU) sP rgT (ul.map Glyph.bit) bU s (by decide)]
  · intro j hjU hjP
    exact mStO sU (Glyph.mk sU) sP j rgT (ul.map Glyph.bit) bU s hjU hjP

/-- `finishEmit` with junk `bP` below the marker of `sP`. -/
theorem finishEmitGen (main : HvdH.Cmd) (L : List Bool) (S0 : List Glyph) (bP : List Glyph)
    (s : State) (hP : s.stk sP = L.map Glyph.bit ++ Glyph.mk sP :: bP) (h0 : s.stk 0 = S0) :
    ∃ s' m, HvdH.Eval main (SG.rLoop sP (Glyph.mk sP) (some 0) rgT) s s' m ∧
      m = 7 + (L.map Glyph.bit).length * 5 ∧
      s'.stk 0 = (L.map Glyph.bit).reverse ++ S0 ∧
      s'.stk sP = Glyph.mk sP :: bP ∧
      (∀ j : Stk, j ≠ sP → j ≠ 0 → s'.stk j = s.stk j) := by
  refine ⟨mSt sP (Glyph.mk sP) 0 rgT (L.map Glyph.bit) bP s, 7 + (L.map Glyph.bit).length * 5,
    SG.mLoop_eval main sP (Glyph.mk sP) 0 rgT (gMk_ne_eos sP) (by decide) (L.map Glyph.bit) bP s
      hP (mem_map_bit_ne_mk L sP), rfl, ?_, ?_, ?_⟩
  · rw [mStD, h0]
  · rw [mStK sP (Glyph.mk sP) 0 rgT (L.map Glyph.bit) bP s (by decide)]
  · intro j hjP hj0
    exact mStO sP (Glyph.mk sP) 0 j rgT (L.map Glyph.bit) bP s hjP hj0

end Work.IntLib.SqrtGcd
