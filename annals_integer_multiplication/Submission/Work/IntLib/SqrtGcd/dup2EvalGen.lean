import Mathlib
import Submission.Work.IntLib.SqrtGcd.Basic
import Submission.Work.IntLib.SqrtGcd.Dup

/-!
# `dup2EvalGen`: `dup2` with arbitrary junk below its markers

`SG.dup2 src dst t1 t2 r` copies the bit region above the marker `Glyph.mk src` of `src` onto `dst`,
keeping `src` and restoring the scratch stacks `t1`, `t2`.  The program only ever touches the
glyphs *above* the markers of `src`, `dst`, `t1`, `t2`; this file proves the specification with
arbitrary junk (`below`, `bD`, `b1`, `b2`) below those markers.  The special case with empty junk
is the companion result `dup2Eval`.

The proof is raw `Eval` bookkeeping:

* `Dup2Gen.c2LoopEval` : one pass of the two-destination copy loop `cLoop2` (cost `7 + 6·|gs|`),
* four `SG.mLoop_eval` moves `t1 → src → ... → dst` (cost `7 + 5·|gs|` each),
* the final state is computed by case analysis on the four stacks that are touched.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG
namespace Dup2Gen

open HvdH Work.Layout

/-! ## glyphs -/

theorem mk_ne_eos (k : Stk) : Glyph.mk k ≠ Glyph.eos := fun h => by cases h

theorem bit_ne_mk (b : Bool) (k : Stk) : Glyph.bit b ≠ Glyph.mk k := fun h => by cases h

/-! ## the components of `c2St`, `mSt`, `dupSt` -/

theorem c2St_stk_k (k : Stk) (T : Glyph) (d1 d2 : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (h1 : k ≠ d1) (h2 : k ≠ d2) :
    (c2St k T d1 d2 r gs below s).stk k = T :: below := by
  simp [c2St, h1, h2]

theorem c2St_stk_d1 (k : Stk) (T : Glyph) (d1 d2 : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (h : d1 ≠ d2) :
    (c2St k T d1 d2 r gs below s).stk d1 = gs.reverse ++ s.stk d1 := by
  simp [c2St, h]

theorem c2St_stk_d2 (k : Stk) (T : Glyph) (d1 d2 : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) : (c2St k T d1 d2 r gs below s).stk d2 = gs.reverse ++ s.stk d2 := by
  simp [c2St]

theorem c2St_stk_other (k : Stk) (T : Glyph) (d1 d2 j : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (h1 : j ≠ k) (h2 : j ≠ d1) (h3 : j ≠ d2) :
    (c2St k T d1 d2 r gs below s).stk j = s.stk j := by
  simp [c2St, h1, h2, h3]

theorem c2St_reg (k : Stk) (T : Glyph) (d1 d2 : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) : (c2St k T d1 d2 r gs below s).reg = Function.update s.reg r T := rfl

theorem mSt_stk_k (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (gs below : List Glyph) (s : State)
    (h : k ≠ d) : (mSt k T d r gs below s).stk k = T :: below := by
  simp [mSt, h]

theorem mSt_stk_d (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (gs below : List Glyph) (s : State) :
    (mSt k T d r gs below s).stk d = gs.reverse ++ s.stk d := by
  simp [mSt]

theorem mSt_stk_other (k : Stk) (T : Glyph) (d j : Stk) (r : Reg) (gs below : List Glyph)
    (s : State) (h1 : j ≠ k) (h2 : j ≠ d) :
    (mSt k T d r gs below s).stk j = s.stk j := by
  simp [mSt, h1, h2]

theorem dupSt_stk_dst (src dst t1 t2 : Stk) (r : Reg) (gs : List Bool) (s : State) :
    (dupSt src dst t1 t2 r gs s).stk dst = gs.map Glyph.bit ++ s.stk dst := by
  simp [dupSt]

theorem dupSt_stk_other (src dst t1 t2 j : Stk) (r : Reg) (gs : List Bool) (s : State)
    (h : j ≠ dst) : (dupSt src dst t1 t2 r gs s).stk j = s.stk j := by
  simp [dupSt, h]

/-! ## the two-destination copy loop `cLoop2` -/

theorem c2LoopAux (main : Cmd) (k : Stk) (T : Glyph) (d1 d2 : Stk) (r : Reg)
    (hTe : T ≠ Glyph.eos) (hd1k : d1 ≠ k) (hd2k : d2 ≠ k) (hd12 : d1 ≠ d2) :
    ∀ (gs : List Glyph) (below : List Glyph) (s : State), s.stk k = gs ++ T :: below →
      (∀ g ∈ gs, g ≠ T) → s.reg r = Glyph.eos →
      Eval main (.loop r Glyph.eos (cBody2 k T d1 d2 r)) s (c2St k T d1 d2 r gs below s)
        (6 + gs.length * 6) := by
  intro gs
  induction gs with
  | nil =>
      intro below s hstk _ hr
      let a1 : State := ⟨Function.update s.reg r T, Function.update s.stk k below⟩
      let a2 : State := ⟨a1.reg, Function.update a1.stk k (T :: below)⟩
      let a3 : State := ⟨Function.update a2.reg r T, a2.stk⟩
      have ha1k : a1.stk k = below := by simp [a1]
      have e1 : Eval main (.pop k r) s a1 1 := by
        have h := Eval.pop (main := main) k r s
        rw [hstk] at h
        simpa [a1, List.headD_cons, List.tail_cons] using h
      have hr1 : a1.reg r = T := by simp [a1]
      have e2 : Eval main (.push k r) a1 a2 1 := by
        have h := Eval.push (main := main) k r a1
        simpa [a2, State.tPush, hr1, ha1k] using h
      have e3 : Eval main (.set r T) a2 a3 1 := by
        have h := Eval.set (main := main) r T a2
        simpa [a3] using h
      have eite : Eval main (.ite r T (.seq (.push k r) (.set r T))
          (.seq (.push d1 r) (.seq (.push d2 r) (.set r Glyph.eos)))) a1 a3 3 :=
        Eval.iteT hr1 (Eval.seq e2 e3)
      have ebody : Eval main (cBody2 k T d1 d2 r) s a3 4 := Eval.seq e1 eite
      have hr3 : a3.reg r ≠ Glyph.eos := by
        have h : a3.reg r = T := by simp [a3, a2, a1]
        rw [h]; exact hTe
      have eloop : Eval main (.loop r Glyph.eos (cBody2 k T d1 d2 r)) a3 a3 1 := Eval.loopF hr3
      have hmain : Eval main (.loop r Glyph.eos (cBody2 k T d1 d2 r)) s a3 6 :=
        Eval.loopT hr ebody eloop
      have hstate : a3 = c2St k T d1 d2 r [] below s := by
        apply State.ext'
        · intro q
          simp only [c2St, a3, a2, a1, Function.update_apply]
          by_cases hq : q = r <;> simp [hq]
        · intro q
          simp only [c2St, a3, a2, a1, Function.update_apply]
          by_cases hqk : q = k
          · subst hqk; simp [Ne.symm hd1k, Ne.symm hd2k]
          · by_cases hqd1 : q = d1
            · subst hqd1; simp [hqk, hd12]
            · by_cases hqd2 : q = d2
              · subst hqd2; simp [hqk, hqd1]
              · simp [hqk, hqd1, hqd2]
      rw [hstate] at hmain
      have hc : 6 + ([] : List Glyph).length * 6 = 6 := by simp
      rw [hc]
      exact hmain
  | cons g gs' ih =>
      intro below s hstk hT hr
      have hgT : g ≠ T := hT g (by simp)
      have hgs'T : ∀ g' ∈ gs', g' ≠ T := fun g' h' => hT g' (by simp [h'])
      have hstk' : s.stk k = g :: (gs' ++ T :: below) := by simpa using hstk
      let a1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (gs' ++ T :: below)⟩
      let a2 : State := ⟨a1.reg, Function.update a1.stk d1 (a1.reg r :: a1.stk d1)⟩
      let a3 : State := ⟨a2.reg, Function.update a2.stk d2 (a2.reg r :: a2.stk d2)⟩
      let a4 : State := ⟨Function.update a3.reg r Glyph.eos, a3.stk⟩
      have ha1r : a1.reg r = g := by simp [a1]
      have ha2r : a2.reg r = g := by simp [a2, a1]
      have ha3r : a3.reg r = g := by simp [a3, a2, a1]
      have e1 : Eval main (.pop k r) s a1 1 := by
        have h := Eval.pop (main := main) k r s
        rw [hstk'] at h
        simpa [a1, List.headD_cons, List.tail_cons] using h
      have e2 : Eval main (.push d1 r) a1 a2 1 := by
        have h := Eval.push (main := main) d1 r a1
        simpa [a2, State.tPush, ha1r] using h
      have e3 : Eval main (.push d2 r) a2 a3 1 := by
        have h := Eval.push (main := main) d2 r a2
        simpa [a3, State.tPush, ha2r] using h
      have e4 : Eval main (.set r Glyph.eos) a3 a4 1 := by
        have h := Eval.set (main := main) r Glyph.eos a3
        simpa [a4] using h
      have hgT' : ¬ (a1.reg r = T) := by rw [ha1r]; exact hgT
      have eite : Eval main (.ite r T (.seq (.push k r) (.set r T))
          (.seq (.push d1 r) (.seq (.push d2 r) (.set r Glyph.eos)))) a1 a4 4 :=
        Eval.iteF hgT' (Eval.seq e2 (Eval.seq e3 e4))
      have ebody : Eval main (cBody2 k T d1 d2 r) s a4 5 := Eval.seq e1 eite
      have hr4 : a4.reg r = Glyph.eos := by simp [a4, a3, a2, a1]
      have ha4k : a4.stk k = gs' ++ T :: below := by
        simp only [a4, a3, a2, a1]
        simp [Function.update_apply, Ne.symm hd1k, Ne.symm hd2k]
      have hrec := ih below a4 ha4k hgs'T hr4
      have hmain : Eval main (.loop r Glyph.eos (cBody2 k T d1 d2 r)) s
          (c2St k T d1 d2 r gs' below a4) (5 + (6 + gs'.length * 6) + 1) :=
        Eval.loopT hr ebody hrec
      have h4d1 : a4.stk d1 = g :: s.stk d1 := by
        simp only [a4, a3, a2, a1]
        simp [Function.update_apply, ha1r, hd12, hd1k]
      have h4d2 : a4.stk d2 = g :: s.stk d2 := by
        simp only [a4, a3, a2, a1]
        simp [Function.update_apply, ha2r, Ne.symm hd12, hd2k]
      have h4o : ∀ j : Stk, j ≠ k → j ≠ d1 → j ≠ d2 → a4.stk j = s.stk j := by
        intro j hjk hjd1 hjd2
        simp only [a4, a3, a2, a1]
        simp [Function.update_apply, hjk, hjd1, hjd2]
      have hstate : c2St k T d1 d2 r gs' below a4 = c2St k T d1 d2 r (g :: gs') below s := by
        apply State.ext'
        · intro q
          have hreg4 : a4.reg = Function.update s.reg r Glyph.eos := by simp [a4, a3, a2, a1]
          simp only [c2St, hreg4, Function.update_apply]
          by_cases hq : q = r <;> simp [hq]
        · intro q
          by_cases hqk : q = k
          · rw [hqk]
            rw [c2St_stk_k k T d1 d2 r gs' below a4 (Ne.symm hd1k) (Ne.symm hd2k),
              c2St_stk_k k T d1 d2 r (g :: gs') below s (Ne.symm hd1k) (Ne.symm hd2k)]
          · by_cases hqd1 : q = d1
            · rw [hqd1]
              rw [c2St_stk_d1 k T d1 d2 r gs' below a4 hd12,
                c2St_stk_d1 k T d1 d2 r (g :: gs') below s hd12, h4d1]
              simp [List.reverse_cons, List.append_assoc]
            · by_cases hqd2 : q = d2
              · rw [hqd2]
                rw [c2St_stk_d2 k T d1 d2 r gs' below a4,
                  c2St_stk_d2 k T d1 d2 r (g :: gs') below s, h4d2]
                simp [List.reverse_cons, List.append_assoc]
              · rw [c2St_stk_other k T d1 d2 q r gs' below a4 hqk hqd1 hqd2,
                  c2St_stk_other k T d1 d2 q r (g :: gs') below s hqk hqd1 hqd2,
                  h4o q hqk hqd1 hqd2]
      rw [hstate] at hmain
      have hc : 5 + (6 + gs'.length * 6) + 1 = 6 + (g :: gs').length * 6 := by
        simp only [List.length_cons]; ring
      rw [← hc]
      exact hmain

theorem c2LoopEval (main : Cmd) (k : Stk) (T : Glyph) (d1 d2 : Stk) (r : Reg)
    (hTe : T ≠ Glyph.eos) (hd1k : d1 ≠ k) (hd2k : d2 ≠ k) (hd12 : d1 ≠ d2)
    (gs below : List Glyph) (s : State) (hstk : s.stk k = gs ++ T :: below)
    (hT : ∀ g ∈ gs, g ≠ T) :
    Eval main (cLoop2 k T d1 d2 r) s (c2St k T d1 d2 r gs below s) (7 + gs.length * 6) := by
  have h1 : Eval main (.set r Glyph.eos) s (s.updReg r Glyph.eos) 1 := Eval.set r Glyph.eos s
  have h2 : Eval main (.loop r Glyph.eos (cBody2 k T d1 d2 r)) (s.updReg r Glyph.eos)
      (c2St k T d1 d2 r gs below (s.updReg r Glyph.eos)) (6 + gs.length * 6) :=
    c2LoopAux main k T d1 d2 r hTe hd1k hd2k hd12 gs below (s.updReg r Glyph.eos)
      (by simpa using hstk) hT (by simp)
  have h3 : c2St k T d1 d2 r gs below (s.updReg r Glyph.eos) = c2St k T d1 d2 r gs below s := by
    apply State.ext'
    · intro q
      simp only [c2St, State.updReg_apply]
      by_cases hq : q = r
      · subst hq; simp
      · simp [hq]
    · intro q
      simp only [c2St, State.updReg_stk]
  rw [h3] at h2
  have h4 := Eval.seq h1 h2
  have hc : 7 + gs.length * 6 = 1 + (6 + gs.length * 6) := by ring
  rw [hc]
  exact h4

end Dup2Gen
end SG
end Work.IntLib

namespace Work.IntLib.SqrtGcd

open HvdH

/-- `dup2` duplicates the bit region of `src` on `dst`, keeping `src`, restoring the scratch stacks
`t1`, `t2` and the part of every stack below the markers; `main` is arbitrary (no `self` is used). -/
theorem dup2EvalGen (main : HvdH.Cmd) (src dst t1 t2 : HvdH.Stk) (r : HvdH.Reg) (gs : List Bool)
    (below bD b1 b2 : List HvdH.Glyph) (s : HvdH.State)
    (hsrc : s.stk src = gs.map HvdH.Glyph.bit ++ HvdH.Glyph.mk src :: below)
    (hdst : s.stk dst = HvdH.Glyph.mk dst :: bD)
    (ht1 : s.stk t1 = HvdH.Glyph.mk t1 :: b1)
    (ht2 : s.stk t2 = HvdH.Glyph.mk t2 :: b2)
    (hd : dst ≠ src) (h1s : t1 ≠ src) (h2s : t2 ≠ src) (h1d : t1 ≠ dst) (h2d : t2 ≠ dst)
    (h12 : t1 ≠ t2) :
    ∃ s' m, HvdH.Eval main (Work.IntLib.SG.dup2 src dst t1 t2 r) s s' m ∧
      m ≤ 100 + gs.length * 40 ∧
      s'.stk src = gs.map HvdH.Glyph.bit ++ HvdH.Glyph.mk src :: below ∧
      s'.stk dst = gs.map HvdH.Glyph.bit ++ HvdH.Glyph.mk dst :: bD ∧
      s'.stk t1 = HvdH.Glyph.mk t1 :: b1 ∧
      s'.stk t2 = HvdH.Glyph.mk t2 :: b2 ∧
      (∀ j : HvdH.Stk, j ≠ src → j ≠ dst → j ≠ t1 → j ≠ t2 → s'.stk j = s.stk j) := by
  -- orientations of the distinctness hypotheses
  have hsd : src ≠ dst := hd.symm
  have hs1 : src ≠ t1 := h1s.symm
  have hs2 : src ≠ t2 := h2s.symm
  have h21 : t2 ≠ t1 := h12.symm
  have hds : dst ≠ t1 := h1d.symm
  have hdt : dst ≠ t2 := h2d.symm
  -- the region of `src` as a list of glyphs
  set b : List Glyph := gs.map Glyph.bit with hb
  have hblen : b.length = gs.length := by rw [hb]; simp
  have hbrlen : b.reverse.length = gs.length := by rw [hb]; simp
  -- the intermediate states
  set s1 : State := SG.c2St src (Glyph.mk src) t1 t2 r b below s with hs1def
  set s2 : State := SG.mSt t1 (Glyph.mk t1) src r b.reverse b1 s1 with hs2def
  set s3 : State := SG.mSt t2 (Glyph.mk t2) t1 r b.reverse b2 s2 with hs3def
  set s4 : State := SG.mSt t1 (Glyph.mk t1) t2 r b b1 s3 with hs4def
  set s5 : State := SG.mSt t2 (Glyph.mk t2) dst r b.reverse b2 s4 with hs5def
  -- every glyph of the region is a `bit`, hence different from every marker
  have hbne : ∀ (j : Stk) (g : Glyph), g ∈ b → g ≠ Glyph.mk j := by
    intro j g hg
    have hg' : g ∈ gs.map Glyph.bit := by rw [← hb]; exact hg
    rw [List.mem_map] at hg'
    obtain ⟨x, -, hx⟩ := hg'
    rw [← hx]
    exact SG.Dup2Gen.bit_ne_mk x j
  have hbS : ∀ g ∈ b, g ≠ Glyph.mk src := fun g hg => hbne src g hg
  have hbT1 : ∀ g ∈ b, g ≠ Glyph.mk t1 := fun g hg => hbne t1 g hg
  have hbT2 : ∀ g ∈ b, g ≠ Glyph.mk t2 := fun g hg => hbne t2 g hg
  have hbRS : ∀ g ∈ b.reverse, g ≠ Glyph.mk src := fun g hg => hbne src g (List.mem_reverse.mp hg)
  have hbR1 : ∀ g ∈ b.reverse, g ≠ Glyph.mk t1 := fun g hg => hbne t1 g (List.mem_reverse.mp hg)
  have hbR2 : ∀ g ∈ b.reverse, g ≠ Glyph.mk t2 := fun g hg => hbne t2 g (List.mem_reverse.mp hg)
  -- the region of `src`
  have hsrcb : s.stk src = b ++ Glyph.mk src :: below := by rw [hb]; exact hsrc
  -- the stacks of `s1`, ..., `s4`
  have hs1t1 : s1.stk t1 = b.reverse ++ Glyph.mk t1 :: b1 := by
    rw [hs1def, SG.Dup2Gen.c2St_stk_d1 src (Glyph.mk src) t1 t2 r b below s h12, ht1]
  have hs1t2 : s1.stk t2 = b.reverse ++ Glyph.mk t2 :: b2 := by
    rw [hs1def, SG.Dup2Gen.c2St_stk_d2 src (Glyph.mk src) t1 t2 r b below s, ht2]
  have hs2t1 : s2.stk t1 = Glyph.mk t1 :: b1 := by
    rw [hs2def, SG.Dup2Gen.mSt_stk_k t1 (Glyph.mk t1) src r b.reverse b1 s1 h1s]
  have hs2t2 : s2.stk t2 = b.reverse ++ Glyph.mk t2 :: b2 := by
    rw [hs2def, SG.Dup2Gen.mSt_stk_other t1 (Glyph.mk t1) src t2 r b.reverse b1 s1 h21 h2s,
      hs1t2]
  have hs3t2 : s3.stk t2 = Glyph.mk t2 :: b2 := by
    rw [hs3def, SG.Dup2Gen.mSt_stk_k t2 (Glyph.mk t2) t1 r b.reverse b2 s2 h21]
  have hs3t1 : s3.stk t1 = b ++ Glyph.mk t1 :: b1 := by
    rw [hs3def, SG.Dup2Gen.mSt_stk_d t2 (Glyph.mk t2) t1 r b.reverse b2 s2, hs2t1,
      List.reverse_reverse]
  have hs4t2 : s4.stk t2 = b.reverse ++ Glyph.mk t2 :: b2 := by
    rw [hs4def, SG.Dup2Gen.mSt_stk_d t1 (Glyph.mk t1) t2 r b b1 s3, hs3t2]
  -- the five steps of `dup2`
  have e1 : Eval main (SG.cLoop2 src (Glyph.mk src) t1 t2 r) s s1 (7 + gs.length * 6) := by
    have h := SG.Dup2Gen.c2LoopEval main src (Glyph.mk src) t1 t2 r (SG.Dup2Gen.mk_ne_eos src)
      h1s h2s h12 b below s hsrcb hbS
    rw [← hs1def] at h
    simpa [hblen] using h
  have e2 : Eval main (SG.rLoop t1 (Glyph.mk t1) (some src) r) s1 s2 (7 + gs.length * 5) := by
    have h := SG.mLoop_eval main t1 (Glyph.mk t1) src r (SG.Dup2Gen.mk_ne_eos t1) hs1
      b.reverse b1 s1 hs1t1 hbR1
    rw [← hs2def] at h
    simpa [hbrlen] using h
  have e3 : Eval main (SG.rLoop t2 (Glyph.mk t2) (some t1) r) s2 s3 (7 + gs.length * 5) := by
    have h := SG.mLoop_eval main t2 (Glyph.mk t2) t1 r (SG.Dup2Gen.mk_ne_eos t2) h12
      b.reverse b2 s2 hs2t2 hbR2
    rw [← hs3def] at h
    simpa [hbrlen] using h
  have e4 : Eval main (SG.rLoop t1 (Glyph.mk t1) (some t2) r) s3 s4 (7 + gs.length * 5) := by
    have h := SG.mLoop_eval main t1 (Glyph.mk t1) t2 r (SG.Dup2Gen.mk_ne_eos t1) h21
      b b1 s3 hs3t1 hbT1
    rw [← hs4def] at h
    simpa [hblen] using h
  have e5 : Eval main (SG.rLoop t2 (Glyph.mk t2) (some dst) r) s4 s5 (7 + gs.length * 5) := by
    have h := SG.mLoop_eval main t2 (Glyph.mk t2) dst r (SG.Dup2Gen.mk_ne_eos t2) hdt
      b.reverse b2 s4 hs4t2 hbR2
    rw [← hs5def] at h
    simpa [hbrlen] using h
  have hcomb : Eval main
      (Work.Layout.seqs [SG.cLoop2 src (Glyph.mk src) t1 t2 r,
        SG.rLoop t1 (Glyph.mk t1) (some src) r,
        SG.rLoop t2 (Glyph.mk t2) (some t1) r,
        SG.rLoop t1 (Glyph.mk t1) (some t2) r,
        SG.rLoop t2 (Glyph.mk t2) (some dst) r]) s s5
      ((7 + gs.length * 6) + ((7 + gs.length * 5) + ((7 + gs.length * 5) +
        ((7 + gs.length * 5) + (7 + gs.length * 5))))) :=
    Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))
  -- the final state, stack by stack
  have hs5src : s5.stk src = gs.map Glyph.bit ++ Glyph.mk src :: below := by
    rw [hs5def, SG.Dup2Gen.mSt_stk_other t2 (Glyph.mk t2) dst src r b.reverse b2 s4
        (Ne.symm h2s) hsd,
      hs4def, SG.Dup2Gen.mSt_stk_other t1 (Glyph.mk t1) t2 src r b b1 s3
        (Ne.symm h1s) (Ne.symm h2s),
      hs3def, SG.Dup2Gen.mSt_stk_other t2 (Glyph.mk t2) t1 src r b.reverse b2 s2
        (Ne.symm h2s) (Ne.symm h1s),
      hs2def, SG.Dup2Gen.mSt_stk_d t1 (Glyph.mk t1) src r b.reverse b1 s1,
      hs1def, SG.Dup2Gen.c2St_stk_k src (Glyph.mk src) t1 t2 r b below s (Ne.symm h1s)
        (Ne.symm h2s),
      List.reverse_reverse]
  have hs5dst : s5.stk dst = gs.map Glyph.bit ++ Glyph.mk dst :: bD := by
    rw [hs5def, SG.Dup2Gen.mSt_stk_d t2 (Glyph.mk t2) dst r b.reverse b2 s4,
      hs4def, SG.Dup2Gen.mSt_stk_other t1 (Glyph.mk t1) t2 dst r b b1 s3 hds hdt,
      hs3def, SG.Dup2Gen.mSt_stk_other t2 (Glyph.mk t2) t1 dst r b.reverse b2 s2 hdt hds,
      hs2def, SG.Dup2Gen.mSt_stk_other t1 (Glyph.mk t1) src dst r b.reverse b1 s1 hds hd,
      hs1def, SG.Dup2Gen.c2St_stk_other src (Glyph.mk src) t1 t2 dst r b below s hd hds hdt,
      hdst, List.reverse_reverse]
  have hs5t1 : s5.stk t1 = Glyph.mk t1 :: b1 := by
    rw [hs5def, SG.Dup2Gen.mSt_stk_other t2 (Glyph.mk t2) dst t1 r b.reverse b2 s4 h12 h1d,
      hs4def, SG.Dup2Gen.mSt_stk_k t1 (Glyph.mk t1) t2 r b b1 s3 h12]
  have hs5t2 : s5.stk t2 = Glyph.mk t2 :: b2 := by
    rw [hs5def, SG.Dup2Gen.mSt_stk_k t2 (Glyph.mk t2) dst r b.reverse b2 s4 h2d]
  have hs5o : ∀ j : Stk, j ≠ src → j ≠ dst → j ≠ t1 → j ≠ t2 → s5.stk j = s.stk j := by
    intro j hj1 hj2 hj3 hj4
    rw [hs5def, SG.Dup2Gen.mSt_stk_other t2 (Glyph.mk t2) dst j r b.reverse b2 s4 hj4 hj2,
      hs4def, SG.Dup2Gen.mSt_stk_other t1 (Glyph.mk t1) t2 j r b b1 s3 hj3 hj4,
      hs3def, SG.Dup2Gen.mSt_stk_other t2 (Glyph.mk t2) t1 j r b.reverse b2 s2 hj4 hj3,
      hs2def, SG.Dup2Gen.mSt_stk_other t1 (Glyph.mk t1) src j r b.reverse b1 s1 hj3 hj1,
      hs1def, SG.Dup2Gen.c2St_stk_other src (Glyph.mk src) t1 t2 j r b below s hj1 hj3 hj4]
  have hcost : ((7 + gs.length * 6) + ((7 + gs.length * 5) + ((7 + gs.length * 5) +
      ((7 + gs.length * 5) + (7 + gs.length * 5))))) ≤ 100 + gs.length * 40 := by omega
  exact ⟨s5, _, hcomb, hcost, hs5src, hs5dst, hs5t1, hs5t2, hs5o⟩

end Work.IntLib.SqrtGcd
