import Mathlib
-- The requested statement only mentions `Sk.mBody`, `Ev`, `gMark`, `encs`, `vsz`, all of which are
-- available from `Submission.Work.Layout.SortDefs`; we therefore do not depend on the colleague-owned
-- `Submission.Work.Layout.MergeDefs` (which is edited concurrently and whose lemmas this proof does
-- not use).  The statement itself is unchanged.
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.drainValsEv
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.Layout.merge_drainQ`

The loop of `Sk.mergePair` in the degenerate case where the *first* source run is empty (`SX` carries
no record): it drains the whole run sitting on `SY` onto the accumulator `T`, in reverse order, and
stops as soon as the run is empty.

This is the mirror image of `Submission/Work/Layout/merge_drainP.lean` (which treats the case where
`SY` is empty).  `Sk.mBody` is asymmetric in its two sources, so the proof is genuinely different:
with `X SX = gMark :: A`, both `peek`s of `SX` inside the body read `gMark ≠ Glyph.cons`, so the body
takes its two `else` branches, i.e. it reduces to `peek SY rI ; ite rI cons (mvVal SY T t d) skip`
followed by the flag update `peek SX rF ; ite rF cons skip (peek SY rF)`.

Structure:

* `nodup_drainQ` : the pairwise distinctness facts extracted from the `Nodup` hypothesis;
* `mBody_nilQ`  : one ineffective iteration (`SX` and `SY` both carry no record);
* `mBody_stepQ` : one iteration moving the record at the top of `SY` onto `T` (`mvVal_ev_full`);
* `loop_drainQ` : the induction on the run `Qs`, with the cost bound `30 * (Σ vsz + |Qs| + 1)`;
* `merge_drainQ`: the requested statement.
-/

namespace Work.Layout

open HvdH Work.Layout

/-! ## distinctness bookkeeping -/

theorem nodup_drainQ {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    SX ≠ SY ∧ SX ≠ T ∧ SX ≠ t ∧ SX ≠ d ∧ SY ≠ T ∧ SY ≠ t ∧ SY ≠ d ∧
      T ≠ t ∧ T ≠ d ∧ t ≠ d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; rw [h] at hdis; simp at hdis)

/-! ## one ineffective iteration (nothing left on `SY`) -/

/-- If `SX` and `SY` both carry no record (their tops are `gMark`), one iteration of the loop
changes nothing but the loop flag `rF` (which becomes `gMark`), in at most `9` steps. -/
theorem mBody_nilQ {main pLt pSize : Cmd} {SX SY T SA SB F1 F2 t d : Stk}
    {g : Reg → Glyph} {X : Stk → List Glyph} {A B' : List Glyph}
    (hSX : X SX = gMark :: A) (hSY : X SY = gMark :: B') :
    ∃ s' n, Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧ n ≤ 9 ∧
      s'.stk = X ∧ s'.reg Sk.rF = gMark := by
  have hheadSX : (X SX).headD Glyph.eos = gMark := by rw [hSX]; rfl
  have hheadSY : (X SY).headD Glyph.eos = gMark := by rw [hSY]; rfl
  let g1 : Reg → Glyph := Function.update g Sk.rH gMark
  have e1 : Ev main (.peek SX Sk.rH) ⟨g, X⟩ ⟨g1, X⟩ 1 := by
    have h := ev_peek' main SX Sk.rH g X
    rw [hheadSX] at h
    simpa [g1] using h
  let g2 : Reg → Glyph := Function.update g1 Sk.rI gMark
  have e2 : Ev main (.peek SY Sk.rI) ⟨g1, X⟩ ⟨g2, X⟩ 1 := by
    have h := ev_peek' main SY Sk.rI g1 X
    rw [hheadSY] at h
    simpa [g2] using h
  have hne1 : g1 Sk.rH ≠ Glyph.cons := by
    simp only [g1, Function.update_self]
    exact gMark_ne_cons
  have hne2 : g2 Sk.rI ≠ Glyph.cons := by
    simp only [g2, g1, Function.update_self]
    exact gMark_ne_cons
  have e3 : Ev main (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip) ⟨g2, X⟩ ⟨g2, X⟩ 2 :=
    Ev.iteF hne2 (ev_skip main ⟨g2, X⟩)
  have e4 : Ev main (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip))
      ⟨g1, X⟩ ⟨g2, X⟩ 3 := Ev.seq' e2 e3 (by omega)
  have e5 : Ev main (.ite Sk.rH Glyph.cons
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
        (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip)))
      ⟨g1, X⟩ ⟨g2, X⟩ 4 := Ev.iteF hne1 e4
  have e6 : Ev main (.seq (.peek SX Sk.rH) (.ite Sk.rH Glyph.cons
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
        (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip))))
      ⟨g, X⟩ ⟨g2, X⟩ 5 := Ev.seq' e1 e5 (by omega)
  let g3 : Reg → Glyph := Function.update g2 Sk.rF gMark
  have e7 : Ev main (.peek SX Sk.rF) ⟨g2, X⟩ ⟨g3, X⟩ 1 := by
    have h := ev_peek' main SX Sk.rF g2 X
    rw [hheadSX] at h
    simpa [g3] using h
  have e8 : Ev main (.peek SY Sk.rF) ⟨g3, X⟩ ⟨Function.update g3 Sk.rF gMark, X⟩ 1 := by
    have h := ev_peek' main SY Sk.rF g3 X
    rw [hheadSY] at h
    exact h
  have hne3 : (Function.update g3 Sk.rF gMark) Sk.rF ≠ Glyph.cons := by
    simp only [Function.update_self]
    exact gMark_ne_cons
  have e9 : Ev main (.ite Sk.rF Glyph.cons .skip (.peek SY Sk.rF)) ⟨g3, X⟩
      ⟨Function.update g3 Sk.rF gMark, X⟩ 2 := Ev.iteF hne3 e8
  have e10 : Ev main (.seq (.peek SX Sk.rF) (.ite Sk.rF Glyph.cons .skip (.peek SY Sk.rF)))
      ⟨g2, X⟩ ⟨Function.update g3 Sk.rF gMark, X⟩ 3 := Ev.seq' e7 e9 (by omega)
  have e11 : Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩
      ⟨Function.update g3 Sk.rF gMark, X⟩ 8 := by
    unfold Sk.mBody
    exact Ev.seq' e6 e10 (by omega)
  refine ⟨_, 8, e11, by omega, rfl, ?_⟩
  show (Function.update g3 Sk.rF gMark) Sk.rF = gMark
  simp only [Function.update_self]

/-! ## one draining iteration -/

/-- One iteration of the `mergePair` loop when `SY` still carries the record `v` and `SX` carries
none: `v` is moved onto the accumulator `T` (leaving `SY` with the rest of the run and `SX`
untouched), and the loop flag `rF` is set to `cons` iff `vs` is still nonempty. -/
theorem mBody_stepQ {main pLt pSize : Cmd} {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph} {A B' B : List Glyph} {v : Val} {vs : List Val}
    (hrec : ∀ w ∈ v :: vs, ∃ (k : ℕ) (v' : Val), w = Val.cons (Val.int (k : ℤ)) v')
    (hSX : X SX = gMark :: A) (hSY : X SY = encs (v :: vs) ++ gMark :: B') (hT : X T = B) :
    ∃ s' n, Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (vsz v + 1) + 9 ∧
      s'.stk SX = gMark :: A ∧ s'.stk SY = encs vs ++ gMark :: B' ∧
      s'.stk T = v.enc ++ B ∧ s'.reg Sk.rF = (if vs = [] then gMark else Glyph.cons) ∧
      (∀ k' : Stk, k' ∉ ({SX, SY, T} : Finset Stk) → s'.stk k' = X k') := by
  obtain ⟨hSXSY, hSXT, hSXt, hSXd, hSYT, hSYt, hSYd, hTt, hTd, htd⟩ := nodup_drainQ hdis
  have hv : ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
    hrec v (List.mem_cons_self ..)
  have hvs : ∀ w ∈ vs, ∃ (k : ℕ) (v' : Val), w = Val.cons (Val.int (k : ℤ)) v' :=
    fun w hw => hrec w (List.mem_cons_of_mem v hw)
  -- the form of `hvs` needed by `drainVals_headD_encs` (only the existence of *some* cons-shape)
  have hvs' : ∀ w ∈ vs, ∃ a b : Val, w = Val.cons a b := by
    intro w hw
    obtain ⟨k', v'', hk'⟩ := hvs w hw
    exact ⟨Val.int k', v'', hk'⟩
  obtain ⟨k, v', rfl⟩ := hv
  have hheadSX : (X SX).headD Glyph.eos = gMark := by rw [hSX]; rfl
  have hpSY : X SY = (Val.cons (Val.int k) v').enc ++ (encs vs ++ gMark :: B') := by
    rw [hSY, drainVals_encs_cons, List.append_assoc]
  have hheadSY : (X SY).headD Glyph.eos = Glyph.cons := by rw [hpSY]; rfl
  let g1 : Reg → Glyph := Function.update g Sk.rH gMark
  have e1 : Ev main (.peek SX Sk.rH) ⟨g, X⟩ ⟨g1, X⟩ 1 := by
    have h := ev_peek' main SX Sk.rH g X
    rw [hheadSX] at h
    simpa [g1] using h
  let g2 : Reg → Glyph := Function.update g1 Sk.rI Glyph.cons
  have e2 : Ev main (.peek SY Sk.rI) ⟨g1, X⟩ ⟨g2, X⟩ 1 := by
    have h := ev_peek' main SY Sk.rI g1 X
    rw [hheadSY] at h
    simpa [g2] using h
  obtain ⟨s3, n3, hmv, hn3, hSY3, hT3, ht3, hd3, hfr3⟩ :=
    mvVal_ev_full (main := main) (a := SY) (b := T) (c := t) (d := d)
      hSYT hSYt hSYd hTt hTd htd (g := g2) (X := X)
      (v := Val.cons (Val.int k) v') (A := encs vs ++ gMark :: B') (B := B) hpSY hT
  obtain ⟨g3, X3⟩ := s3
  -- restate the hypotheses about the new state with the substituted form of `s3`
  have hfr3' : ∀ k : Stk, k ≠ SY → k ≠ T → k ≠ t → k ≠ d → X3 k = X k := hfr3
  have hSY3' : X3 SY = encs vs ++ gMark :: B' := hSY3
  have hT3' : X3 T = (Val.cons (Val.int k) v').enc ++ B := hT3
  have ht3' : X3 t = X t := ht3
  have hd3' : X3 d = X d := hd3
  have hg2 : g2 Sk.rI = Glyph.cons := by simp only [g2, Function.update_self]
  have e3 : Ev main (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip) ⟨g2, X⟩ ⟨g3, X3⟩ (n3 + 1) :=
    Ev.iteT hg2 hmv
  have e4 : Ev main (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip))
      ⟨g1, X⟩ ⟨g3, X3⟩ (n3 + 2) := Ev.seq' e2 e3 (by omega)
  have hne1 : g1 Sk.rH ≠ Glyph.cons := by
    simp only [g1, Function.update_self]
    exact gMark_ne_cons
  have e5 : Ev main (.ite Sk.rH Glyph.cons
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
        (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip)))
      ⟨g1, X⟩ ⟨g3, X3⟩ (n3 + 3) := Ev.iteF hne1 e4
  have e6 : Ev main (.seq (.peek SX Sk.rH) (.ite Sk.rH Glyph.cons
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
        (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip))))
      ⟨g, X⟩ ⟨g3, X3⟩ (n3 + 4) := Ev.seq' e1 e5 (by omega)
  have hSX3 : X3 SX = gMark :: A := by
    rw [hfr3' SX hSXSY hSXT hSXt hSXd]
    exact hSX
  have hheadSY3 : (X3 SY).headD Glyph.eos = (if vs = [] then gMark else Glyph.cons) := by
    rw [hSY3', drainVals_headD_encs hvs']
    by_cases h : vs = [] <;> simp [h]
  let g4 : Reg → Glyph := Function.update g3 Sk.rF gMark
  have e7 : Ev main (.peek SX Sk.rF) ⟨g3, X3⟩ ⟨g4, X3⟩ 1 := by
    have h := ev_peek' main SX Sk.rF g3 X3
    rw [hSX3] at h
    simpa [g4] using h
  have e8 : Ev main (.peek SY Sk.rF) ⟨g4, X3⟩
      ⟨Function.update g4 Sk.rF ((X3 SY).headD Glyph.eos), X3⟩ 1 :=
    ev_peek' main SY Sk.rF g4 X3
  have hne3 : g4 Sk.rF ≠ Glyph.cons := by
    simp only [g4, Function.update_self]
    exact gMark_ne_cons
  have e9 : Ev main (.ite Sk.rF Glyph.cons .skip (.peek SY Sk.rF)) ⟨g4, X3⟩
      ⟨Function.update g4 Sk.rF ((X3 SY).headD Glyph.eos), X3⟩ 2 := Ev.iteF hne3 e8
  have e10 : Ev main (.seq (.peek SX Sk.rF) (.ite Sk.rF Glyph.cons .skip (.peek SY Sk.rF)))
      ⟨g3, X3⟩ ⟨Function.update g4 Sk.rF ((X3 SY).headD Glyph.eos), X3⟩ 3 :=
    Ev.seq' e7 e9 (by omega)
  have e11 : Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩
      ⟨Function.update g4 Sk.rF ((X3 SY).headD Glyph.eos), X3⟩ (n3 + 7) := by
    unfold Sk.mBody
    exact Ev.seq' e6 e10 (by omega)
  refine ⟨_, n3 + 7, e11, by omega, hSX3, hSY3', hT3', ?_, ?_⟩
  · show (Function.update g4 Sk.rF ((X3 SY).headD Glyph.eos)) Sk.rF =
      (if vs = [] then gMark else Glyph.cons)
    rw [Function.update_self, hheadSY3]
  · intro k' hk'
    have hk'SY : k' ≠ SY := fun e => hk' (by rw [e]; simp)
    have hk'T : k' ≠ T := fun e => hk' (by rw [e]; simp)
    by_cases hkt : k' = t
    · rw [hkt]; exact ht3'
    by_cases hkd : k' = d
    · rw [hkd]; exact hd3'
    exact hfr3' k' hk'SY hk'T hkt hkd

/-! ## the loop -/

/-- `|Qs|` iterations of the `mergePair` loop, draining the run `Qs` from `SY` onto `T` (in reverse
order), with cost `≤ 30 * (Σ vsz + |Qs| + 1)`. -/
theorem loop_drainQ {main pLt pSize : Cmd} {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    ∀ (Qs : List Val) (A B' B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ v ∈ Qs, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') →
      g Sk.rF = Glyph.cons → X SX = gMark :: A → X SY = encs Qs ++ gMark :: B' →
      X T = B →
      ∃ s' n, Ev main (.loop Sk.rF Glyph.cons (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d))
          ⟨g, X⟩ s' n ∧
        n ≤ 30 * ((Qs.map vsz).sum + Qs.length + 1) ∧
        s'.stk SX = gMark :: A ∧ s'.stk SY = gMark :: B' ∧
        s'.stk T = encs Qs.reverse ++ B ∧
        s'.reg Sk.rF ≠ Glyph.cons ∧
        (∀ k', k' ∉ ({SX, SY, T} : Finset Stk) → s'.stk k' = X k') := by
  intro Qs
  induction Qs with
  | nil =>
      intro A B' B g X hrec hg hSX hSY hT
      have hSY' : X SY = gMark :: B' := by rw [hSY]; rfl
      obtain ⟨s1, n1, hbody, hn1, hstk1, hreg1⟩ :=
        mBody_nilQ (main := main) (hSX := hSX) (hSY := hSY')
      have hne : s1.reg Sk.rF ≠ Glyph.cons := by rw [hreg1]; exact gMark_ne_cons
      have hloopF : Ev main (.loop Sk.rF Glyph.cons
          (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) s1 s1 1 := Ev.loopF hne
      have hloopT : Ev main (.loop Sk.rF Glyph.cons
          (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) ⟨g, X⟩ s1 (n1 + 1 + 1) :=
        Ev.loopT hg hbody hloopF
      refine ⟨s1, n1 + 1 + 1, hloopT, ?_, ?_, ?_, ?_, hne, ?_⟩
      · simp only [List.map_nil, List.sum_nil, List.length_nil]
        omega
      · rw [hstk1]; exact hSX
      · rw [hstk1]; exact hSY'
      · rw [hstk1, hT, List.reverse_nil]
        rw [drainVals_encs_nil, List.nil_append]
      · intro k' _
        rw [hstk1]
  | cons v vs ih =>
      intro A B' B g X hrec hg hSX hSY hT
      have hvs : ∀ w ∈ vs, ∃ (k : ℕ) (v' : Val), w = Val.cons (Val.int (k : ℤ)) v' :=
        fun w hw => hrec w (List.mem_cons_of_mem v hw)
      obtain ⟨s1, n1, hbody, hn1, hSX1, hSY1, hT1, hreg1, hfr1⟩ :=
        mBody_stepQ (main := main) hdis hrec hSX hSY hT
      by_cases hvs0 : vs = []
      · subst hvs0
        have hne : s1.reg Sk.rF ≠ Glyph.cons := by
          rw [hreg1, if_pos rfl]; exact gMark_ne_cons
        have hloopF : Ev main (.loop Sk.rF Glyph.cons
            (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) s1 s1 1 := Ev.loopF hne
        have hloopT : Ev main (.loop Sk.rF Glyph.cons
            (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) ⟨g, X⟩ s1 (n1 + 1 + 1) :=
          Ev.loopT hg hbody hloopF
        refine ⟨s1, n1 + 1 + 1, hloopT, ?_, hSX1, ?_, ?_, hne, ?_⟩
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
            List.length_nil]
          omega
        · rw [hSY1]
          rfl
        · rw [hT1, List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [drainVals_encs_cons, drainVals_encs_nil, List.append_nil]
        · intro k' hk'
          rw [hfr1 k' hk']
      · have hreg1' : s1.reg Sk.rF = Glyph.cons := by rw [hreg1, if_neg hvs0]
        obtain ⟨s2, n2, hloop2, hn2, hSX2, hSY2, hT2, hrf2, hfr2⟩ :=
          ih A B' (v.enc ++ B) s1.reg s1.stk hvs hreg1' hSX1 hSY1 hT1
        have hloopT : Ev main (.loop Sk.rF Glyph.cons
            (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) ⟨g, X⟩ s2 (n1 + n2 + 1) :=
          Ev.loopT hg hbody hloop2
        refine ⟨s2, n1 + n2 + 1, hloopT, ?_, hSX2, hSY2, ?_, hrf2, ?_⟩
        · simp only [List.map_cons, List.sum_cons, List.length_cons]
          omega
        · rw [hT2, drainVals_encs_reverse_cons, List.append_assoc]
        · intro k' hk'
          rw [hfr2 k' hk', hfr1 k' hk']

/-! ## the requested lemma -/

theorem merge_drainQ {main pLt pSize : Cmd} {SX SY T SA SB F1 F2 t d : Stk} (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) {g : Reg → Glyph} {X : Stk → List Glyph} {A B' Tc R Sc : List Glyph} {CLA : List Val} {Tk Qs : List Val} (hrec : ∀ v ∈ Qs, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') (hg : g Sk.rF = Glyph.cons) (hSX : X SX = gMark :: A) (hSY : X SY = encs Qs ++ gMark :: B') (hT : X T = encs Tk ++ gMark :: Tc) (hSA : X SA = encs CLA ++ gMark :: Sc) (h0 : X 0 = R) : ∃ s' n, Ev main (.loop Sk.rF Glyph.cons (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) ⟨g, X⟩ s' n ∧ n ≤ 30 * ((Qs.map vsz).sum + Qs.length + 1) ∧ s'.stk SX = gMark :: A ∧ s'.stk SY = gMark :: B' ∧ s'.stk T = encs (Qs.reverse ++ Tk) ++ gMark :: Tc ∧ s'.stk SA = encs CLA ++ gMark :: Sc ∧ s'.stk 0 = R ∧ s'.reg Sk.rF ≠ Glyph.cons ∧ (∀ k' : Stk, k' ∉ ({SX, SY, T} : Finset Stk) → s'.stk k' = X k') := by
  obtain ⟨s', n, hev, hn, hSX', hSY', hT', hrf, hfr⟩ :=
    loop_drainQ (main := main) (pLt := pLt) (pSize := pSize) (SX := SX) (SY := SY) (T := T)
      (SA := SA) (SB := SB) (F1 := F1) (F2 := F2) (t := t) (d := d) hdis
      Qs A B' (encs Tk ++ gMark :: Tc) g X hrec hg hSX hSY hT
  obtain ⟨hSXn, hd1⟩ := List.nodup_cons.mp hdis
  obtain ⟨hSYn, hd2⟩ := List.nodup_cons.mp hd1
  obtain ⟨hTn, -⟩ := List.nodup_cons.mp hd2
  have hSASX : SA ≠ SX := by intro e; exact hSXn (by rw [e]; simp)
  have hSASY : SA ≠ SY := by intro e; exact hSYn (by rw [e]; simp)
  have hSAT : SA ≠ T := by intro e; exact hTn (by rw [e]; simp)
  have h0SX : (0 : Stk) ≠ SX := by intro e; exact hSXn (by rw [e]; simp)
  have h0SY : (0 : Stk) ≠ SY := by intro e; exact hSYn (by rw [e]; simp)
  have h0T : (0 : Stk) ≠ T := by intro e; exact hTn (by rw [e]; simp)
  have hSAmem : SA ∉ ({SX, SY, T} : Finset Stk) := by
    simp [Finset.mem_insert, Finset.mem_singleton, hSASX, hSASY, hSAT]
  have h0mem : (0 : Stk) ∉ ({SX, SY, T} : Finset Stk) := by
    simp [Finset.mem_insert, Finset.mem_singleton, h0SX, h0SY, h0T]
  exact ⟨s', n, hev, hn, hSX', hSY', by rw [hT', drainVals_encs_append, List.append_assoc],
    by rw [hfr SA hSAmem]; exact hSA, by rw [hfr 0 h0mem]; exact h0, hrf, hfr⟩

end Work.Layout
