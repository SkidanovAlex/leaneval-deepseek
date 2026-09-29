import Mathlib
import Submission.Work.Layout.drainValsEv

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.Layout.merge_drainP`

The loop of `Sk.mergePair` in the degenerate case where the second source run is empty: it drains
the whole run sitting on `SX` onto the accumulator `T`, in reverse order.

* `mBody_post`: the trailing `peek SX rF ; ite rF cons skip (peek SY rF)` of `Sk.mBody`, which only
  reads the top of `SX`/`SY` and sets the loop flag `rF` (it changes no stack).
* `mBody_nilLeft`: one (ineffective) iteration of the loop when `SX` carries no value.
* `mBody_drainP`: one iteration of the loop in which the top value of `SX` is moved onto `T`.
* `loop_drainP`: the induction on the list of values, with the cost bound `30 * (Σ vsz + |Ps| + 1)`.
* `merge_drainP`: the requested statement.
-/

namespace Work.Layout

open HvdH Work.Layout

/-! ## the trailing flag update of `mBody` -/

/-- `peek SX rF ; ite rF cons skip (peek SY rF)`: it changes no stack and sets `rF` to `cons` when
the top of `SX` is `cons`, and to `gMark` otherwise (the top of `SY` being `gMark`). -/
theorem mBody_post {main : Cmd} {SX SY : Stk} {rf : Reg} {g : Reg → Glyph} {X : Stk → List Glyph}
    {P B' : List Glyph} (hSX : X SX = P) (hSY : X SY = gMark :: B') :
    ∃ s' n, Ev main (.seq (.peek SX rf) (.ite rf Glyph.cons .skip (.peek SY rf))) ⟨g, X⟩ s' n ∧
      n ≤ 3 ∧ s'.stk = X ∧
      s'.reg rf = (if P.headD Glyph.eos = Glyph.cons then Glyph.cons else gMark) := by
  have hpeek : Ev main (.peek SX rf) ⟨g, X⟩
      ⟨Function.update g rf (P.headD Glyph.eos), X⟩ 1 := by
    have h := ev_peek' main SX rf g X
    rw [hSX] at h
    exact h
  have hheadSY : (X SY).headD Glyph.eos = gMark := by rw [hSY]; rfl
  by_cases h : P.headD Glyph.eos = Glyph.cons
  · have hskip : Ev main .skip ⟨Function.update g rf (P.headD Glyph.eos), X⟩
        ⟨Function.update g rf (P.headD Glyph.eos), X⟩ 1 := ev_skip main _
    have hite : Ev main (.ite rf Glyph.cons .skip (.peek SY rf))
        ⟨Function.update g rf (P.headD Glyph.eos), X⟩
        ⟨Function.update g rf (P.headD Glyph.eos), X⟩ 2 :=
      Ev.iteT (by
        show (Function.update g rf (P.headD Glyph.eos)) rf = Glyph.cons
        simp only [Function.update_self]
        exact h) hskip
    refine ⟨_, 3, Ev.seq' hpeek hite le_rfl, le_rfl, rfl, ?_⟩
    show (Function.update g rf (P.headD Glyph.eos)) rf =
      (if P.headD Glyph.eos = Glyph.cons then Glyph.cons else gMark)
    rw [if_pos h]
    simpa only [Function.update_self] using h
  · have hne : (Function.update g rf (P.headD Glyph.eos)) rf ≠ Glyph.cons := by
      simp only [Function.update_self]; exact h
    have hpeek2 : Ev main (.peek SY rf) ⟨Function.update g rf (P.headD Glyph.eos), X⟩
        ⟨Function.update (Function.update g rf (P.headD Glyph.eos)) rf gMark, X⟩ 1 := by
      have hh := ev_peek' main SY rf (Function.update g rf (P.headD Glyph.eos)) X
      rw [hheadSY] at hh
      exact hh
    have hite : Ev main (.ite rf Glyph.cons .skip (.peek SY rf))
        ⟨Function.update g rf (P.headD Glyph.eos), X⟩
        ⟨Function.update (Function.update g rf (P.headD Glyph.eos)) rf gMark, X⟩ 2 :=
      Ev.iteF hne hpeek2
    refine ⟨_, 3, Ev.seq' hpeek hite le_rfl, le_rfl, rfl, ?_⟩
    show (Function.update (Function.update g rf (P.headD Glyph.eos)) rf gMark) rf =
      (if P.headD Glyph.eos = Glyph.cons then Glyph.cons else gMark)
    rw [if_neg h]
    simp only [Function.update_self]

/-! ## one ineffective iteration (nothing left on `SX`) -/

/-- If `SX` and `SY` both carry no value (their tops are `gMark`), one iteration of the `mergePair`
loop changes nothing but the loop flag `rF` (which becomes `gMark`), in at most `8` steps. -/
theorem mBody_nilLeft {main pLt pSize : Cmd} {SX SY T SA SB F1 F2 t d : Stk}
    {g : Reg → Glyph} {X : Stk → List Glyph} {A B' : List Glyph}
    (hSX : X SX = gMark :: A) (hSY : X SY = gMark :: B') :
    ∃ s' n, Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧ n ≤ 8 ∧
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
    simp only [g1, Function.update_self]; exact gMark_ne_cons
  have hne2 : g2 Sk.rI ≠ Glyph.cons := by
    simp only [g2, g1, Function.update_self]; exact gMark_ne_cons
  have e3 : Ev main (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip) ⟨g2, X⟩ ⟨g2, X⟩ 2 :=
    Ev.iteF hne2 (ev_skip main ⟨g2, X⟩)
  have e4 : Ev main (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip))
      ⟨g1, X⟩ ⟨g2, X⟩ 3 :=
    Ev.seq' e2 e3 (by omega)
  have e5 : Ev main (.ite Sk.rH Glyph.cons
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
        (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip)))
      ⟨g1, X⟩ ⟨g2, X⟩ 4 :=
    Ev.iteF hne1 e4
  have e6 : Ev main (.seq (.peek SX Sk.rH) (.ite Sk.rH Glyph.cons
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
        (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip))))
      ⟨g, X⟩ ⟨g2, X⟩ 5 :=
    Ev.seq' e1 e5 (by omega)
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
    simp only [Function.update_self]; exact gMark_ne_cons
  have e9 : Ev main (.ite Sk.rF Glyph.cons .skip (.peek SY Sk.rF)) ⟨g3, X⟩
      ⟨Function.update g3 Sk.rF gMark, X⟩ 2 :=
    Ev.iteF hne3 e8
  have e10 : Ev main (.seq (.peek SX Sk.rF) (.ite Sk.rF Glyph.cons .skip (.peek SY Sk.rF)))
      ⟨g2, X⟩ ⟨Function.update g3 Sk.rF gMark, X⟩ 3 :=
    Ev.seq' e7 e9 (by omega)
  have e11 : Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩
      ⟨Function.update g3 Sk.rF gMark, X⟩ 8 := by
    unfold Sk.mBody
    exact Ev.seq' e6 e10 (by omega)
  refine ⟨_, 8, e11, le_rfl, rfl, ?_⟩
  show (Function.update g3 Sk.rF gMark) Sk.rF = gMark
  simp only [Function.update_self]

/-! ## one draining iteration -/

/-- One iteration of the `mergePair` loop when `SX` still carries the value `p` and `SY` carries
none: `p` is moved onto the accumulator `T`, leaving `SX` with the rest of the run and `SY`
untouched, and setting the loop flag `rF` to `cons` iff `ps` is still nonempty. -/
theorem mBody_drainP {main pLt pSize : Cmd} {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph} {A B' Tc : List Glyph} {Tk : List Val}
    {p : Val} {ps : List Val}
    (hp : ∃ (k : ℕ) (v' : Val), p = Val.cons (Val.int (k : ℤ)) v')
    (hps : ∀ v ∈ ps, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v')
    (hSX : X SX = encs (p :: ps) ++ gMark :: A) (hSY : X SY = gMark :: B')
    (hT : X T = encs Tk ++ gMark :: Tc) :
    ∃ s' n, Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (vsz p + 1) + 7 ∧
      s'.stk SX = encs ps ++ gMark :: A ∧ s'.stk SY = gMark :: B' ∧
      s'.stk T = encs (p :: Tk) ++ gMark :: Tc ∧
      (∀ k', k' ∉ ({SX, SY, T} : Finset Stk) → s'.stk k' = X k') ∧
      s'.reg Sk.rF = (if ps = [] then gMark else Glyph.cons) := by
  obtain ⟨k, v', rfl⟩ := hp
  obtain ⟨hSXn, hd1⟩ := List.nodup_cons.mp hdis
  obtain ⟨hSYn, hd2⟩ := List.nodup_cons.mp hd1
  obtain ⟨hTn, hd3⟩ := List.nodup_cons.mp hd2
  obtain ⟨_, hd4⟩ := List.nodup_cons.mp hd3
  obtain ⟨_, hd5⟩ := List.nodup_cons.mp hd4
  obtain ⟨_, hd6⟩ := List.nodup_cons.mp hd5
  obtain ⟨_, hd7⟩ := List.nodup_cons.mp hd6
  obtain ⟨htn, _⟩ := List.nodup_cons.mp hd7
  have htd : t ≠ d := by intro e; exact htn (by rw [e]; simp)
  have hSXT : SX ≠ T := by intro e; exact hSXn (by rw [e]; simp)
  have hSXt : SX ≠ t := by intro e; exact hSXn (by rw [e]; simp)
  have hSXd : SX ≠ d := by intro e; exact hSXn (by rw [e]; simp)
  have hTt : T ≠ t := by intro e; exact hTn (by rw [e]; simp)
  have hTd : T ≠ d := by intro e; exact hTn (by rw [e]; simp)
  have hSYSX : SY ≠ SX := by intro e; exact hSXn (by rw [e]; simp)
  have hSYT : SY ≠ T := by intro e; exact hSYn (by rw [e]; simp)
  have hSYt : SY ≠ t := by intro e; exact hSYn (by rw [e]; simp)
  have hSYd : SY ≠ d := by intro e; exact hSYn (by rw [e]; simp)
  have hpSX : X SX = (Val.cons (Val.int k) v').enc ++ (encs ps ++ gMark :: A) := by
    rw [hSX, drainVals_encs_cons, List.append_assoc]
  have hheadSX : (X SX).headD Glyph.eos = Glyph.cons := by rw [hpSX]; rfl
  have hheadSY : (X SY).headD Glyph.eos = gMark := by rw [hSY]; rfl
  let g1 : Reg → Glyph := Function.update g Sk.rH Glyph.cons
  have e1 : Ev main (.peek SX Sk.rH) ⟨g, X⟩ ⟨g1, X⟩ 1 := by
    have h := ev_peek' main SX Sk.rH g X
    rw [hheadSX] at h
    simpa [g1] using h
  let g2 : Reg → Glyph := Function.update g1 Sk.rI gMark
  have e2 : Ev main (.peek SY Sk.rI) ⟨g1, X⟩ ⟨g2, X⟩ 1 := by
    have h := ev_peek' main SY Sk.rI g1 X
    rw [hheadSY] at h
    simpa [g2] using h
  obtain ⟨s3, n3, hmv, hn3, hSX3, hT3, ht3, hd3', hfr3⟩ :=
    mvVal_ev_full (main := main) (a := SX) (b := T) (c := t) (d := d)
      hSXT hSXt hSXd hTt hTd htd (g := g2) (X := X)
      (v := Val.cons (Val.int k) v') (A := encs ps ++ gMark :: A)
      (B := encs Tk ++ gMark :: Tc) hpSX hT
  have hne2 : g2 Sk.rI ≠ Glyph.cons := by
    simp only [g2, g1, Function.update_self]; exact gMark_ne_cons
  have e4 : Ev main (.ite Sk.rI Glyph.cons
      (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)) ⟨g2, X⟩ s3 (n3 + 1) :=
    Ev.iteF hne2 hmv
  have e5 : Ev main (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
      (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
      ⟨g1, X⟩ s3 (n3 + 2) :=
    Ev.seq' e2 e4 (by omega)
  have hg1 : g1 Sk.rH = Glyph.cons := by simp only [g1, Function.update_self]
  have e6 : Ev main (.ite Sk.rH Glyph.cons
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
        (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip)))
      ⟨g1, X⟩ s3 (n3 + 3) :=
    Ev.iteT hg1 e5
  have e7 : Ev main (.seq (.peek SX Sk.rH) (.ite Sk.rH Glyph.cons
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons
        (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) (mvVal SX T t d)))
      (.seq (.peek SY Sk.rI) (.ite Sk.rI Glyph.cons (mvVal SY T t d) .skip))))
      ⟨g, X⟩ s3 (n3 + 4) :=
    Ev.seq' e1 e6 (by omega)
  have hSY3 : s3.stk SY = gMark :: B' := by
    rw [hfr3 SY hSYSX hSYT hSYt hSYd]; exact hSY
  obtain ⟨s4, n4, hpost, hn4, hstk4, hreg4⟩ :=
    mBody_post (main := main) (SX := SX) (SY := SY) (rf := Sk.rF) (g := s3.reg) (X := s3.stk)
      (P := encs ps ++ gMark :: A) (B' := B') hSX3 hSY3
  have e8 : Ev main (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s4 ((n3 + 4) + n4) := by
    unfold Sk.mBody
    exact Ev.seq' e7 hpost le_rfl
  have hhead : (encs ps ++ gMark :: A).headD Glyph.eos =
      (if ps = [] then gMark else Glyph.cons) := by
    cases ps with
    | nil => rfl
    | cons q qs =>
        obtain ⟨k', v'', hk⟩ := hps q (List.mem_cons_self ..)
        subst hk
        rw [if_neg (List.cons_ne_nil _ _)]
        exact drainVals_headD_encs_consval (Val.int k') v'' qs (gMark :: A)
  refine ⟨s4, (n3 + 4) + n4, e8, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstk4, hSX3]
  · rw [hstk4]; exact hSY3
  · rw [hstk4, hT3, drainVals_encs_cons, List.append_assoc]
  · intro k' hk'
    rw [hstk4]
    have hkSX : k' ≠ SX := fun e => hk' (by rw [e]; simp)
    have hkT : k' ≠ T := fun e => hk' (by rw [e]; simp)
    by_cases hkt : k' = t
    · rw [hkt]; exact ht3
    by_cases hkd : k' = d
    · rw [hkd]; exact hd3'
    exact hfr3 k' hkSX hkT hkt hkd
  · rw [hreg4, hhead]
    by_cases h : ps = [] <;> simp [h, gMark_ne_cons]

/-! ## the loop -/

/-- `|Ps|` iterations of the `mergePair` loop, draining the run `Ps` from `SX` onto `T` (in reverse
order), with cost `≤ 30 * (Σ vsz + |Ps| + 1)`. -/
theorem loop_drainP {main pLt pSize : Cmd} {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    ∀ (Ps Tk : List Val) (A B' Tc : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ v ∈ Ps, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') →
      g Sk.rF = Glyph.cons →
      X SX = encs Ps ++ gMark :: A → X SY = gMark :: B' → X T = encs Tk ++ gMark :: Tc →
      ∃ s' n, Ev main (.loop Sk.rF Glyph.cons (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d))
          ⟨g, X⟩ s' n ∧
        n ≤ 30 * ((Ps.map vsz).sum + Ps.length + 1) ∧
        s'.stk SX = gMark :: A ∧ s'.stk SY = gMark :: B' ∧
        s'.stk T = encs (Ps.reverse ++ Tk) ++ gMark :: Tc ∧
        s'.reg Sk.rF ≠ Glyph.cons ∧
        (∀ k', k' ∉ ({SX, SY, T} : Finset Stk) → s'.stk k' = X k') := by
  intro Ps
  induction Ps with
  | nil =>
      intro Tk A B' Tc g X hrec hg hSX hSY hT
      have hSX' : X SX = gMark :: A := by rw [hSX]; rfl
      obtain ⟨s1, n1, hbody, hn1, hstk1, hreg1⟩ :=
        mBody_nilLeft (main := main) (hSX := hSX') (hSY := hSY)
      have hne : s1.reg Sk.rF ≠ Glyph.cons := by rw [hreg1]; exact gMark_ne_cons
      have hloopF : Ev main (.loop Sk.rF Glyph.cons
          (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) s1 s1 1 := Ev.loopF hne
      have hloopT : Ev main (.loop Sk.rF Glyph.cons
          (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) ⟨g, X⟩ s1 (n1 + 1 + 1) :=
        Ev.loopT hg hbody hloopF
      refine ⟨s1, n1 + 1 + 1, hloopT, ?_, ?_, ?_, ?_, hne, ?_⟩
      · simp only [List.map_nil, List.sum_nil, List.length_nil]
        omega
      · rw [hstk1]; exact hSX'
      · rw [hstk1]; exact hSY
      · rw [hstk1, hT]
        have hx : ([] : List Val).reverse ++ Tk = Tk := by
          rw [List.reverse_nil, List.nil_append]
        rw [hx]
      · intro k' _; rw [hstk1]
  | cons p ps ih =>
      intro Tk A B' Tc g X hrec hg hSX hSY hT
      have hp : ∃ (k : ℕ) (v' : Val), p = Val.cons (Val.int (k : ℤ)) v' :=
        hrec p (List.mem_cons_self ..)
      have hps : ∀ v ∈ ps, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v' :=
        fun v hv => hrec v (List.mem_cons_of_mem p hv)
      obtain ⟨s1, n1, hbody, hn1, hSX1, hSY1, hT1, hfr1, hreg1⟩ :=
        mBody_drainP (main := main) hdis hp hps hSX hSY hT
      by_cases hps0 : ps = []
      · subst ps
        have hne : s1.reg Sk.rF ≠ Glyph.cons := by
          rw [hreg1, if_pos rfl]; exact gMark_ne_cons
        have hloopF : Ev main (.loop Sk.rF Glyph.cons
            (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) s1 s1 1 := Ev.loopF hne
        have hloopT : Ev main (.loop Sk.rF Glyph.cons
            (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) ⟨g, X⟩ s1 (n1 + 1 + 1) :=
          Ev.loopT hg hbody hloopF
        refine ⟨s1, n1 + 1 + 1, hloopT, ?_, ?_, ?_, ?_, hne, ?_⟩
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
            List.length_nil]
          omega
        · rw [hSX1]; rfl
        · exact hSY1
        · rw [hT1]
          have hx : (p :: ([] : List Val)).reverse ++ Tk = p :: Tk := by
            rw [List.reverse_cons, List.reverse_nil, List.nil_append]; rfl
          rw [hx]
        · intro k' hk'; rw [hfr1 k' hk']
      · have hreg1' : s1.reg Sk.rF = Glyph.cons := by rw [hreg1, if_neg hps0]
        obtain ⟨s2, n2, hloop2, hn2, hSX2, hSY2, hT2, hrf2, hfr2⟩ :=
          ih (p :: Tk) A B' Tc s1.reg s1.stk hps hreg1' hSX1 hSY1 hT1
        have hloopT : Ev main (.loop Sk.rF Glyph.cons
            (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) ⟨g, X⟩ s2 (n1 + n2 + 1) :=
          Ev.loopT hg hbody hloop2
        refine ⟨s2, n1 + n2 + 1, hloopT, ?_, hSX2, hSY2, ?_, hrf2, ?_⟩
        · simp only [List.map_cons, List.sum_cons, List.length_cons]
          omega
        · rw [hT2]
          have hx : (p :: ps).reverse ++ Tk = ps.reverse ++ (p :: Tk) := by
            rw [List.reverse_cons, List.append_assoc]; rfl
          rw [hx]
        · intro k' hk'
          rw [hfr2 k' hk', hfr1 k' hk']

/-! ## the requested lemma -/

theorem merge_drainP {main pLt pSize : Cmd} {SX SY T SA SB F1 F2 t d : Stk} (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) {g : Reg → Glyph} {X : Stk → List Glyph} {A B' Tc R Sc : List Glyph} {CLA : List Val} {Tk Ps : List Val} (hrec : ∀ v ∈ Ps, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') (hg : g Sk.rF = Glyph.cons) (hSX : X SX = encs Ps ++ gMark :: A) (hSY : X SY = gMark :: B') (hT : X T = encs Tk ++ gMark :: Tc) (hSA : X SA = encs CLA ++ gMark :: Sc) (h0 : X 0 = R) : ∃ s' n, Ev main (.loop Sk.rF Glyph.cons (Sk.mBody pLt pSize SX SY SA SB T F1 F2 t d)) ⟨g, X⟩ s' n ∧ n ≤ 30 * ((Ps.map vsz).sum + Ps.length + 1) ∧ s'.stk SX = gMark :: A ∧ s'.stk SY = gMark :: B' ∧ s'.stk T = encs (Ps.reverse ++ Tk) ++ gMark :: Tc ∧ s'.stk SA = encs CLA ++ gMark :: Sc ∧ s'.stk 0 = R ∧ s'.reg Sk.rF ≠ Glyph.cons ∧ (∀ k' : Stk, k' ∉ ({SX, SY, T} : Finset Stk) → s'.stk k' = X k') := by
  obtain ⟨s', n, hev, hn, hSX', hSY', hT', hrf, hfr⟩ :=
    loop_drainP (main := main) (pLt := pLt) (pSize := pSize) (SX := SX) (SY := SY) (T := T)
      (SA := SA) (SB := SB) (F1 := F1) (F2 := F2) (t := t) (d := d) hdis
      Ps Tk A B' Tc g X hrec hg hSX hSY hT
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
  exact ⟨s', n, hev, hn, hSX', hSY', hT', by rw [hfr SA hSAmem]; exact hSA,
    by rw [hfr 0 h0mem]; exact h0, hrf, hfr⟩

end Work.Layout
