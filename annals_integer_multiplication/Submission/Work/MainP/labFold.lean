import Mathlib
import Submission.Work.MainP.labFoldDefs

/-!
# `Work.MainP.labFold`: the fold over the `cons`-chain `intList l` on stack 7

`labFold step` produces a program that walks the `cons`-chain `intList l` sitting on stack 7
(above an arbitrary rest `Y7`), applies the caller's word `step` once per element — `step` sees
`int l[i] :: int (P i) :: ofList (AC i) :: acc` on the value stack and returns
`int (P (i+1)) :: ofList (AC (i+1)) :: acc` — and leaves `int (P l.length) :: ofList (AC l.length) :: acc`
on stack 0, restoring every stack other than 0 and 7.

The program is `Work.MainP.labProg step = set labR cons ;; loop labR cons (labBody step)`
(`labR = 9`, `labElt = 7`, scratch stacks `labS1 = 14`, `labS2 = 15`):

* `labBody step` peeks the head glyph of stack 7 into `labR`; at `cons` it pops it,
  `Work.Layout.mvVal` moves the exposed factor onto the top of stack 0, `step` runs, and `labR`
  is re-armed; at `nil` it pops the glyph and disarms.

Route: `labWork_ev` (one round's fragment), `labBody_ev` (one round, `cons` case),
`labExit_ev` (the `nil` round), `labLoop_ev` (the loop, by induction on `l.length - i` with the
invariant `labInv`), and the arithmetic bound `1 + cost ≤ 64 * (1 + Σ (Cnt i + size_i + 1))`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH
open Work.Layout

/-- One round of the fold, from the state after the peek: `pop` the `cons` glyph, move the exposed
value `v` onto stack 0, run `step`, re-arm `labR`. -/
theorem labWork_ev (main step : Cmd) (v : Val) (vs : List Val) (T B : List Glyph)
    (Post : List Val → List Val → Prop) (C : ℕ)
    (hstep : WordR main step (fun w => w = v :: vs) Post (fun _ => C))
    (s : State) (h7 : s.stk labElt = Glyph.cons :: (v.enc ++ T)) (h0 : s.stk 0 = encs vs ++ B) :
    ∃ s', Ev main (seqs [Cmd.pop labElt labR, mvVal labElt 0 labS1 labS2, step,
        Cmd.set labR Glyph.cons]) s s' (16 * (vsz v + 1) + C + 2) ∧
      (∃ out, Post (v :: vs) out ∧ s'.stk 0 = encs out ++ B) ∧
      s'.stk labElt = T ∧ s'.reg labR = Glyph.cons ∧
      (∀ k : Stk, k ≠ 0 → k ≠ labElt → s'.stk k = s.stk k) := by
  have hhd : (s.stk labElt).headD Glyph.eos = Glyph.cons := by rw [h7]; rfl
  have htl : (s.stk labElt).tail = v.enc ++ T := by rw [h7]; rfl
  have he1 := ev_pop main labElt labR s
  rw [hhd, htl] at he1
  obtain ⟨s2, n2, he2, hn2, h2a, h2b, h2c, h2d, h2fr⟩ :=
    mvVal_ev_full (main := main) (a := labElt) (b := 0) (c := labS1) (d := labS2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update s.reg labR Glyph.cons)
      (X := Function.update s.stk labElt (v.enc ++ T)) (v := v) (A := T) (B := encs vs ++ B)
      (by simp) (by rw [Function.update_of_ne (by decide : (0 : Stk) ≠ labElt), h0])
  obtain ⟨out, s3, n3, hpost, he3, hn3, h30, h3fr⟩ :=
    hstep (v :: vs) rfl s2 B (by rw [h2b, Work.Kernel.encs_cons, List.append_assoc])
  have hn3' : n3 ≤ C := hn3
  have he4 := ev_set main labR Glyph.cons s3
  refine ⟨{ reg := Function.update s3.reg labR Glyph.cons, stk := s3.stk }, ?_, ?_, ?_, ?_, ?_⟩
  · have hE : Ev main (.seq (.pop labElt labR) (.seq (mvVal labElt 0 labS1 labS2)
        (.seq step (.set labR Glyph.cons)))) s
        { reg := Function.update s3.reg labR Glyph.cons, stk := s3.stk } (1 + (n2 + (n3 + 1))) :=
      Ev.seq he1 (Ev.seq he2 (Ev.seq ⟨n3, he3, le_rfl⟩ he4))
    have hseq : seqs [Cmd.pop labElt labR, mvVal labElt 0 labS1 labS2, step, Cmd.set labR Glyph.cons]
        = .seq (.pop labElt labR)
            (.seq (mvVal labElt 0 labS1 labS2) (.seq step (.set labR Glyph.cons))) := rfl
    rw [hseq]
    exact hE.mono (by omega)
  · exact ⟨out, hpost, h30⟩
  · rw [h3fr labElt (by decide), h2a]
  · rfl
  · intro k hk0 hk7
    have h1 : s3.stk k = s2.stk k := h3fr k hk0
    have h2 : s2.stk k = (Function.update s.stk labElt (v.enc ++ T)) k := by
      by_cases h14 : k = labS1
      · subst h14; exact h2c
      · by_cases h15 : k = labS2
        · subst h15; exact h2d
        · exact h2fr k hk7 hk0 h14 h15
    rw [h1, h2, Function.update_of_ne hk7]

/-- One round of the fold at an index `i < l.length`. -/
theorem labBody_ev (main step : Cmd) (l : List ℕ) (P : ℕ → ℕ) (AC : ℕ → List Val)
    (acc : List Val) (R Y7 : List Glyph) (X : Stk → List Glyph) (Cnt : ℕ → ℕ)
    (hstep : ∀ i, i < l.length → WordR main step
      (fun vs => vs = Val.int ((l.getD i 0 : ℕ) : ℤ) :: Val.int ((P i : ℕ) : ℤ) ::
        ofList (AC i) :: acc)
      (fun _ out => out = Val.int ((P (i+1) : ℕ) : ℤ) :: ofList (AC (i+1)) :: acc)
      (fun _ => Cnt i))
    (i : ℕ) (hi : i < l.length) (s : State) (hs : labInv l P AC acc R Y7 X i s) :
    ∃ s', Ev main (labBody step) s s' (labBd l Cnt i) ∧ labInv l P AC acc R Y7 X (i+1) s' := by
  obtain ⟨h0, h7, hfr, hreg⟩ := hs
  have h7' : s.stk labElt = Glyph.cons ::
      ((Val.int ((l.getD i 0 : ℕ) : ℤ)).enc ++ ((intList (l.drop (i+1))).enc ++ Y7)) := by
    change s.stk (7 : Stk) = _
    rw [h7, intList_drop_cons hi]
    simp only [List.cons_append, List.append_assoc]
  have hhd : (s.stk labElt).headD Glyph.eos = Glyph.cons := by rw [h7']; rfl
  have hepk := ev_peek main labElt labR s
  rw [hhd] at hepk
  obtain ⟨s1, heW, ⟨out, hpost, h1_0⟩, h1_7, h1_reg, h1fr⟩ :=
    labWork_ev main step (Val.int ((l.getD i 0 : ℕ) : ℤ))
      (Val.int ((P i : ℕ) : ℤ) :: ofList (AC i) :: acc)
      ((intList (l.drop (i+1))).enc ++ Y7) R
      (fun _ out => out = Val.int ((P (i+1) : ℕ) : ℤ) :: ofList (AC (i+1)) :: acc) (Cnt i)
      (hstep i hi) { reg := Function.update s.reg labR Glyph.cons, stk := s.stk } h7'
      (by simp only [h0, Work.Kernel.encs_cons, List.append_assoc])
  have hite : Ev main (.ite labR Glyph.cons
      (seqs [Cmd.pop labElt labR, mvVal labElt 0 labS1 labS2, step, Cmd.set labR Glyph.cons])
      (seqs [Cmd.pop labElt labR, Cmd.set labR Glyph.nil]))
      { reg := Function.update s.reg labR Glyph.cons, stk := s.stk } s1
      (16 * (vsz (Val.int ((l.getD i 0 : ℕ) : ℤ)) + 1) + Cnt i + 2 + 1) :=
    Ev.iteT (by simp) heW
  refine ⟨s1, ?_, ?_, ?_, ?_, ?_⟩
  · have hbody : Ev main (.seq (.peek labElt labR) (.ite labR Glyph.cons
        (seqs [Cmd.pop labElt labR, mvVal labElt 0 labS1 labS2, step, Cmd.set labR Glyph.cons])
        (seqs [Cmd.pop labElt labR, Cmd.set labR Glyph.nil]))) s s1
        (1 + (16 * (vsz (Val.int ((l.getD i 0 : ℕ) : ℤ)) + 1) + Cnt i + 2 + 1)) :=
      Ev.seq hepk hite
    have hb : labBody step = .seq (.peek labElt labR) (.ite labR Glyph.cons
        (seqs [Cmd.pop labElt labR, mvVal labElt 0 labS1 labS2, step, Cmd.set labR Glyph.cons])
        (seqs [Cmd.pop labElt labR, Cmd.set labR Glyph.nil])) := rfl
    rw [hb]
    exact hbody.mono (by simp only [labBd]; omega)
  · simp only [h1_0, hpost, Work.Kernel.encs_cons, List.append_assoc]
  · exact h1_7
  · intro k hk0 hk7
    rw [h1fr k hk0 hk7]
    exact hfr k hk0 hk7
  · exact h1_reg

/-- The `nil` round: the chain is exhausted, the closing glyph is consumed and the loop disarmed. -/
theorem labExit_ev (main step : Cmd) (l : List ℕ) (P : ℕ → ℕ) (AC : ℕ → List Val)
    (acc : List Val) (R Y7 : List Glyph) (X : Stk → List Glyph)
    (s : State) (hs : labInv l P AC acc R Y7 X l.length s) :
    ∃ s', Ev main (labBody step) s s' 4 ∧ labFin l P AC acc R Y7 X s' := by
  obtain ⟨h0, h7, hfr, hreg⟩ := hs
  have h7' : s.stk labElt = Glyph.nil :: Y7 := by
    change s.stk (7 : Stk) = _
    rw [h7, intList_enc_drop_length]
    rfl
  have hhd : (s.stk labElt).headD Glyph.eos = Glyph.nil := by rw [h7']; rfl
  have htl : (s.stk labElt).tail = Y7 := by rw [h7']; rfl
  have hepk := ev_peek main labElt labR s
  rw [hhd] at hepk
  have hpop := ev_pop main labElt labR { reg := Function.update s.reg labR Glyph.nil, stk := s.stk }
  rw [hhd, htl] at hpop
  have hset := ev_set main labR Glyph.nil
    { reg := Function.update (Function.update s.reg labR Glyph.nil) labR Glyph.nil,
      stk := Function.update s.stk labElt Y7 }
  have hne : ({ reg := Function.update s.reg labR Glyph.nil, stk := s.stk } : State).reg labR
      ≠ Glyph.cons := by simp
  have hex : Ev main (seqs [Cmd.pop labElt labR, Cmd.set labR Glyph.nil])
      { reg := Function.update s.reg labR Glyph.nil, stk := s.stk }
      { reg := Function.update (Function.update (Function.update s.reg labR Glyph.nil) labR Glyph.nil)
          labR Glyph.nil,
        stk := Function.update s.stk labElt Y7 } 2 := by
    have hseq : seqs [Cmd.pop labElt labR, Cmd.set labR Glyph.nil]
        = .seq (.pop labElt labR) (.set labR Glyph.nil) := rfl
    rw [hseq]
    exact Ev.seq hpop hset
  have hite : Ev main (.ite labR Glyph.cons
      (seqs [Cmd.pop labElt labR, mvVal labElt 0 labS1 labS2, step, Cmd.set labR Glyph.cons])
      (seqs [Cmd.pop labElt labR, Cmd.set labR Glyph.nil]))
      { reg := Function.update s.reg labR Glyph.nil, stk := s.stk }
      { reg := Function.update (Function.update (Function.update s.reg labR Glyph.nil) labR Glyph.nil)
          labR Glyph.nil,
        stk := Function.update s.stk labElt Y7 } (2 + 1) :=
    Ev.iteF hne hex
  have hEv : Ev main (labBody step) s
      { reg := Function.update (Function.update (Function.update s.reg labR Glyph.nil) labR Glyph.nil)
          labR Glyph.nil,
        stk := Function.update s.stk labElt Y7 } 4 := by
    have hb : labBody step = .seq (.peek labElt labR) (.ite labR Glyph.cons
        (seqs [Cmd.pop labElt labR, mvVal labElt 0 labS1 labS2, step, Cmd.set labR Glyph.cons])
        (seqs [Cmd.pop labElt labR, Cmd.set labR Glyph.nil])) := rfl
    rw [hb]
    exact Ev.seq hepk hite
  refine ⟨_, hEv, ?_, ?_, ?_, ?_⟩
  · show Function.update s.stk labElt Y7 0 = _
    rw [Function.update_of_ne (by decide : (0 : Stk) ≠ labElt)]
    exact h0
  · show Function.update s.stk labElt Y7 labElt = Y7
    rw [Function.update_apply]; simp
  · intro k hk0 hk7
    show Function.update s.stk labElt Y7 k = X k
    rw [Function.update_of_ne (a := k) (a' := labElt) (v := Y7) (f := s.stk)
      (by intro h; exact hk7 h)]
    exact hfr k hk0 hk7
  · show Function.update (Function.update (Function.update s.reg labR Glyph.nil) labR Glyph.nil)
        labR Glyph.nil labR = Glyph.nil
    rw [Function.update_apply]; simp

/-- Telescoping the per-round budget. -/
theorem sum_shift (f : ℕ → ℕ) (i k : ℕ) :
    (∑ j ∈ Finset.range (k+1), f (i + j)) = (∑ j ∈ Finset.range k, f (i + 1 + j)) + f i := by
  rw [Finset.sum_range_succ']
  congr 1
  exact Finset.sum_congr rfl (fun j _ => congrArg f (by omega))

/-- The loop: from `labInv … i`, the loop reaches `labFin` with the budget
`6 + Σ_{j<k} (labBd (i+j) + 1)` when `i + k = l.length`. -/
theorem labLoop_ev (main step : Cmd) (l : List ℕ) (P : ℕ → ℕ) (AC : ℕ → List Val)
    (acc : List Val) (R Y7 : List Glyph) (X : Stk → List Glyph) (Cnt : ℕ → ℕ)
    (hbody : ∀ i, i < l.length → ∀ s : State, labInv l P AC acc R Y7 X i s →
      ∃ s', Ev main (labBody step) s s' (labBd l Cnt i) ∧ labInv l P AC acc R Y7 X (i+1) s')
    (hexit : ∀ s : State, labInv l P AC acc R Y7 X l.length s →
      ∃ s', Ev main (labBody step) s s' 4 ∧ labFin l P AC acc R Y7 X s')
    (s : State) (hs : labInv l P AC acc R Y7 X 0 s) :
    ∃ s' n, Ev main (labLoop step) s s' n ∧
      n ≤ 6 + ∑ j ∈ Finset.range l.length, (labBd l Cnt j + 1) ∧
      labFin l P AC acc R Y7 X s' := by
  have aux : ∀ (k i : ℕ) (s : State), i + k = l.length → labInv l P AC acc R Y7 X i s →
      ∃ s' C, Ev main (labLoop step) s s' C ∧
        C ≤ 6 + ∑ j ∈ Finset.range k, (labBd l Cnt (i+j) + 1) ∧
        labFin l P AC acc R Y7 X s' := by
    intro k
    induction k with
    | zero =>
      intro i s hik hs
      have hi : i = l.length := by omega
      subst hi
      obtain ⟨s₁, hb, hf⟩ := hexit s hs
      have hne : s₁.reg labR ≠ Glyph.cons := by rw [hf.2.2.2]; decide
      have hloop : Ev main (labLoop step) s s₁ 6 := by
        rw [labLoop]
        exact Ev.loopT hs.2.2.2 hb (Ev.loopF hne)
      refine ⟨s₁, 6, hloop, ?_, hf⟩
      rw [Finset.sum_range_zero]
      norm_num
    | succ k ih =>
      intro i s hik hs
      have hi : i < l.length := by omega
      obtain ⟨s₁, hb, hs₁⟩ := hbody i hi s hs
      obtain ⟨s₂, C₂, hev₂, hc₂, hf⟩ := ih (i+1) s₁ (by omega) hs₁
      have hloop : Ev main (labLoop step) s s₂ (labBd l Cnt i + C₂ + 1) := by
        rw [labLoop]
        exact Ev.loopT hs.2.2.2 hb hev₂
      refine ⟨s₂, labBd l Cnt i + C₂ + 1, hloop, ?_, hf⟩
      rw [sum_shift (fun j => labBd l Cnt j + 1) i k]
      omega
  obtain ⟨s', C, hev, hc, hf⟩ := aux l.length 0 s (by omega) hs
  have hc' : C ≤ 6 + ∑ j ∈ Finset.range l.length, (labBd l Cnt j + 1) := by
    refine le_trans hc (le_of_eq ?_)
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.zero_add]
  exact ⟨s', C, hev, hc', hf⟩

theorem labFold (step : HvdH.Cmd) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (l : List ℕ) (P : ℕ → ℕ)
      (AC : ℕ → List HvdH.Val) (Cnt : ℕ → ℕ),
      (∀ i, i < l.length → ∀ acc : List HvdH.Val,
        HvdH.WordR main step
          (fun vs => vs = HvdH.Val.int ((l.getD i 0 : ℕ) : ℤ) ::
            HvdH.Val.int ((P i : ℕ) : ℤ) :: HvdH.ofList (AC i) :: acc)
          (fun _ out => out = HvdH.Val.int ((P (i+1) : ℕ) : ℤ) ::
            HvdH.ofList (AC (i+1)) :: acc)
          (fun _ => Cnt i)) →
      ∀ (acc : List HvdH.Val) (R Y7 : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
        (X : HvdH.Stk → List HvdH.Glyph),
      X 0 = (HvdH.Val.int ((P 0 : ℕ) : ℤ)).enc ++ (HvdH.ofList (AC 0)).enc ++
        HvdH.encs acc ++ R →
      X 7 = (HvdH.intList l).enc ++ Y7 →
      ∃ s' n, Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧
        n ≤ K * (1 + ∑ i ∈ Finset.range l.length, (Cnt i + (l.getD i 0).size + 1)) ∧
        s'.stk 0 = (HvdH.Val.int ((P l.length : ℕ) : ℤ)).enc ++
          (HvdH.ofList (AC l.length)).enc ++ HvdH.encs acc ++ R ∧
        s'.stk 7 = Y7 ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 7 → s'.stk k = X k) := by
  refine ⟨labProg step, 64, ?_⟩
  intro main l P AC Cnt hstep acc R Y7 g X hX0 hX7
  have hbody : ∀ i, i < l.length → ∀ s : State, labInv l P AC acc R Y7 X i s →
      ∃ s', Ev main (labBody step) s s' (labBd l Cnt i) ∧ labInv l P AC acc R Y7 X (i+1) s' :=
    fun i hi s hs => labBody_ev main step l P AC acc R Y7 X Cnt
      (fun i hi => hstep i hi acc) i hi s hs
  have hexit : ∀ s : State, labInv l P AC acc R Y7 X l.length s →
      ∃ s', Ev main (labBody step) s s' 4 ∧ labFin l P AC acc R Y7 X s' :=
    fun s hs => labExit_ev main step l P AC acc R Y7 X s hs
  have hs0 : labInv l P AC acc R Y7 X 0
      { reg := Function.update g labR Glyph.cons, stk := X } := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hX0
    · simpa using hX7
    · intro k hk0 hk7; rfl
    · simp
  obtain ⟨s', Cloop, hev, hc, hf⟩ :=
    labLoop_ev main step l P AC acc R Y7 X Cnt hbody hexit _ hs0
  have hcost : 1 + Cloop
      ≤ 64 * (1 + ∑ i ∈ Finset.range l.length, (Cnt i + (l.getD i 0).size + 1)) := by
    have hbd : ∀ j, labBd l Cnt j + 1 = 16 * ((l.getD j 0).size + 3) + Cnt j + 6 := by
      intro j
      simp only [labBd, vsz_val_int_natCast]
    have hsum : (∑ j ∈ Finset.range l.length, (labBd l Cnt j + 1))
        ≤ ∑ j ∈ Finset.range l.length, (64 * (Cnt j + (l.getD j 0).size + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [hbd j]
      nlinarith
    have hS : (∑ j ∈ Finset.range l.length, (64 * (Cnt j + (l.getD j 0).size + 1)))
        = 64 * ∑ j ∈ Finset.range l.length, (Cnt j + (l.getD j 0).size + 1) := by
      rw [Finset.mul_sum]
    nlinarith [hc, hsum]
  refine ⟨s', 1 + Cloop, ?_, hcost, hf.1, hf.2.1, hf.2.2.1⟩
  · have hprog : labProg step = .seq (.set labR Glyph.cons) (labLoop step) := rfl
    rw [hprog]
    exact Ev.seq (ev_set main labR Glyph.cons (⟨g, X⟩ : State)) hev

end Work.MainP
