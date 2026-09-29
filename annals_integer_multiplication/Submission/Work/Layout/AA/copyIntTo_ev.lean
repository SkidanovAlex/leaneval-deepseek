import Mathlib
import Submission.Work.Layout.AA.Defs
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Layout.AA.enc_int_decomp
import Submission.Work.Layout.AA.copyIntB1_loop

/-!
# `copyIntTo`: copying the integer value on top of stack `a` onto stack `b`

`Work.Layout.copyIntTo a b t rr rf` copies the integer value on top of `a` onto `b`, leaving the
copy on `a` as well; `t` is scratch (its content above the boundary marker `gMark = Glyph.mk 7`
carries the reversed glyphs between the two phases).

Phase 1 (the loop of `copyIntB1`, from `Submission.Work.Layout.AA.copyIntB1_loop`) pops the glyphs
of the encoding `(Val.int k).enc` from `a` onto `t` until the terminator `Glyph.iend`, reversing
them; phase 2 (the loop of `copyIntB2`, proved here) walks `t` up to the boundary marker and pushes
every glyph onto `a` and onto `b` in turn, so that both receive the encoding `(Val.int k).enc` in
the right order again.

The encoding facts used are `Work.Layout.AA.enc_int_decomp`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Layout.AA

open HvdH

/-! ## Phase 2: the `copyIntB2` loop -/

private theorem copyIntB2_step_hit (main : Cmd) {t a b : Stk} (rr rf : Reg)
    (g : Reg → Glyph) (X : Stk → List Glyph) {DB : List Glyph}
    (ht : X t = Glyph.mk 7 :: DB) :
    ∃ s' n, Ev main (copyIntB2 t a b rr rf) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk t = Glyph.mk 7 :: DB ∧ s'.stk a = X a ∧ s'.stk b = X b ∧
      (∀ j, s'.stk j = X j) ∧ s'.reg rf = Glyph.eos := by
  have h1 : Ev main (.peek t rr) ⟨g, X⟩ ⟨Function.update g rr (Glyph.mk 7), X⟩ 1 := by
    have h := ev_peek' main t rr g X
    rw [ht, List.headD_cons] at h
    exact h
  have h2 : Ev main (.set rf Glyph.eos) ⟨Function.update g rr (Glyph.mk 7), X⟩
      ⟨Function.update (Function.update g rr (Glyph.mk 7)) rf Glyph.eos, X⟩ 1 :=
    ev_set' main rf Glyph.eos _ _
  have hbody : copyIntB2 t a b rr rf = .seq (.peek t rr) (.ite rr gMark (.set rf Glyph.eos)
      (.seq (.pop t rr) (.seq (.push a rr) (.seq (.push b rr) (.set rf Glyph.cons))))) := rfl
  refine ⟨⟨Function.update (Function.update g rr (Glyph.mk 7)) rf Glyph.eos, X⟩,
    3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody]
    exact (Ev.seq h1 (Ev.iteT (by simp [Function.update_self, Work.Layout.gMark]) h2)).mono
      (by omega)
  · omega
  · simpa using ht
  · rfl
  · rfl
  · intro j; rfl
  · simp [Function.update_self]

private theorem copyIntB2_step_miss (main : Cmd) {t a b : Stk} (hta : t ≠ a) (htb : t ≠ b)
    (hab : a ≠ b) (rr rf : Reg) (g : Reg → Glyph) (X : Stk → List Glyph)
    {h : Glyph} {Y : List Glyph}
    (ht : X t = h :: Y) (hh : h ≠ Glyph.mk 7) :
    ∃ s' n, Ev main (copyIntB2 t a b rr rf) ⟨g, X⟩ s' n ∧ n ≤ 6 ∧
      s'.stk t = Y ∧ s'.stk a = h :: X a ∧ s'.stk b = h :: X b ∧
      (∀ j, j ≠ t → j ≠ a → j ≠ b → s'.stk j = X j) ∧ s'.reg rf = Glyph.cons := by
  have h1 : Ev main (.peek t rr) ⟨g, X⟩ ⟨Function.update g rr h, X⟩ 1 := by
    have h := ev_peek' main t rr g X
    rw [ht, List.headD_cons] at h
    exact h
  have h2 : Ev main (.pop t rr) ⟨Function.update g rr h, X⟩
      ⟨Function.update (Function.update g rr h) rr h, Function.update X t Y⟩ 1 := by
    have h := ev_pop' main t rr (Function.update g rr h) X
    rw [ht, List.headD_cons, List.tail_cons] at h
    exact h
  have hbody : copyIntB2 t a b rr rf = .seq (.peek t rr) (.ite rr gMark (.set rf Glyph.eos)
      (.seq (.pop t rr) (.seq (.push a rr) (.seq (.push b rr) (.set rf Glyph.cons))))) := rfl
  refine ⟨⟨Function.update (Function.update (Function.update g rr h) rr h) rf Glyph.cons,
      Function.update
        (Function.update (Function.update X t Y) a
          ((Function.update (Function.update g rr h) rr h) rr :: Function.update X t Y a)) b
        ((Function.update (Function.update g rr h) rr h) rr ::
          Function.update (Function.update X t Y) a
            ((Function.update (Function.update g rr h) rr h) rr :: Function.update X t Y a) b)⟩,
    6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody]
    exact (Ev.seq h1 (Ev.iteF (by simpa [Function.update_self, Work.Layout.gMark] using hh)
      (Ev.seq h2 (Ev.seq (ev_push' main a rr _ _)
        (Ev.seq (ev_push' main b rr _ _) (ev_set' main rf Glyph.cons _ _)))))).mono (by omega)
  · omega
  · simp [Function.update_self, Function.update_of_ne htb, Function.update_of_ne hta]
  · simp [Function.update_self, Function.update_of_ne hab, Function.update_of_ne (Ne.symm hta)]
  · simp [Function.update_self, Function.update_of_ne (Ne.symm hab), Function.update_of_ne htb.symm]
  · intro j hjt hja hjb
    simp [Function.update_self, Function.update_of_ne hjb, Function.update_of_ne hja,
      Function.update_of_ne hjt]
  · simp [Function.update_self]

private theorem copyIntB2_loop_aux (main : Cmd) {t a b : Stk} (hta : t ≠ a) (htb : t ≠ b)
    (hab : a ≠ b) (rr rf : Reg) :
    ∀ (D DB : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      Glyph.mk 7 ∉ D → g rf = Glyph.cons → X t = D ++ Glyph.mk 7 :: DB →
      ∃ s', loopRuns main rf Glyph.cons (copyIntB2 t a b rr rf) (D.length + 1) ⟨g, X⟩ s'
          (7 * (D.length + 1)) ∧
        s'.stk t = Glyph.mk 7 :: DB ∧ s'.stk a = D.reverse ++ X a ∧
        s'.stk b = D.reverse ++ X b ∧
        (∀ j, j ≠ t → j ≠ a → j ≠ b → s'.stk j = X j) ∧ s'.reg rf = Glyph.eos := by
  intro D
  induction D with
  | nil =>
      intro DB g X hD hg ht
      obtain ⟨s', n, hev, hn, ht', ha', hb', hfr', hrf⟩ :=
        copyIntB2_step_hit main (rr := rr) (rf := rf) g X (DB := DB) (by simpa using ht)
      refine ⟨s', ?_, ?_, ?_, ?_, ?_, hrf⟩
      · exact loopRuns.succ' hg (hev.mono hn) loopRuns.zero (by omega)
      · simpa using ht'
      · simpa using ha'
      · simpa using hb'
      · intro j _ _ _; exact hfr' j
  | cons d D' ih =>
      intro DB g X hD hg ht
      have hd : d ≠ Glyph.mk 7 := by intro h; exact hD (by rw [h]; exact List.mem_cons_self)
      have hD' : Glyph.mk 7 ∉ D' := fun h => hD (List.mem_cons_of_mem d h)
      obtain ⟨s₁, n₁, hev₁, hn₁, ht₁, ha₁, hb₁, hfr₁, hr₁⟩ :=
        copyIntB2_step_miss main (hta := hta) (htb := htb) (hab := hab) (rr := rr) (rf := rf)
          g X (h := d) (Y := D' ++ Glyph.mk 7 :: DB) (by simpa using ht) hd
      obtain ⟨s₂, hrun₂, ht₂, ha₂, hb₂, hfr₂, hr₂⟩ := ih DB s₁.reg s₁.stk hD' hr₁ ht₁
      refine ⟨s₂, ?_, ht₂, ?_, ?_, ?_, hr₂⟩
      · exact loopRuns.succ' hg (hev₁.mono hn₁) hrun₂ (by simp only [List.length_cons]; omega)
      · rw [ha₂, ha₁]
        simp [List.reverse_cons, List.append_assoc]
      · rw [hb₂, hb₁]
        simp [List.reverse_cons, List.append_assoc]
      · intro j hjt hja hjb; rw [hfr₂ j hjt hja hjb, hfr₁ j hjt hja hjb]

/-! ## Main specification -/

theorem copyIntTo_ev (main : HvdH.Cmd) (a b t : HvdH.Stk) (rr rf : HvdH.Reg) (hrt : rr ≠ rf)
    (hat : a ≠ t) (hbt : b ≠ t) (hab : a ≠ b)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (k : ℕ)
    (A B DB : List HvdH.Glyph) (hD : HvdH.Glyph.mk 7 ∉ DB)
    (ha : X a = (HvdH.Val.int k).enc ++ A) (hb : X b = B) (ht : X t = HvdH.Glyph.mk 7 :: DB) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.copyIntTo a b t rr rf) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (HvdH.isz k + 1) ∧
      s'.stk a = (HvdH.Val.int k).enc ++ A ∧ s'.stk b = (HvdH.Val.int k).enc ++ B ∧
      s'.stk t = HvdH.Glyph.mk 7 :: DB ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ t → s'.stk j = X j) := by
  obtain ⟨D, hE, hDiend, hDmk, hDlen⟩ := enc_int_decomp k
  have ha' : X a = D ++ Glyph.iend :: A := by rw [ha, hE]; simp
  have hg1 : (Function.update g rf Glyph.cons) rf = Glyph.cons := by simp
  obtain ⟨s1, hrun1, ha1, ht1, hfr1, hr1⟩ :=
    copyIntB1_loop main (hat := hat) (rr := rr) (rf := rf) D A
      (Function.update g rf Glyph.cons) X hDiend hg1 ha'
  have hloop1 : Ev main (.loop rf Glyph.cons (copyIntB1 a t rr rf))
      ⟨Function.update g rf Glyph.cons, X⟩ s1 (5 * (D.length + 1) + 1) :=
    loopRuns.eval hrun1 (by rw [hr1]; decide)
  have hDmk' : Glyph.mk 7 ∉ (Glyph.iend :: D.reverse) := by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    · exact hDmk (List.mem_reverse.mp h)
  have ht1' : s1.stk t = (Glyph.iend :: D.reverse) ++ Glyph.mk 7 :: DB := by
    rw [ht1, ht]
  obtain ⟨s2, hrun2, ht2, ha2, hb2, hfr2, hr2⟩ :=
    copyIntB2_loop_aux main (hta := Ne.symm hat) (htb := Ne.symm hbt) (hab := hab)
      (rr := rr) (rf := rf) (Glyph.iend :: D.reverse) DB
      (Function.update s1.reg rf Glyph.cons) s1.stk hDmk' (by simp) ht1'
  have hloop2 : Ev main (.loop rf Glyph.cons (copyIntB2 t a b rr rf))
      ⟨Function.update s1.reg rf Glyph.cons, s1.stk⟩ s2
      (7 * ((Glyph.iend :: D.reverse).length + 1) + 1) :=
    loopRuns.eval hrun2 (by rw [hr2]; decide)
  have hset1 : Ev main (.set rf Glyph.cons) ⟨g, X⟩ ⟨Function.update g rf Glyph.cons, X⟩ 1 :=
    ev_set main rf Glyph.cons ⟨g, X⟩
  have hset2 : Ev main (.set rf Glyph.cons) s1 ⟨Function.update s1.reg rf Glyph.cons, s1.stk⟩ 1 :=
    ev_set main rf Glyph.cons s1
  have hprog : copyIntTo a b t rr rf = .seq (.set rf Glyph.cons)
      (.seq (.loop rf Glyph.cons (copyIntB1 a t rr rf))
        (.seq (.set rf Glyph.cons) (.loop rf Glyph.cons (copyIntB2 t a b rr rf)))) := rfl
  have hcost : 1 + ((5 * (D.length + 1) + 1) +
      (1 + (7 * ((Glyph.iend :: D.reverse).length + 1) + 1))) ≤ 16 * (isz (k : ℤ) + 1) := by
    have hlen : (Glyph.iend :: D.reverse).length = D.length + 1 := by simp
    rw [hlen, hDlen]; omega
  have hEv : Ev main (copyIntTo a b t rr rf) ⟨g, X⟩ s2 (16 * (isz (k : ℤ) + 1)) := by
    rw [hprog]
    exact (Ev.seq hset1 (Ev.seq hloop1 (Ev.seq hset2 hloop2))).mono hcost
  have hrev : (Glyph.iend :: D.reverse).reverse = (Val.int (k : ℤ)).enc := by
    rw [List.reverse_cons, List.reverse_reverse]
    rw [hE]
  have hsb : s1.stk b = B := by rw [hfr1 b hab.symm hbt, hb]
  refine ⟨s2, 16 * (isz (k : ℤ) + 1), hEv, le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [ha2, ha1, hrev]
  · rw [hb2, hsb, hrev]
  · rw [ht2]
  · intro j hja hjb hjt
    rw [hfr2 j hjt hja hjb, hfr1 j hja hjt]

end Work.Layout.AA
