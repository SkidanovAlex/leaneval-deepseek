import Mathlib
import Submission.Work.Layout.flattenDefs
import Submission.Work.Layout.mvVal_ev_full

/-!
# `Layout.flattenInnerLoop`: the inner (per-inner-list) loop of `Work.Layout.flattenProg`

`Work.Layout.flatInnerBody` is the body of the loop that consumes one inner list: while the top
glyph of stack 2 is `Glyph.cons`, pop it and move the element (a whole `Val`) to stack 1; at
`Glyph.nil` stop (set the loop flag to `eos`).

This file proves that starting from
`X 2 = (ofList ys).enc ++ A`, `X 1 = encs arr ++ gMark :: B`
the loop runs `ys.length + 1` times at cost `scanCost ys`, ending with
`s'.stk 2 = (ofList []).enc ++ A`, `s'.stk 1 = encs (ys.reverse ++ arr) ++ gMark :: B`,
the scratch stacks 3, 4 restored, and the flag `rFlatIn` equal to `eos`.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## The two one-step lemmas for the inner-loop body -/

/-- the current inner list is exhausted (its encoding starts with `nil`): the body sets the flag to
`eos` and changes nothing else. -/
theorem flattenInnerLoop_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {A : List Glyph} (h2 : X 2 = (ofList ([] : List Val)).enc ++ A) :
    ∃ s' n, Ev main flatInnerBody ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk 2 = X 2 ∧ s'.stk 1 = X 1 ∧ s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧
      s'.reg rFlatIn = Glyph.eos := by
  have hhead : (X 2).headD Glyph.eos = Glyph.nil := by rw [h2]; rfl
  have h1 := ev_peek' (main := main) 2 rA g X
  rw [hhead] at h1
  have h2ev : Ev main (.ite rA Glyph.nil (.set rFlatIn Glyph.eos)
      (.seq (.pop 2 rB) (.seq (mvVal 2 1 3 4) (.set rFlatIn Glyph.cons))))
      ⟨Function.update g rA Glyph.nil, X⟩
      ⟨Function.update (Function.update g rA Glyph.nil) rFlatIn Glyph.eos, X⟩ 2 :=
    Ev.iteT (by simp) (ev_set' (main := main) rFlatIn Glyph.eos _ X)
  have h3 : Ev main flatInnerBody ⟨g, X⟩
      ⟨Function.update (Function.update g rA Glyph.nil) rFlatIn Glyph.eos, X⟩ 3 := by
    unfold flatInnerBody
    exact Ev.seq h1 h2ev
  exact ⟨_, _, h3, by omega, rfl, rfl, rfl, rfl, by simp⟩

/-- there is still an element in the current inner list: pop the leading `cons` glyph of stack 2,
move the element onto the top of stack 1, and set the flag to `cons`. -/
theorem flattenInnerLoop_cons {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {y : Val} {ys arr : List Val} {A B : List Glyph}
    (h2 : X 2 = (ofList (y :: ys)).enc ++ A) (h1 : X 1 = encs arr ++ gMark :: B) :
    ∃ s' n, Ev main flatInnerBody ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz y + 1) + 4 ∧
      s'.stk 2 = (ofList ys).enc ++ A ∧ s'.stk 1 = encs (y :: arr) ++ gMark :: B ∧
      s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧ s'.reg rFlatIn = Glyph.cons := by
  have hhead : (X 2).headD Glyph.eos = Glyph.cons := by rw [h2]; rfl
  have htail : (X 2).tail = y.enc ++ ((ofList ys).enc ++ A) := by
    rw [h2, ofList_enc_cons, List.cons_append, List.tail_cons, List.append_assoc]
  have hpeek := ev_peek' (main := main) 2 rA g X
  rw [hhead] at hpeek
  have hpop : Ev main (.pop 2 rB) ⟨Function.update g rA Glyph.cons, X⟩
      ⟨Function.update (Function.update g rA Glyph.cons) rB Glyph.cons,
        Function.update X 2 (X 2).tail⟩ 1 := by
    have h := ev_pop' (main := main) 2 rB (Function.update g rA Glyph.cons) X
    rw [hhead] at h
    exact h
  obtain ⟨s₃, n₃, hmv, hn₃, h3a, h3b, h3c, h3d, -⟩ :=
    mvVal_ev_full (main := main) (a := 2) (b := 1) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update (Function.update g rA Glyph.cons) rB Glyph.cons)
      (X := Function.update X 2 (X 2).tail) (v := y)
      (A := (ofList ys).enc ++ A) (B := encs arr ++ gMark :: B)
      (by simp only [stkFn_same, htail])
      (by simp only [stkFn_ne X (by decide : (1 : Stk) ≠ 2), h1])
  have hset : Ev main (.set rFlatIn Glyph.cons) s₃
      ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩ 1 :=
    ev_set' (main := main) rFlatIn Glyph.cons s₃.reg s₃.stk
  have hbranch : Ev main (.seq (.pop 2 rB) (.seq (mvVal 2 1 3 4) (.set rFlatIn Glyph.cons)))
      ⟨Function.update g rA Glyph.cons, X⟩ ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩
      (1 + (n₃ + 1)) :=
    Ev.seq hpop (Ev.seq hmv hset)
  have hite : Ev main (.ite rA Glyph.nil (.set rFlatIn Glyph.eos)
      (.seq (.pop 2 rB) (.seq (mvVal 2 1 3 4) (.set rFlatIn Glyph.cons))))
      ⟨Function.update g rA Glyph.cons, X⟩ ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩
      ((1 + (n₃ + 1)) + 1) :=
    Ev.iteF (by simp) hbranch
  have hbody : Ev main flatInnerBody ⟨g, X⟩
      ⟨Function.update s₃.reg rFlatIn Glyph.cons, s₃.stk⟩
      (1 + ((1 + (n₃ + 1)) + 1)) := by
    unfold flatInnerBody
    exact Ev.seq hpeek hite
  have hle : 1 + ((1 + (n₃ + 1)) + 1) ≤ 16 * (vsz y + 1) + 4 := by omega
  obtain ⟨n, hev, hle'⟩ := hbody.mono hle
  refine ⟨_, n, ⟨n, hev, le_rfl⟩, hle', ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3a]
  · rw [h3b]
    simp only [encs_cons', List.append_assoc]
  · rw [h3c]
    exact Function.update_of_ne (by decide : (3 : Stk) ≠ 2) (X 2).tail X
  · rw [h3d]
    exact Function.update_of_ne (by decide : (4 : Stk) ≠ 2) (X 2).tail X
  · simp

/-! ## The loop -/

theorem flattenInnerLoop {main : HvdH.Cmd} :
    ∀ (ys : List HvdH.Val) (arr : List HvdH.Val) (A B : List HvdH.Glyph)
      (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      g Work.Layout.rFlatIn = HvdH.Glyph.cons →
      X 2 = (HvdH.ofList ys).enc ++ A →
      X 1 = HvdH.encs arr ++ Work.Layout.gMark :: B →
      ∃ s', Work.Layout.loopRuns main Work.Layout.rFlatIn HvdH.Glyph.cons
          Work.Layout.flatInnerBody (ys.length + 1) ⟨g, X⟩ s' (Work.Layout.scanCost ys) ∧
        s'.stk 2 = (HvdH.ofList ([] : List HvdH.Val)).enc ++ A ∧
        s'.stk 1 = HvdH.encs (ys.reverse ++ arr) ++ Work.Layout.gMark :: B ∧
        s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧
        s'.reg Work.Layout.rFlatIn = HvdH.Glyph.eos := by
  intro ys
  induction ys with
  | nil =>
      intro arr A B g X hg h2 h1
      obtain ⟨s', n, hev, hn, h2', h1', h3', h4', hr'⟩ :=
        flattenInnerLoop_stop (main := main) (g := g) (X := X) (A := A) h2
      have hcost : n + 1 ≤ scanCost ([] : List Val) := by
        simp only [scanCost, List.map_nil, List.sum_nil]
        omega
      refine ⟨s', loopRuns.mono (k := 1) le_rfl (loopRuns.one hg hev) hcost, ?_, ?_, h3', h4', hr'⟩
      · rw [h2', h2]
      · simpa [h1'] using h1
  | cons y ys ih =>
      intro arr A B g X hg h2 h1
      obtain ⟨s₁, n₁, hev₁, hn₁, h2₁, h1₁, h3₁, h4₁, hr₁⟩ :=
        flattenInnerLoop_cons (main := main) (g := g) (X := X) (y := y) (ys := ys) (arr := arr)
          (A := A) (B := B) h2 h1
      obtain ⟨s₂, hrun₂, h2₂, h1₂, h3₂, h4₂, hr₂⟩ :=
        ih (y :: arr) A B s₁.reg s₁.stk hr₁ h2₁ h1₁
      have hcost : (n₁ + 1) + scanCost ys ≤ scanCost (y :: ys) := by
        simp only [scanCost, List.map_cons, List.sum_cons]
        omega
      have hcat := loopRuns.concat (ys.length + 1) (loopRuns.one hg hev₁) hrun₂
      have hcat1 : loopRuns main rFlatIn Glyph.cons flatInnerBody ((y :: ys).length + 1)
          ⟨g, X⟩ s₂ (n₁ + 1 + scanCost ys) :=
        loopRuns.cast (by simp only [List.length_cons]; omega) hcat
      have hcat2 : loopRuns main rFlatIn Glyph.cons flatInnerBody ((y :: ys).length + 1)
          ⟨g, X⟩ s₂ (scanCost (y :: ys)) :=
        loopRuns.mono (by simp only [List.length_cons]; omega) hcat1 hcost
      have hrev : ys.reverse ++ (y :: arr) = (y :: ys).reverse ++ arr := by
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      refine ⟨s₂, hcat2, h2₂, ?_, ?_, ?_, hr₂⟩
      · rw [h1₂, hrev]
      · rw [h3₂, h3₁]
      · rw [h4₂, h4₁]

end Work.Layout
