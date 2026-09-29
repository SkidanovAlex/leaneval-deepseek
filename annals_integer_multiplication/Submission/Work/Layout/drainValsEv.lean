import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.mvVal_ev_full

/-!
# `Work.Layout.drainValsEv`

`Work.Layout.Sk.drainVals S T t d` moves the values sitting at the top of stack `S` one at a time
onto stack `T`, stopping as soon as the top glyph of `S` is no longer `Glyph.cons`.  The encoding
`Val.enc` of a `cons`-value starts with `Glyph.cons` (and only `cons`-values do), so the loop test
recognises "there is still a value to move"; the marker `Work.Layout.gMark` below the run makes the
loop stop at the end of the run.

Stack layout: `X S = encs vals ++ gMark :: A` (`gMark` terminates the run), `X T = B` and `t`, `d`
are the scratch stacks of `Work.Layout.mvVal`.  Each value is pushed onto `T` on top of the previous
ones, so the values arrive in reverse order: `s'.stk T = encs vals.reverse ++ B`.

This file proves the raw `Ev` statement with its cost bound; the loop is driven by `loopRuns`.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## Elementary facts about the encoding of a stack of values -/

theorem drainVals_encs_nil : encs ([] : List Val) = [] := rfl

theorem drainVals_encs_cons (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := rfl

theorem drainVals_encs_append (l₁ l₂ : List Val) : encs (l₁ ++ l₂) = encs l₁ ++ encs l₂ := by
  induction l₁ with
  | nil => simp [drainVals_encs_nil]
  | cons v vs ih =>
      show encs (v :: (vs ++ l₂)) = encs (v :: vs) ++ encs l₂
      rw [drainVals_encs_cons, drainVals_encs_cons, ih, List.append_assoc]

theorem drainVals_encs_reverse_cons (v : Val) (vs : List Val) :
    encs ((v :: vs).reverse) = encs vs.reverse ++ v.enc := by
  rw [List.reverse_cons, drainVals_encs_append, drainVals_encs_cons, drainVals_encs_nil,
    List.append_nil]

theorem drainVals_headD_encs_consval (a b : Val) (vs : List Val) (A : List Glyph) :
    (encs (Val.cons a b :: vs) ++ A).headD Glyph.eos = Glyph.cons := by
  rw [drainVals_encs_cons, List.append_assoc]
  rfl

/-- The top glyph of a run of `cons`-values is `Glyph.cons`; the run is empty iff its encoding is
empty (in which case the top glyph is the marker of the tail). -/
theorem drainVals_headD_encs {vs : List Val} {A : List Glyph}
    (h : ∀ w ∈ vs, ∃ a b : Val, w = Val.cons a b) :
    (encs vs ++ A).headD Glyph.eos = if vs = [] then A.headD Glyph.eos else Glyph.cons := by
  cases vs with
  | nil => simp [drainVals_encs_nil]
  | cons v ws =>
      obtain ⟨a, b, rfl⟩ := h v (List.mem_cons_self ..)
      rw [drainVals_headD_encs_consval, if_neg (by simp)]

/-- Cost of the whole `drainVals` loop on the run `vals`: one `mvVal` per value plus the loop tests. -/
theorem drainVals_cost_sum (vals : List Val) :
    (vals.map (fun v => 16 * (vsz v + 1) + 2)).sum
      = 16 * (vals.map vsz).sum + 18 * vals.length := by
  induction vals with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      omega

/-! ## One iteration of the loop -/

/-- One iteration of the `drainVals` loop: move the top value `v` of `S` onto `T` (`mvVal`) and
re-peek the top glyph of `S` into the loop register `rH` (so that the loop test sees the next value,
or `gMark` at the end of the run). -/
theorem drainValsBody_ev {main : Cmd} {S T t d : Stk}
    (hST : S ≠ T) (hSt : S ≠ t) (hSd : S ≠ d) (hTt : T ≠ t) (hTd : T ≠ d) (htd : t ≠ d)
    {g : Reg → Glyph} {X : Stk → List Glyph} {v : Val} {vs : List Val} {A B : List Glyph}
    (hv : ∃ a b : Val, v = Val.cons a b)
    (hvs : ∀ w ∈ vs, ∃ a b : Val, w = Val.cons a b)
    (hS : X S = encs (v :: vs) ++ gMark :: A) (hT : X T = B) :
    ∃ s' n, Ev main (.seq (mvVal S T t d) (.peek S Sk.rH)) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (vsz v + 1) + 1 ∧
      s'.stk S = encs vs ++ gMark :: A ∧ s'.stk T = v.enc ++ B ∧
      s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k : Stk, k ≠ S → k ≠ T → k ≠ t → k ≠ d → s'.stk k = X k) ∧
      s'.reg Sk.rH = (if vs = [] then gMark else Glyph.cons) := by
  obtain ⟨a₀, b₀, _⟩ := hv
  obtain ⟨s₁, n₁, hmv, hn₁, hS₁, hT₁, ht₁, hd₁, hfr₁⟩ :=
    mvVal_ev_full (main := main) (a := S) (b := T) (c := t) (d := d)
      hST hSt hSd hTt hTd htd (v := v) (A := encs vs ++ gMark :: A) (B := B)
      (by rw [hS, drainVals_encs_cons, List.append_assoc]) hT
  have hhead : (s₁.stk S).headD Glyph.eos = (if vs = [] then gMark else Glyph.cons) := by
    rw [hS₁, drainVals_headD_encs hvs]
    by_cases hv' : vs = []
    · rw [if_pos hv', if_pos hv']
      rfl
    · rw [if_neg hv', if_neg hv']
  refine ⟨⟨Function.update s₁.reg Sk.rH ((s₁.stk S).headD Glyph.eos), s₁.stk⟩, n₁ + 1,
    Ev.seq hmv (ev_peek' main S Sk.rH s₁.reg s₁.stk), by omega, hS₁, hT₁, ht₁, hd₁,
    (fun k hkS hkT hkt hkd => hfr₁ k hkS hkT hkt hkd), hhead⟩

/-! ## The loop -/

/-- The `drainVals` loop: starting with `X S = encs vs ++ gMark :: A` and the loop register already
holding the top glyph of `S`, the body runs once per element of `vs`, and the values arrive on `T`
in reverse order. -/
theorem drainValsLoop_ev {main : Cmd} {S T t d : Stk}
    (hST : S ≠ T) (hSt : S ≠ t) (hSd : S ≠ d) (hTt : T ≠ t) (hTd : T ≠ d) (htd : t ≠ d) :
    ∀ (vs : List Val) (A B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ w ∈ vs, ∃ a b : Val, w = Val.cons a b) →
      X S = encs vs ++ gMark :: A → X T = B →
      g Sk.rH = (if vs = [] then gMark else Glyph.cons) →
      ∃ s', loopRuns main Sk.rH Glyph.cons (.seq (mvVal S T t d) (.peek S Sk.rH)) vs.length
          ⟨g, X⟩ s' ((vs.map (fun w => 16 * (vsz w + 1) + 2)).sum) ∧
        s'.stk S = gMark :: A ∧ s'.stk T = encs vs.reverse ++ B ∧
        s'.stk t = X t ∧ s'.stk d = X d ∧
        (∀ k : Stk, k ≠ S → k ≠ T → k ≠ t → k ≠ d → s'.stk k = X k) ∧
        s'.reg Sk.rH = gMark := by
  intro vs
  induction vs with
  | nil =>
      intro A B g X _ hS hT hg
      refine ⟨⟨g, X⟩, loopRuns.zero, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [drainVals_encs_nil] using hS
      · simpa [drainVals_encs_nil] using hT
      · rfl
      · rfl
      · intro k _ _ _ _; rfl
      · simpa using hg
  | cons v vs ih =>
      intro A B g X hcons hS hT hg
      have hv : ∃ a b : Val, v = Val.cons a b := hcons v (List.mem_cons_self ..)
      have hvs : ∀ w ∈ vs, ∃ a b : Val, w = Val.cons a b :=
        fun w hw => hcons w (List.mem_cons_of_mem v hw)
      have hgcons : g Sk.rH = Glyph.cons := by
        rw [hg, if_neg (by simp)]
      obtain ⟨s₁, n₁, hev₁, hn₁, hS₁, hT₁, ht₁, hd₁, hfr₁, hreg₁⟩ :=
        drainValsBody_ev (main := main) hST hSt hSd hTt hTd htd hv hvs hS hT
      obtain ⟨s₂, hrun₂, hS₂, hT₂, ht₂, hd₂, hfr₂, hreg₂⟩ :=
        ih A (v.enc ++ B) s₁.reg s₁.stk hvs hS₁ hT₁ hreg₁
      have hcat : loopRuns main Sk.rH Glyph.cons (.seq (mvVal S T t d) (.peek S Sk.rH))
          (1 + vs.length) ⟨g, X⟩ s₂
          (n₁ + 1 + (vs.map (fun w => 16 * (vsz w + 1) + 2)).sum) :=
        loopRuns.concat vs.length (loopRuns.one hgcons hev₁) hrun₂
      have hcost : n₁ + 1 + (vs.map (fun w => 16 * (vsz w + 1) + 2)).sum
          ≤ ((v :: vs).map (fun w => 16 * (vsz w + 1) + 2)).sum := by
        simp only [List.map_cons, List.sum_cons]
        omega
      refine ⟨s₂, ?_, hS₂, ?_, ht₂.trans ht₁, hd₂.trans hd₁, ?_, hreg₂⟩
      · have hlen : 1 + vs.length = (v :: vs).length := by simp only [List.length_cons]; omega
        have hpos : 1 ≤ (v :: vs).length := by simp only [List.length_cons]; omega
        exact loopRuns.mono hpos (loopRuns.cast hlen hcat) hcost
      · rw [hT₂, drainVals_encs_reverse_cons, List.append_assoc]
      · intro k hkS hkT hkt hkd
        rw [hfr₂ k hkS hkT hkt hkd, hfr₁ k hkS hkT hkt hkd]

/-! ## The word -/

/-- `Work.Layout.Sk.drainVals S T t d` moves values one at a time from the top of stack `S` onto
stack `T` (via `mvVal`, scratches `t`,`d`), stopping when the top glyph of `S` is not
`HvdH.Glyph.cons`.  Here the values sitting on `S` are exactly `vals`, i.e.
`X S = HvdH.encs vals ++ Work.Layout.gMark :: A` (so `gMark` terminates the run), and every element
of `vals` is a `cons`-value (so the loop test succeeds for each of them).  `mvVal` leaves `t` and `d`
as it found them, and each value is pushed onto `T`, so the values arrive in reverse order. -/
theorem drainValsEv {main : HvdH.Cmd} {S T t d : HvdH.Stk}
    (hST : S ≠ T) (hSt : S ≠ t) (hSd : S ≠ d) (hTt : T ≠ t) (hTd : T ≠ d) (htd : t ≠ d)
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph} {vals : List HvdH.Val}
    {A B : List HvdH.Glyph}
    (hcons : ∀ v ∈ vals, ∃ a b : HvdH.Val, v = HvdH.Val.cons a b)
    (hS : X S = HvdH.encs vals ++ Work.Layout.gMark :: A) (hT : X T = B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.Sk.drainVals S T t d) ⟨g, X⟩ s' n ∧
      n ≤ 20 * ((vals.map HvdH.vsz).sum + vals.length + 1) ∧
      s'.stk S = Work.Layout.gMark :: A ∧
      s'.stk T = HvdH.encs vals.reverse ++ B ∧
      s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k : HvdH.Stk, k ≠ S → k ≠ T → k ≠ t → k ≠ d → s'.stk k = X k) := by
  have hhead : (X S).headD Glyph.eos = (if vals = [] then gMark else Glyph.cons) := by
    rw [hS, drainVals_headD_encs hcons]
    by_cases hv' : vals = []
    · rw [if_pos hv', if_pos hv']
      rfl
    · rw [if_neg hv', if_neg hv']
  have hpeek : Ev main (.peek S Sk.rH) ⟨g, X⟩
      ⟨Function.update g Sk.rH ((X S).headD Glyph.eos), X⟩ 1 := ev_peek' main S Sk.rH g X
  obtain ⟨s₁, hrun₁, hS₁, hT₁, ht₁, hd₁, hfr₁, hreg₁⟩ :=
    drainValsLoop_ev (main := main) hST hSt hSd hTt hTd htd vals A B
      (Function.update g Sk.rH ((X S).headD Glyph.eos)) X hcons hS hT
      (by rw [Function.update_self, hhead])
  have hne : s₁.reg Sk.rH ≠ Glyph.cons := by
    rw [hreg₁]
    exact gMark_ne_cons
  obtain ⟨n₂, hloop, hn₂⟩ := loopRuns.eval hrun₁ hne
  obtain ⟨np, hpeekEv, hnp⟩ := hpeek
  have hcost := drainVals_cost_sum vals
  refine ⟨s₁, np + n₂, ⟨np + n₂, ?_, le_rfl⟩, by omega, hS₁, hT₁, ht₁, hd₁, hfr₁⟩
  unfold Sk.drainVals
  exact Eval.seq hpeekEv hloop

end Work.Layout
