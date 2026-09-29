import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.Base
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-- `encs` of a cons. -/
theorem encs_cons_tk (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := by
  simp [encs, List.flatten_cons]

/-- Apply a `WordR` word to a raw state whose stack 0 is `encs vs ++ R`. -/
theorem WordR.applyEv {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} (h : WordR main p P Q C) {vs : List Val} (hP : P vs)
    {g : Reg → Glyph} {X : Stk → List Glyph} {R : List Glyph} (h0 : X 0 = encs vs ++ R) :
    ∃ (out : List Val) (s' : State), Q vs out ∧ Ev main p ⟨g, X⟩ s' (C vs) ∧
      s'.stk 0 = encs out ++ R ∧ ∀ k : Stk, k ≠ 0 → s'.stk k = X k := by
  obtain ⟨out, s', n, hQ, hE, hn, h0', hfr⟩ := h vs hP ⟨g, X⟩ R h0
  exact ⟨out, s', hQ, ⟨n, hE, hn⟩, h0', hfr⟩

/-- move the top value of stack 0 to stack `b ≠ 0` -/
theorem mvVal_up {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {v : Val} {A' : List Glyph}
    {b c d : Stk} (hb : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (h0 : X 0 = v.enc ++ A') :
    ∃ s' N, Ev main (mvVal 0 b c d) ⟨g, X⟩ s' N ∧ N ≤ 16 * (vsz v + 1) ∧
      s'.stk 0 = A' ∧ s'.stk b = v.enc ++ X b ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ k : Stk, k ≠ 0 → k ≠ b → k ≠ c → k ≠ d → s'.stk k = X k) :=
  mvVal_ev_full (a := 0) (b := b) (c := c) (d := d) (v := v) (A := A') (B := X b)
    (fun h => hb h.symm) (fun h => hc0 h.symm) (fun h => hd0 h.symm) hbc hbd hcd h0 rfl

/-- move the top value of stack `a ≠ 0` to stack 0 -/
theorem mvVal_down {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {v : Val} {A' : List Glyph}
    {a c d : Stk} (ha : a ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hac : a ≠ c) (had : a ≠ d)
    (hcd : c ≠ d) (hX : X a = v.enc ++ A') :
    ∃ s' N, Ev main (mvVal a 0 c d) ⟨g, X⟩ s' N ∧ N ≤ 16 * (vsz v + 1) ∧
      s'.stk a = A' ∧ s'.stk 0 = v.enc ++ X 0 ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ k : Stk, k ≠ 0 → k ≠ a → k ≠ c → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s', N, hE, hN, hA, h0, hc, hd, hfr⟩ :=
    mvVal_ev_full (a := a) (b := 0) (c := c) (d := d) (v := v) (A := A') (B := X 0)
      ha hac had (fun h => hc0 h.symm) (fun h => hd0 h.symm) hcd hX rfl
  exact ⟨s', N, hE, hN, hA, h0, hc, hd, fun k hk hka hkc hkd => hfr k hka hk hkc hkd⟩

end Work.Layout
