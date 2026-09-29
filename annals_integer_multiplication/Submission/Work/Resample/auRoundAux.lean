import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.pbKit2
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.ifNil
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

/-!
# Auxiliary words and size lemmas for the resampling round word (`Work.Resample.auRoundWord`)

* `auRoundFr` — the FRAME condition on the non-zero stacks other than `1,2,3`;
* `auRoundPop`, `auRoundPush` — value words moving a value between stack `0` and a non-zero stack,
  leaving the rest of that stack in place (`pbW1`/`pbW2` of `pbWords`, generalised to a non-empty
  tail; proved here from `Work.Layout.mvVal`, so this module does not depend on `pbWords`);
* `auRoundIfNil` — the `WordM`-level `ifNil` (a branch on the top value of stack `0`, with both
  branches allowed to touch the other stacks);
* value facts (`ofList`) and size bounds used in the cost estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-- The stacks that the round word is allowed to touch are `0,1,2,3`; `auRoundFr a b` records that
the description `b` agrees with `a` on every other stack. -/
def auRoundFr (a b : Stk → List Val) : Prop := ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → b k = a k

/-- Pop the top value of a non-zero stack `src` onto stack `0`, leaving the tail of `src`. -/
theorem auRoundPop (src : Stk) (hsrc : src ≠ 0) :
    ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val) (L rest : List Val),
      WordM main prog
        (fun vs a => vs = rest ∧ a src = v :: L)
        (fun vs a out b => out = v :: vs ∧ b src = L ∧
          (∀ k, k ≠ 0 → k ≠ src → b k = a k))
        (fun _ _ => Kc * (vsz v + 1)) := by
  obtain ⟨c, d, hcd, hc0, hcs, hd0, hds⟩ := pbScratch2 src
  refine ⟨Work.Layout.mvVal src 0 c d, 16, ?_⟩
  intro main v L rest vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  rw [hvs] at h0
  rw [hvs]
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs rest ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have haX : X src = v.enc ++ (encs L ++ Bg src) := by
    rw [hkX src hsrc, ha, Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s', N, hev, hN, hsA, hsB, hfr⟩ :=
    pbMvValEv (main := main) (a := src) (b := 0) (c := c) (d := d)
      (hab := hsrc) (hac := Ne.symm hcs) (had := Ne.symm hds)
      (hbc := Ne.symm hc0) (hbd := Ne.symm hd0) (hcd := hcd)
      (g := g) (X := X) (v := v) (A := encs L ++ Bg src) (B := encs rest ++ R) haX h0X
  obtain ⟨n, heval, hnN⟩ := hev
  refine ⟨v :: rest, Function.update a src L, s', n, ⟨rfl, by simp, ?_⟩, heval, le_trans hnN hN,
    ?_, ?_⟩
  · intro k hk0 hks
    simp only [Function.update_of_ne hks]
  · rw [hsB, Work.Kernel.encs_cons]
    simp only [List.append_assoc]
  · intro k hk0
    by_cases hks : k = src
    · rw [hks]; simp only [Function.update_self, hsA]
    · rw [Function.update_of_ne hks, hfr k hks hk0, hkX k hk0]

/-- Move the top value of stack `0` onto a non-zero stack `tgt`. -/
theorem auRoundPush (tgt : Stk) (htgt : tgt ≠ 0) :
    ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val) (rest : List Val) (L : List Val),
      WordM main prog
        (fun vs a => vs = v :: rest ∧ a tgt = L)
        (fun vs a out b => out = rest ∧ b tgt = v :: L ∧
          (∀ k, k ≠ 0 → k ≠ tgt → b k = a k))
        (fun _ _ => Kc * (vsz v + 1)) := by
  obtain ⟨c, d, hcd, hc0, hct, hd0, hdt⟩ := pbScratch2 tgt
  refine ⟨Work.Layout.mvVal 0 tgt c d, 16, ?_⟩
  intro main v rest L vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = encs vs ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = encs (a k) ++ Bg k := hk
  have h00 : X 0 = v.enc ++ (encs rest ++ R) := by
    rw [h0X, hvs, Work.Kernel.encs_cons, List.append_assoc]
  have htgtX : X tgt = encs L ++ Bg tgt := by rw [hkX tgt htgt, ha]
  obtain ⟨s', N, hev, hN, h0', htgt', hfr⟩ :=
    pbMvValEv (main := main) (a := 0) (b := tgt) (c := c) (d := d)
      (hab := Ne.symm htgt) (hac := Ne.symm hc0) (had := Ne.symm hd0)
      (hbc := Ne.symm hct) (hbd := Ne.symm hdt) (hcd := hcd)
      (g := g) (X := X) (v := v) (A := encs rest ++ R) (B := encs L ++ Bg tgt) h00 htgtX
  obtain ⟨n, heval, hnN⟩ := hev
  refine ⟨rest, Function.update a tgt (v :: L), s', n, ⟨rfl, by simp, ?_⟩, heval, le_trans hnN hN,
    ?_, ?_⟩
  · intro k hk0 hkt
    simp only [Function.update_of_ne hkt]
  · rw [h0']
  · intro k hk0
    by_cases hkt : k = tgt
    · rw [hkt]; simp only [Function.update_self, htgt', Work.Kernel.encs_cons, List.append_assoc]
    · rw [Function.update_of_ne hkt, hfr k hk0 hkt, hkX k hk0]

/-- A `WordM`-level `ifNil`: branch on whether the top value of stack `0` is `nil` (the `nil`
encoding is a single glyph, so a raw `peek`/`pop` decides it), with both branches allowed to touch
the other stacks. -/
theorem auRoundIfNil :
    ∃ (comb : Cmd → Cmd → Cmd) (K : ℕ), ∀ (main q₁ q₂ : Cmd) (v : Val) (rest : List Val)
      (P₁ P₂ : (Stk → List Val) → Prop)
      (Q₁ Q₂ : (Stk → List Val) → List Val → (Stk → List Val) → Prop) (c₁ c₂ : ℕ),
      (v = .nil → WordM main q₁ (fun vs a => vs = rest ∧ P₁ a)
        (fun _ a out b => Q₁ a out b) (fun _ _ => c₁)) →
      (v ≠ .nil → WordM main q₂ (fun vs a => vs = v :: rest ∧ P₂ a)
        (fun _ a out b => Q₂ a out b) (fun _ _ => c₂)) →
      WordM main (comb q₁ q₂)
        (fun vs a => vs = v :: rest ∧ (v = .nil → P₁ a) ∧ (v ≠ .nil → P₂ a))
        (fun _ a out b => (v = .nil → Q₁ a out b) ∧ (v ≠ .nil → Q₂ a out b))
        (fun _ _ => K + max c₁ c₂) := by
  refine ⟨fun q₁ q₂ => Cmd.seq (Cmd.peek 0 0)
      (Cmd.ite 0 Glyph.nil (Cmd.seq (Cmd.pop 0 0) q₁) q₂), 3, ?_⟩
  intro main q₁ q₂ v rest P₁ P₂ Q₁ Q₂ c₁ c₂ h₁ h₂ vs a hpre s R Bg h0 hk
  obtain ⟨hvs, hP₁, hP₂⟩ := hpre
  subst hvs
  have hpeekreg : (State.tPeek s 0 0).reg 0 = (encs (v :: rest) ++ R).headD Glyph.eos := by
    rw [Work.Kernel.ifNil_tPeek_reg, h0]
  have hpeekstk : (State.tPeek s 0 0).stk 0 = encs (v :: rest) ++ R := by
    rw [Work.Kernel.ifNil_tPeek_stk0]; exact h0
  have hpeekk : ∀ k : Stk, k ≠ 0 → (State.tPeek s 0 0).stk k = encs (a k) ++ Bg k := by
    intro k hk0; rw [Work.Kernel.ifNil_tPeek_stk]; exact hk k hk0
  by_cases hv : v = .nil
  · have hhead : (State.tPeek s 0 0).reg 0 = Glyph.nil := by
      rw [hpeekreg]; exact Work.Kernel.ifNil_headD_nil v hv rest R
    have hpop0 : (State.tPop (State.tPeek s 0 0) 0 0).stk 0 = encs rest ++ R := by
      rw [Work.Kernel.ifNil_tPop_stk0, hpeekstk, hv]
      exact Work.Kernel.ifNil_tail_encs_nil rest R
    have hpopk : ∀ k : Stk, k ≠ 0 →
        (State.tPop (State.tPeek s 0 0) 0 0).stk k = encs (a k) ++ Bg k := by
      intro k hk0; rw [Work.Kernel.ifNil_tPop_stk _ hk0]; exact hpeekk k hk0
    obtain ⟨out, b, s', n, hQ, hev, hn, hstk, hk'⟩ :=
      h₁ hv rest a ⟨rfl, hP₁ hv⟩ (State.tPop (State.tPeek s 0 0) 0 0) R Bg hpop0 hpopk
    refine ⟨out, b, s', 1 + (1 + (n + 1)), ⟨fun _ => hQ, fun hne => absurd hv hne⟩, ?_, ?_, hstk,
      hk'⟩
    · exact Eval.seq (Eval.peek 0 0 s)
        (Eval.iteT hhead (Eval.seq (Eval.pop 0 0 (State.tPeek s 0 0)) hev))
    · have hn' : n ≤ c₁ := hn
      have hmax : c₁ ≤ max c₁ c₂ := Nat.le_max_left _ _
      show 1 + (1 + (n + 1)) ≤ 3 + max c₁ c₂
      omega
  · have hhead : (State.tPeek s 0 0).reg 0 ≠ Glyph.nil := by
      rw [hpeekreg]; exact Work.Kernel.ifNil_headD_ne v hv rest R
    obtain ⟨out, b, s', n, hQ, hev, hn, hstk, hk'⟩ :=
      h₂ hv (v :: rest) a ⟨rfl, hP₂ hv⟩ (State.tPeek s 0 0) R Bg hpeekstk hpeekk
    refine ⟨out, b, s', 1 + (n + 1), ⟨fun heq => absurd heq hv, fun _ => hQ⟩, ?_, ?_, hstk, hk'⟩
    · exact Eval.seq (Eval.peek 0 0 s) (Eval.iteF hhead hev)
    · have hn' : n ≤ c₂ := hn
      have hmax : c₂ ≤ max c₁ c₂ := Nat.le_max_right _ _
      show 1 + (n + 1) ≤ 3 + max c₁ c₂
      omega

/-! ## Value facts -/

theorem auRound_vsz_cons (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, List.length_cons, List.length_append]

theorem auRound_vsz_nil : vsz (.nil : Val) = 1 := rfl

/-- `ofList` is `nil` only for the empty list. -/
theorem auRound_ofList_eq_nil_iff (W : List Val) : ofList W = .nil ↔ W = [] := by
  constructor
  · intro h
    cases W with
    | nil => rfl
    | cons v vs => exact absurd h (by simp [ofList])
  · intro h; subst h; rfl

theorem auRound_ofList_ne_nil (W : List Val) (h : W ≠ []) : ofList W ≠ .nil :=
  fun hh => h ((auRound_ofList_eq_nil_iff W).mp hh)

/-- Head and tail of `ofList` for a non-empty list. -/
theorem auRound_ofList_drop_one (W : List Val) (h : W ≠ []) :
    ofList W = .cons (W.headD .nil) (ofList (W.drop 1)) := by
  cases W with
  | nil => exact absurd rfl h
  | cons v vs => rfl

theorem auRound_ofList_singleton (v : Val) : ofList [v] = .cons v .nil := rfl

/-- Sizes: `vsz` of a list value. -/
theorem auRound_vsz_ofList_le (W : List Val) (B : ℕ) (h : ∀ v ∈ W, vsz v ≤ B) :
    vsz (ofList W) ≤ 3 * ((W.length + 1) * (B + 1) + 1) := by
  induction W with
  | nil =>
    show (1:ℕ) ≤ 3 * ((0 + 1) * (B + 1) + 1)
    omega
  | cons v vs ih =>
    have hv : vsz v ≤ B := h v (by simp)
    have hvs : ∀ w ∈ vs, vsz w ≤ B := fun w hw => h w (by simp [hw])
    have hih := ih hvs
    rw [show ofList (v :: vs) = .cons v (ofList vs) from rfl, auRound_vsz_cons, List.length_cons]
    nlinarith [hv, hih]

theorem auRound_isz_le_three (g : ℕ) (h : g ≤ 1) : isz (g : ℤ) ≤ 3 := by
  interval_cases g <;> decide

end Work.Resample
