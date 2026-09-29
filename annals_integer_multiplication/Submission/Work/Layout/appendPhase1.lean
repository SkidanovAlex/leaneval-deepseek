import Mathlib
import Submission.Work.Layout.appendDefs

/-!
# Layout area: phase 1 of the append word

`Work.Layout.p1` walks the encoding `lstEnc zs` of `ofList zs` on stack 2 and moves the elements,
each preceded by the marker `gMark`, onto the element stack 1 (so that they end up in reverse order).
It is the first loop of `Work.Layout.appendP` (see `appendDefs.lean` for the surrounding phases).

* `p1Body_cons` / `p1Body_nil`: one iteration of the loop body, in its two cases;
* `p1_loop`: the loop invariant over a list of values (an induction on `zs`).

Costs.  `lstEnc zs` is `cons, zs₀.enc, cons, zs₁.enc, …, nil`, so the loop performs `zs.length + 1`
iterations: one `cons` iteration per element (cost `≤ 23 + 16 * vsz v`, dominated by the `mvVal`
of the element) and one final `nil` iteration (cost `≤ 5`).  The budget `22 * (vsz (ofList zs) + 1)`
covers the loop (`vsz (ofList zs) = (zs.map vsz).sum + zs.length + 1` is large enough), and
`40 * (vsz (ofList zs) + 1) + 2` covers `set rFl cons ; loop ; failing test`.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## The two cases of the loop body -/

set_option maxHeartbeats 800000 in
/-- `p1Cons`: pop the `cons` glyph, move the element to stack 1 behind its marker `gMark`. -/
theorem p1Cons_ev {main : Cmd} {v : Val} {A B : List Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} (h2 : X 2 = Glyph.cons :: (v.enc ++ A)) (h1 : X 1 = B) :
    ∃ s' n, Ev main p1Cons ⟨g, X⟩ s' n ∧ n ≤ 20 + 16 * vsz v ∧
      s'.stk 2 = A ∧ s'.stk 1 = gMark :: (v.enc ++ B) ∧
      s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧ s'.reg rFl = Glyph.cons := by
  have hp : Ev main (.pop 2 rA) ⟨g, X⟩
      ⟨Function.update g rA ((X 2).headD Glyph.eos), Function.update X 2 (X 2).tail⟩ 1 :=
    ev_pop' main 2 rA g X
  have hp2 : (Function.update X 2 (X 2).tail) 2 = v.enc ++ A := by
    rw [Function.update_self, h2]; rfl
  have hp1 : (Function.update X 2 (X 2).tail) 1 = B := by
    rw [Function.update_of_ne (by decide : (1 : Stk) ≠ 2)]; exact h1
  obtain ⟨s₂, n₂, hmv, hn₂, h2₂, h1₂, h3₂, h4₂, _⟩ :=
    mvVal_ev_all (main := main) (a := 2) (b := 1) (c := 3) (d := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (v := v) (A := A) (B := B)
      (g := Function.update g rA ((X 2).headD Glyph.eos))
      (X := Function.update X 2 (X 2).tail) hp2 hp1
  obtain ⟨s₃, n₃, hpu, hn₃, h3₁, h3fr, -, -⟩ :=
    pushConst_ev (main := main) (k := 1) (cst := gMark) (g := s₂.reg) (X := s₂.stk)
  have hset : Ev main (.set rFl Glyph.cons) ⟨s₃.reg, s₃.stk⟩
      ⟨Function.update s₃.reg rFl Glyph.cons, s₃.stk⟩ 1 := ev_set' main rFl Glyph.cons s₃.reg s₃.stk
  have hmain : Ev main p1Cons ⟨g, X⟩
      ⟨Function.update s₃.reg rFl Glyph.cons, s₃.stk⟩ (1 + (n₂ + (n₃ + 1))) := by
    unfold p1Cons
    simp only [seqs]
    refine Ev.seq' (C₂ := n₂ + (n₃ + 1)) (C := 1 + (n₂ + (n₃ + 1))) hp
      (Ev.seq' (C₂ := n₃ + 1) (C := n₂ + (n₃ + 1)) hmv
        (Ev.seq' (C := n₃ + 1) hpu hset (by omega)) (by omega)) (by omega)
  refine ⟨⟨Function.update s₃.reg rFl Glyph.cons, s₃.stk⟩, 1 + (n₂ + (n₃ + 1)), hmain,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hhn₂ : n₂ ≤ 16 * (vsz v + 1) := hn₂
    have hhn₃ : n₃ ≤ 2 := hn₃
    omega
  · rw [h3fr 2 (by decide), h2₂]
  · rw [h3₁, h1₂]
  · rw [h3fr 3 (by decide), h3₂, Function.update_of_ne (by decide : (3 : Stk) ≠ 2)]
  · rw [h3fr 4 (by decide), h4₂, Function.update_of_ne (by decide : (4 : Stk) ≠ 2)]
  · rfl

set_option maxHeartbeats 800000 in
/-- One `cons` iteration of the loop body. -/
theorem p1Body_cons {main : Cmd} {v : Val} {A B : List Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} (h2 : X 2 = Glyph.cons :: (v.enc ++ A)) (h1 : X 1 = B) :
    ∃ s' n, Ev main p1Body ⟨g, X⟩ s' n ∧ n ≤ 22 + 16 * vsz v ∧
      s'.stk 2 = A ∧ s'.stk 1 = gMark :: (v.enc ++ B) ∧
      s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧ s'.reg rFl = Glyph.cons := by
  have hpk : Ev main (.peek 2 rA) ⟨g, X⟩
      ⟨Function.update g rA ((X 2).headD Glyph.eos), X⟩ 1 := ev_peek' main 2 rA g X
  have hreg : (Function.update g rA ((X 2).headD Glyph.eos)) rA = Glyph.cons := by
    rw [Function.update_self, h2]; rfl
  obtain ⟨s₁, n₁, hb, hn₁, h2₁, h1₁, h3₁, h4₁, hr₁⟩ :=
    p1Cons_ev (main := main) (v := v) (A := A) (B := B)
      (g := Function.update g rA ((X 2).headD Glyph.eos)) (X := X) h2 h1
  have hite : Ev main (.ite rA Glyph.cons p1Cons p1Nil)
      ⟨Function.update g rA ((X 2).headD Glyph.eos), X⟩ s₁ (n₁ + 1) :=
    Ev.iteT hreg hb
  have hbdy : Ev main p1Body ⟨g, X⟩ s₁ (1 + (n₁ + 1)) := by
    unfold p1Body
    simp only [seqs]
    exact Ev.seq' (C₂ := n₁ + 1) (C := 1 + (n₁ + 1)) hpk hite (by omega)
  refine ⟨s₁, 1 + (n₁ + 1), hbdy, ?_, h2₁, h1₁, h3₁, h4₁, hr₁⟩
  · have hhn₁ : n₁ ≤ 20 + 16 * vsz v := hn₁
    omega

set_option maxHeartbeats 800000 in
/-- The final (`nil`) iteration of the loop body: consume the terminator and stop. -/
theorem p1Body_nil {main : Cmd} {A B : List Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} (h2 : X 2 = Glyph.nil :: A) (h1 : X 1 = B) :
    ∃ s' n, Ev main p1Body ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk 2 = A ∧ s'.stk 1 = B ∧ s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧
      s'.reg rFl = Glyph.eos := by
  have hpk : Ev main (.peek 2 rA) ⟨g, X⟩
      ⟨Function.update g rA ((X 2).headD Glyph.eos), X⟩ 1 := ev_peek' main 2 rA g X
  have hreg : (Function.update g rA ((X 2).headD Glyph.eos)) rA ≠ Glyph.cons := by
    simp [h2]
  have hpop : Ev main (.pop 2 rA)
      ⟨Function.update g rA ((X 2).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g rA ((X 2).headD Glyph.eos)) rA ((X 2).headD Glyph.eos),
        Function.update X 2 (X 2).tail⟩ 1 :=
    ev_pop' main 2 rA (Function.update g rA ((X 2).headD Glyph.eos)) X
  have hset : Ev main (.set rFl Glyph.eos)
      ⟨Function.update (Function.update g rA ((X 2).headD Glyph.eos)) rA ((X 2).headD Glyph.eos),
        Function.update X 2 (X 2).tail⟩
      ⟨Function.update (Function.update (Function.update g rA ((X 2).headD Glyph.eos)) rA
          ((X 2).headD Glyph.eos)) rFl Glyph.eos,
        Function.update X 2 (X 2).tail⟩ 1 :=
    ev_set' main rFl Glyph.eos _ _
  have hnil : Ev main p1Nil ⟨Function.update g rA ((X 2).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update (Function.update g rA ((X 2).headD Glyph.eos)) rA
          ((X 2).headD Glyph.eos)) rFl Glyph.eos,
        Function.update X 2 (X 2).tail⟩ (1 + 1) := by
    unfold p1Nil
    simp only [seqs]
    exact Ev.seq' (C := 1 + 1) hpop hset (by omega)
  have hite : Ev main (.ite rA Glyph.cons p1Cons p1Nil)
      ⟨Function.update g rA ((X 2).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update (Function.update g rA ((X 2).headD Glyph.eos)) rA
          ((X 2).headD Glyph.eos)) rFl Glyph.eos,
        Function.update X 2 (X 2).tail⟩ (1 + 1 + 1) :=
    Ev.iteF hreg hnil
  have hbdy : Ev main p1Body ⟨g, X⟩
      ⟨Function.update (Function.update (Function.update g rA ((X 2).headD Glyph.eos)) rA
          ((X 2).headD Glyph.eos)) rFl Glyph.eos,
        Function.update X 2 (X 2).tail⟩ (1 + (1 + (1 + 1))) := by
    unfold p1Body
    simp only [seqs]
    exact Ev.seq' (C₂ := 1 + (1 + 1)) (C := 1 + (1 + (1 + 1))) hpk hite (by omega)
  refine ⟨⟨Function.update (Function.update (Function.update g rA ((X 2).headD Glyph.eos)) rA
          ((X 2).headD Glyph.eos)) rFl Glyph.eos,
        Function.update X 2 (X 2).tail⟩, _, hbdy, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h2]
  · simp [h1]
  · simp
  · simp
  · rfl

/-! ## The loop -/

set_option maxHeartbeats 1600000 in
/-- Phase 1 loop, from `lstEnc zs ++ C2` on stack 2 and `elsEnc acc (gSent :: C1)` on stack 1:
after `zs.length + 1` iterations stack 1 holds `elsEnc (zs.reverse ++ acc) (gSent :: C1)` and stack 2
holds `C2`; stacks 3 and 4 are restored and `reg rFl` ends at `eos`. -/
theorem p1_loop {main : Cmd} (zs acc : List Val) (C1 C2 : List Glyph) (g : Reg → Glyph)
    (X : Stk → List Glyph) (h2 : X 2 = lstEnc zs ++ C2)
    (h1 : X 1 = elsEnc acc (gSent :: C1)) (hr : g rFl = Glyph.cons) :
    ∃ s', loopRuns main rFl Glyph.cons p1Body (zs.length + 1) ⟨g, X⟩ s'
        (22 * (vsz (ofList zs) + 1)) ∧
      s'.stk 1 = elsEnc (zs.reverse ++ acc) (gSent :: C1) ∧ s'.stk 2 = C2 ∧
      s'.stk 3 = X 3 ∧ s'.stk 4 = X 4 ∧ s'.reg rFl = Glyph.eos := by
  induction zs generalizing acc g X with
  | nil =>
      obtain ⟨s₁, n₁, hb, hn₁, h2₁, h1₁, h3₁, h4₁, hr₁⟩ :=
        p1Body_nil (main := main) (A := C2) (B := elsEnc acc (gSent :: C1))
          (g := g) (X := X) h2 h1
      refine ⟨s₁, ?_, ?_, h2₁, h3₁, h4₁, hr₁⟩
      · refine loopRuns.mono (by omega) (loopRuns.one hr hb) ?_
        have hhn₁ : n₁ ≤ 4 := hn₁
        have hvs : vsz (ofList ([] : List Val)) = 1 := by
          simp [ofList, vsz, Val.enc]
        rw [hvs]
        omega
      · rw [h1₁]
        simp
  | cons v zs ih =>
      have h2' : X 2 = Glyph.cons :: (v.enc ++ (lstEnc zs ++ C2)) := by
        rw [h2, lstEnc_cons_append]
      obtain ⟨s₁, n₁, hb, hn₁, h2₁, h1₁, h3₁, h4₁, hr₁⟩ :=
        p1Body_cons (main := main) (v := v) (A := lstEnc zs ++ C2)
          (B := elsEnc acc (gSent :: C1)) (g := g) (X := X) h2' h1
      have h1₁' : s₁.stk 1 = elsEnc (v :: acc) (gSent :: C1) := by
        rw [h1₁]
        simp [elsEnc_cons]
      obtain ⟨s₂, hrun₂, h1₂, h2₂, h3₂, h4₂, hr₂⟩ :=
        ih (acc := v :: acc) (g := s₁.reg) (X := s₁.stk) h2₁ h1₁' hr₁
      have hone : loopRuns main rFl Glyph.cons p1Body 1 ⟨g, X⟩ s₁ (n₁ + 1) :=
        loopRuns.one hr hb
      have hcat : loopRuns main rFl Glyph.cons p1Body ((v :: zs).length + 1) ⟨g, X⟩ s₂
          ((n₁ + 1) + 22 * (vsz (ofList zs) + 1)) :=
        loopRuns.cast (by simp only [List.length_cons]; omega)
          (loopRuns.concat (zs.length + 1) hone hrun₂)
      refine ⟨s₂, ?_, ?_, h2₂, h3₂.trans h3₁, h4₂.trans h4₁, hr₂⟩
      · refine loopRuns.mono (by omega) hcat ?_
        have hhn₁ : n₁ ≤ 22 + 16 * vsz v := hn₁
        have hv : 1 ≤ vsz v := one_le_vsz v
        rw [vsz_ofList_cons_ap]
        omega
      · have hrev : (v :: zs).reverse ++ acc = zs.reverse ++ (v :: acc) := by
          simp [List.reverse_cons, List.append_assoc]
        rw [hrev]
        exact h1₂

/-! ## Phase 1 -/

theorem appendPhase1 {main : HvdH.Cmd} (zs mzs : List HvdH.Val) (C1 C2 C3 C4 : List HvdH.Glyph)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h1 : X 1 = Work.Layout.elsEnc mzs (Work.Layout.gSent :: C1))
    (h2 : X 2 = Work.Layout.lstEnc zs ++ C2)
    (h3 : X 3 = C3) (h4 : X 4 = C4) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.p1 ⟨g, X⟩ s' n ∧
      n ≤ 40 * (HvdH.vsz (HvdH.ofList zs) + 1) + 2 ∧
      s'.stk 1 = Work.Layout.elsEnc (zs.reverse ++ mzs) (Work.Layout.gSent :: C1) ∧ s'.stk 2 = C2 ∧
      s'.stk 3 = C3 ∧ s'.stk 4 = C4 ∧
      (∀ k : HvdH.Stk, k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → s'.stk k = X k) := by
  have hset : Ev main (.set rFl Glyph.cons) ⟨g, X⟩ ⟨Function.update g rFl Glyph.cons, X⟩ 1 :=
    ev_set' main rFl Glyph.cons g X
  obtain ⟨s₁, hrun, h1₁, h2₁, h3₁, h4₁, hr₁⟩ :=
    p1_loop zs mzs C1 C2 (Function.update g rFl Glyph.cons) X h2 h1 (by simp)
  have hne : s₁.reg rFl ≠ Glyph.cons := by rw [hr₁]; decide
  have hloop : Ev main (.loop rFl Glyph.cons p1Body)
      ⟨Function.update g rFl Glyph.cons, X⟩ s₁ (22 * (vsz (ofList zs) + 1) + 1) :=
    loopRuns.eval hrun hne
  have hmain : Ev main p1 ⟨g, X⟩ s₁ (22 * (vsz (ofList zs) + 1) + 2) := by
    unfold p1
    exact Ev.seq' (C₂ := 22 * (vsz (ofList zs) + 1) + 1) hset hloop (by omega)
  refine ⟨s₁, 22 * (vsz (ofList zs) + 1) + 2, hmain, by omega,
    h1₁, h2₁, h3₁.trans h3, h4₁.trans h4, ?_⟩
  · intro k hk1 hk2 hk3 hk4
    have hfr := Ev.frame hmain (S := ({1, 2, 3, 4} : Finset Stk)) cmdTouches_p1
      (notMem_1234 hk1 hk2 hk3 hk4)
    simpa using hfr

end Work.Layout
