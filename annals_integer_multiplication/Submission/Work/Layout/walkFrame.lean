import Mathlib
import Submission.Work.Layout.chunksOfDefs
import Submission.Work.Layout.chunksProof

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## One iteration of the walking loop -/

/-- `walkBody_ck` on a `cons` glyph: pop the `cons`, move the element to `sT` in normal order with
`mvVal_ev_full` (which restores the scratch stacks `sB`, `sC`), and continue the loop. -/
theorem walkBody_cons_ev {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {y : Val}
    {A : List Glyph} (h0 : X 0 = Glyph.cons :: (y.enc ++ A)) (_hreg : g rLoopG = gCont) :
    ∃ s', Ev main walkBody_ck ⟨g, X⟩ s' (16 * (vsz y + 1) + 4) ∧
      s'.stk 0 = A ∧ s'.stk sT = y.enc ++ X sT ∧
      s'.stk sB = X sB ∧ s'.stk sC = X sC ∧ s'.reg rLoopG = gCont ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁stk, hs₁r, hs₁f, -⟩ :=
    step_peek (main := main) (k := 0) (r := rE) (g := g) (X := X)
      (h := Glyph.cons) (L := y.enc ++ A) h0
  obtain ⟨s₂, hev₂, hs₂stk, -, hs₂f, -⟩ :=
    step_pop (main := main) (k := 0) (r := rE) (g := s₁.reg) (X := s₁.stk)
      (h := Glyph.cons) (L := y.enc ++ A) hs₁stk
  obtain ⟨s₃, n₃, hev₃, hn₃, hs₃a, hs₃b, hs₃c, hs₃d, hs₃f⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := sT) (c := sB) (d := sC)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₂.reg) (X := s₂.stk) (v := y) (A := A) (B := s₂.stk sT) hs₂stk rfl
  obtain ⟨s₄, hev₄, hs₄r, -, hs₄f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₃.reg) (X := s₃.stk)
  have hpop : Ev main (.pop 0 rE) ⟨s₁.reg, s₁.stk⟩ s₂ 1 := hev₂
  have hmv : Ev main (mvVal 0 sT sB sC) ⟨s₂.reg, s₂.stk⟩ s₃ (16 * (vsz y + 1)) :=
    hev₃.mono hn₃
  have hset : Ev main (.set rLoopG gCont) ⟨s₃.reg, s₃.stk⟩ s₄ 1 := hev₄
  have h23 : Ev main (seqs [mvVal 0 sT sB sC, .set rLoopG gCont]) s₂ s₄
      (16 * (vsz y + 1) + 1) := Ev.seq' hmv hset (by omega)
  have h123 : Ev main (seqs [.pop 0 rE, mvVal 0 sT sB sC, .set rLoopG gCont]) s₁ s₄
      (16 * (vsz y + 1) + 2) := Ev.seq' hpop h23 (by omega)
  have hit : Ev main (.ite rE Glyph.cons
      (seqs [.pop 0 rE, mvVal 0 sT sB sC, .set rLoopG gCont]) (.set rLoopG Glyph.eos))
      s₁ s₄ (16 * (vsz y + 1) + 3) :=
    Ev.iteT (C := 16 * (vsz y + 1) + 2) hs₁r h123
  have hbody : Ev main walkBody_ck ⟨g, X⟩ s₄ (16 * (vsz y + 1) + 4) := by
    unfold walkBody_ck
    exact Ev.seq' hev₁ hit (by omega)
  refine ⟨s₄, hbody, ?_, ?_, ?_, ?_, hs₄r, ?_⟩
  · rw [hs₄f 0, hs₃a]
  · rw [hs₄f sT, hs₃b, hs₂f sT (by decide), hs₁f sT (by decide)]
  · rw [hs₄f sB, hs₃c, hs₂f sB (by decide), hs₁f sB (by decide)]
  · rw [hs₄f sC, hs₃d, hs₂f sC (by decide), hs₁f sC (by decide)]
  · intro j h1 h2 h3 h4
    rw [hs₄f j, hs₃f j h1 h2 h3 h4, hs₂f j h1, hs₁f j h1]

/-- `walkBody_ck` on the `nil` terminator: stop the loop; the `nil` glyph is left in place and no
other stack is changed. -/
theorem walkBody_nil_ev {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {A : List Glyph}
    (h0 : X 0 = Glyph.nil :: A) :
    ∃ s', Ev main walkBody_ck ⟨g, X⟩ s' 3 ∧ s'.stk 0 = X 0 ∧
      (∀ j : Stk, j ≠ 0 → s'.stk j = X j) ∧ s'.reg rLoopG = Glyph.eos := by
  obtain ⟨s₁, hev₁, hs₁stk, hs₁r, hs₁f, -⟩ :=
    step_peek (main := main) (k := 0) (r := rE) (g := g) (X := X)
      (h := Glyph.nil) (L := A) h0
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rLoopG) (c := Glyph.eos) (g := s₁.reg) (X := s₁.stk)
  have hne : ¬ (s₁.reg rE = Glyph.cons) := by rw [hs₁r]; exact gnil_ne_cons
  have hit : Ev main (.ite rE Glyph.cons
      (seqs [.pop 0 rE, mvVal 0 sT sB sC, .set rLoopG gCont]) (.set rLoopG Glyph.eos))
      s₁ s₂ 2 := Ev.iteF hne hev₂
  have hbody : Ev main walkBody_ck ⟨g, X⟩ s₂ 3 := by
    unfold walkBody_ck
    exact Ev.seq' hev₁ hit (by omega)
  exact ⟨s₂, hbody, by rw [hs₂f 0, hs₁stk, h0],
    fun j hj => by rw [hs₂f j, hs₁f j hj], hs₂r⟩

/-! ## The walking loop -/

/-- The loop of `walkProg`: walking `ofList ys` on stack 0 moves every element to `sT` (first
element deepest), leaves `nil` on stack 0, and restores the `mvVal` scratch stacks `sB`, `sC`. -/
theorem walkLoop {main : Cmd} {ys : List Val} :
    ∀ (g : Reg → Glyph) (X : Stk → List Glyph) (A T0 : List Glyph),
      g rLoopG = gCont → X 0 = (ofList ys).enc ++ A → X sT = T0 →
      ∃ s' n, Ev main (.loop rLoopG gCont walkBody_ck) ⟨g, X⟩ s' n ∧
        n ≤ 20 * vsz (ofList ys) ∧
        s'.stk 0 = [Glyph.nil] ++ A ∧
        s'.stk sT = ((ys.map Val.enc).reverse).flatten ++ T0 ∧
        s'.stk sB = X sB ∧ s'.stk sC = X sC ∧ s'.reg rLoopG = Glyph.eos ∧
        (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  induction ys with
  | nil =>
      intro g X A T0 hreg h0 hT
      obtain ⟨s₁, hev₁, hs₁stk, hs₁f, hs₁r⟩ :=
        walkBody_nil_ev (main := main) (g := g) (X := X) (A := A) (by rw [h0]; rfl)
      have hne : s₁.reg rLoopG ≠ gCont := by rw [hs₁r]; decide
      have hloop : Ev main (.loop rLoopG gCont walkBody_ck) ⟨g, X⟩ s₁ 5 :=
        Ev.loopT (C₁ := 3) (C₂ := 1) hreg hev₁ (Ev.loopF hne)
      refine ⟨s₁, 20 * vsz (ofList ([] : List Val)), hloop.mono ?_, le_rfl, ?_, ?_, ?_, ?_, hs₁r, ?_⟩
      · have h1 : vsz (ofList ([] : List Val)) = 1 := by simp [vsz, ofList, Val.enc]
        omega
      · exact hs₁stk.trans h0
      · rw [hs₁f sT (by decide), hT]
        simp
      · exact hs₁f sB (by decide)
      · exact hs₁f sC (by decide)
      · intro j h1 _ _ _; exact hs₁f j h1
  | cons y ys' ih =>
      intro g X A T0 hreg h0 hT
      have h0' : X 0 = Glyph.cons :: (y.enc ++ ((ofList ys').enc ++ A)) := by
        rw [h0, enc_ofList_cons, List.cons_append, List.append_assoc]
      obtain ⟨s₁, hev₁, hs₁0, hs₁T, hs₁B, hs₁C, hs₁reg, hs₁f⟩ :=
        walkBody_cons_ev (main := main) (g := g) (X := X) (y := y)
          (A := (ofList ys').enc ++ A) h0' hreg
      have hT₁ : s₁.stk sT = y.enc ++ T0 := by rw [hs₁T, hT]
      obtain ⟨s₂, n₂, hev₂, hn₂, hs₂0, hs₂T, hs₂B, hs₂C, hs₂reg, hs₂f⟩ :=
        ih s₁.reg s₁.stk A (y.enc ++ T0) hs₁reg hs₁0 hT₁
      have hloop : Ev main (.loop rLoopG gCont walkBody_ck) ⟨g, X⟩ s₂
          (16 * (vsz y + 1) + 4 + n₂ + 1) := Ev.loopT hreg hev₁ hev₂
      refine ⟨s₂, 20 * vsz (ofList (y :: ys')), hloop.mono ?_, le_rfl, ?_, ?_, ?_, ?_,
        hs₂reg, ?_⟩
      · have hy : 1 ≤ vsz y := one_le_vsz y
        rw [vsz_ofList_cons]
        omega
      · rw [hs₂0]
      · rw [hs₂T]
        simp only [List.map_cons, List.reverse_cons, List.flatten_append, List.flatten_cons,
          List.flatten_nil, List.nil_append, List.append_nil]
        rw [List.append_assoc]
      · rw [hs₂B, hs₁B]
      · rw [hs₂C, hs₁C]
      · intro j h1 h2 h3 h4
        rw [hs₂f j h1 h2 h3 h4, hs₁f j h1 h2 h3 h4]

/-- Requires the import of `Submission.Work.Layout.chunksOfDefs`.

STRENGTHENING of `Work.Layout.walk_ev` (`Submission/Work/Layout/walk_ev.lean`): `walkProg` also
restores the two `mvVal` scratch stacks `sB` and `sC` (they are used as the buffer/counter of
`Work.Layout.mvVal` in `walkBody_ck`, and `Work.Layout.mvVal_ev_full` restores them).  This is needed
because the frame clause of `walk_ev` deliberately excludes them. -/
theorem walkFrame {main : HvdH.Cmd} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {ys : List HvdH.Val} {A T0 : List HvdH.Glyph}
    (h0 : X 0 = (HvdH.ofList ys).enc ++ A) (hT : X Work.Layout.sT = T0) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.walkProg ⟨g, X⟩ s' n ∧
      n ≤ 40 * (HvdH.vsz (HvdH.ofList ys) + 1) ∧
      s'.stk 0 = [HvdH.Glyph.nil] ++ A ∧
      s'.stk Work.Layout.sT =
        ((ys.map HvdH.Val.enc).reverse).flatten ++ Work.Layout.gSent :: T0 ∧
      s'.stk Work.Layout.sB = X Work.Layout.sB ∧
      s'.stk Work.Layout.sC = X Work.Layout.sC ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.Layout.sT → j ≠ Work.Layout.sB →
        j ≠ Work.Layout.sC → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁T, hs₁f, -, -⟩ :=
    step_pushK (main := main) (k := sT) (c := gSent) (g := g) (X := X)
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₁.reg) (X := s₁.stk)
  have h0₂ : s₂.stk 0 = (ofList ys).enc ++ A := by
    rw [hs₂f 0, hs₁f 0 (by decide : (0 : Stk) ≠ sT), h0]
  have hT₂ : s₂.stk sT = gSent :: T0 := by rw [hs₂f sT, hs₁T, hT]
  obtain ⟨s₃, n₃, hev₃, hn₃, hs₃0, hs₃T, hs₃B, hs₃C, -, hs₃f⟩ :=
    walkLoop (main := main) (ys := ys) s₂.reg s₂.stk A (gSent :: T0)
      (by rw [hs₂r]) h0₂ hT₂
  have hset : Ev main (.set rLoopG gCont) ⟨s₁.reg, s₁.stk⟩ s₂ 1 := hev₂
  have h23 : Ev main (seqs [.set rLoopG gCont, .loop rLoopG gCont walkBody_ck]) s₁ s₃ (1 + n₃) :=
    Ev.seq' hset hev₃ (by omega)
  have hmain : Ev main walkProg ⟨g, X⟩ s₃ (40 * (vsz (ofList ys) + 1)) := by
    unfold walkProg
    exact Ev.seq' hev₁ h23 (by omega)
  exact ⟨s₃, 40 * (vsz (ofList ys) + 1), hmain, le_rfl, hs₃0, hs₃T,
    by rw [hs₃B, hs₂f sB, hs₁f sB (by decide : sB ≠ sT)],
    by rw [hs₃C, hs₂f sC, hs₁f sC (by decide : sC ≠ sT)],
    fun j h1 h2 h3 h4 => by rw [hs₃f j h1 h2 h3 h4, hs₂f j, hs₁f j h2]⟩

end Work.Layout
