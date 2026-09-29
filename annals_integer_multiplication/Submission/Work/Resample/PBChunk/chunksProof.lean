-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Layout/chunksProof.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.PBChunk.chunksOfDefs
/-!
# `LayoutLib.chunksOf`: the phase lemmas

Raw `Eval`/`Ev` proofs for the phases of `Work.Resample.PBChunk.mainProg` (see `chunksOfDefs.lean`).
-/

set_option autoImplicit false

namespace Work.Resample.PBChunk

open Work.Layout
open HvdH

/-! ## Footprints -/

theorem cmdTouches_drainToBody (k : Stk) (κ : Glyph) : cmdTouches (drainToBody k κ) = {k} := by
  simp [drainToBody, seqs, cmdTouches]

theorem cmdTouches_mvVal (a b c d : Stk) : cmdTouches (mvVal a b c d) = {a, b, c, d} := by
  simp only [mvVal, Cmd.seq, cmdTouches, cmdTouches_mvA, cmdTouches_mvB]
  ext j
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem cmdTouches_pushK (k : Stk) (c : Glyph) : cmdTouches (pushK k c) = {k} := by
  simp [pushK, seqs, cmdTouches]

theorem cmdTouches_doubMoveBody : cmdTouches doubMoveBody = {sM, sT2} := by decide
theorem cmdTouches_doubDupBody : cmdTouches doubDupBody = {sM, sT2} := by decide
theorem cmdTouches_cpyOutBody : cmdTouches cpyOutBody = {sM, sT2} := by decide
theorem cmdTouches_cpyBackBody : cmdTouches cpyBackBody = {sM, sW, sT2} := by decide
theorem cmdTouches_readBitBody : cmdTouches readBitBody = {0, sBits} := by
  simp [readBitBody, seqs, cmdTouches]

theorem cmdTouches_elemBody : cmdTouches elemBody = {0, sT, sW, sB, sC} := by
  simp only [elemBody, pushK, seqs, Cmd.seq, cmdTouches, cmdTouches_mvVal]
  ext j
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem cmdTouches_innerProg : cmdTouches innerProg = {0, sT, sW, sB, sC} := by
  simp [innerProg, seqs, cmdTouches, cmdTouches_elemBody]

/-- `List.replicate` with one more element at the front -/
theorem replicate_succ_cons {α : Type} (k : ℕ) (a : α) (l : List α) :
    List.replicate k a ++ a :: l = List.replicate (k + 1) a ++ l := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc List.replicate (k + 1) a ++ a :: l
          = (a :: List.replicate k a) ++ a :: l := by rw [List.replicate_succ]
        _ = a :: (List.replicate k a ++ a :: l) := List.cons_append ..
        _ = a :: (List.replicate (k + 1) a ++ l) := by rw [ih]
        _ = List.replicate (k + 1 + 1) a ++ l := by
              rw [← List.cons_append, ← List.replicate_succ]

/-! ## Primitive steps -/

theorem step_peek {main : Cmd} {k : Stk} {r : Reg} {g : Reg → Glyph} {X : Stk → List Glyph}
    {h : Glyph} {L : List Glyph} (hh : X k = h :: L) :
    ∃ s', Ev main (.peek k r) ⟨g, X⟩ s' 1 ∧ s'.stk k = h :: L ∧ s'.reg r = h ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) ∧ (∀ r' : Reg, r' ≠ r → s'.reg r' = g r') := by
  refine ⟨⟨Function.update g r h, X⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := ev_peek' main k r g X
    rw [show (X k).headD Glyph.eos = h from by rw [hh]; rfl] at h1
    exact h1
  · simp only [stk_mk]
    exact hh
  · simp only [reg_mk]
    exact Function.update_self r h g
  · intro j _; rfl
  · intro r' hr'; exact Function.update_of_ne hr' h g

theorem step_pop {main : Cmd} {k : Stk} {r : Reg} {g : Reg → Glyph} {X : Stk → List Glyph}
    {h : Glyph} {L : List Glyph} (hh : X k = h :: L) :
    ∃ s', Ev main (.pop k r) ⟨g, X⟩ s' 1 ∧ s'.stk k = L ∧ s'.reg r = h ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) ∧ (∀ r' : Reg, r' ≠ r → s'.reg r' = g r') := by
  refine ⟨⟨Function.update g r h, Function.update X k L⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := ev_pop' main k r g X
    rw [show (X k).headD Glyph.eos = h from by rw [hh]; rfl,
      show (X k).tail = L from by rw [hh]; rfl] at h1
    simpa [Function.update_idem] using h1
  · simp only [stk_mk]
    exact Function.update_self k L X
  · simp only [reg_mk]
    exact Function.update_self r h g
  · intro j hj; exact Function.update_of_ne hj L X
  · intro r' hr'; exact Function.update_of_ne hr' h g

theorem step_set {main : Cmd} {r : Reg} {c : Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} :
    ∃ s', Ev main (.set r c) ⟨g, X⟩ s' 1 ∧ s'.reg r = c ∧
      (∀ r' : Reg, r' ≠ r → s'.reg r' = g r') ∧ (∀ j : Stk, s'.stk j = X j) :=
  ⟨⟨Function.update g r c, X⟩, ev_set' main r c g X, Function.update_self r c g,
    fun r' hr' => Function.update_of_ne hr' c g, fun j => rfl⟩

theorem step_push {main : Cmd} {k : Stk} {r : Reg} {g : Reg → Glyph} {X : Stk → List Glyph}
    {v : Glyph} (hv : g r = v) :
    ∃ s', Ev main (.push k r) ⟨g, X⟩ s' 1 ∧ s'.stk k = v :: X k ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) ∧ (∀ r' : Reg, s'.reg r' = g r') := by
  refine ⟨⟨g, Function.update X k (v :: X k)⟩, ?_, ?_, ?_, ?_⟩
  · have h1 := ev_push' main k r g X
    rw [hv] at h1
    exact h1
  · simp only [stk_mk, Function.update_self]
  · intro j hj
    simp only [stk_mk, Function.update_of_ne hj]
  · intro r'; rfl

theorem step_pushK {main : Cmd} {k : Stk} {c : Glyph} {g : Reg → Glyph} {X : Stk → List Glyph} :
    ∃ s', Ev main (pushK k c) ⟨g, X⟩ s' 2 ∧ s'.stk k = c :: X k ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) ∧ s'.reg rE = c ∧
      (∀ r' : Reg, r' ≠ rE → s'.reg r' = g r') := by
  obtain ⟨s₁, hev₁, hr₁, hg₁, hf₁⟩ := step_set (main := main) (r := rE) (c := c) (g := g) (X := X)
  have hpush : Ev main (.push k rE) s₁
      ⟨s₁.reg, Function.update s₁.stk k (c :: s₁.stk k)⟩ 1 := by
    have h := ev_push' main k rE s₁.reg s₁.stk
    rw [hr₁] at h
    exact h
  refine ⟨⟨s₁.reg, Function.update s₁.stk k (c :: s₁.stk k)⟩, ?_, ?_, ?_, hr₁, hg₁⟩
  · exact Ev.seq' hev₁ hpush (by omega)
  · simp only [stk_mk, Function.update_self]
    rw [hf₁ k]
  · intro j hj
    simp only [stk_mk, Function.update_of_ne hj]
    exact hf₁ j

/-! ## Draining a stack down to a glyph -/

theorem drainToBody_ev {main : Cmd} {k : Stk} {κ : Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} {h : Glyph} {L : List Glyph} (hh : X k = h :: L) :
    ∃ s', Ev main (drainToBody k κ) ⟨g, X⟩ s' 4 ∧
      s'.stk k = L ∧ s'.reg rLoopG = (if h = κ then Glyph.eos else gCont) ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁k, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := k) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂k, hs₂r, hs₂f, -⟩ :=
    step_pop (main := main) (k := k) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁k
  by_cases hκ : h = κ
  · obtain ⟨s₃, hev₃, hs₃r, -, hs₃f⟩ :=
      step_set (main := main) (r := rLoopG) (c := Glyph.eos) (g := s₂.reg) (X := s₂.stk)
    have hcond : s₁.reg rE = κ := by rw [hs₁r]; exact hκ
    have hit : Ev main (.ite rE κ (seqs [.pop k rE, .set rLoopG Glyph.eos])
        (seqs [.pop k rE, .set rLoopG gCont])) s₁ s₃ 3 :=
      Ev.iteT hcond (Ev.seq' hev₂ hev₃ (by omega))
    have hbody : Ev main (drainToBody k κ) ⟨g, X⟩ s₃ 4 := Ev.seq' hev₁ hit (by omega)
    refine ⟨s₃, hbody, ?_, ?_, ?_⟩
    · rw [hs₃f k, hs₂k]
    · rw [hs₃r, if_pos hκ]
    · intro j hj
      rw [hs₃f j, hs₂f j hj, hs₁f j hj]
  · obtain ⟨s₃, hev₃, hs₃r, -, hs₃f⟩ :=
      step_set (main := main) (r := rLoopG) (c := gCont) (g := s₂.reg) (X := s₂.stk)
    have hcond : ¬ (s₁.reg rE = κ) := by rw [hs₁r]; exact hκ
    have hit : Ev main (.ite rE κ (seqs [.pop k rE, .set rLoopG Glyph.eos])
        (seqs [.pop k rE, .set rLoopG gCont])) s₁ s₃ 3 :=
      Ev.iteF hcond (Ev.seq' hev₂ hev₃ (by omega))
    have hbody : Ev main (drainToBody k κ) ⟨g, X⟩ s₃ 4 := Ev.seq' hev₁ hit (by omega)
    refine ⟨s₃, hbody, ?_, ?_, ?_⟩
    · rw [hs₃f k, hs₂k]
    · rw [hs₃r, if_neg hκ]
    · intro j hj
      rw [hs₃f j, hs₂f j hj, hs₁f j hj]

theorem drainToLoop {main : Cmd} {k : Stk} {κ : Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} {G B : List Glyph} (hreg : g rLoopG = gCont) (hκ : κ ∉ G)
    (hX : X k = G ++ κ :: B) :
    ∃ s', loopRuns main rLoopG gCont (drainToBody k κ) (G.length + 1) ⟨g, X⟩ s'
        (5 * (G.length + 1)) ∧
      s'.stk k = B ∧ s'.reg rLoopG = Glyph.eos ∧
      (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  induction G generalizing g X with
  | nil =>
      obtain ⟨s', hev, hstk, hreg', hfr⟩ := drainToBody_ev (main := main) (k := k) (κ := κ)
        (g := g) (X := X) (h := κ) (L := B) (by rw [hX]; rfl)
      refine ⟨s', ?_, ?_, ?_, hfr⟩
      · exact loopRuns.one (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev
      · simpa using hstk
      · simpa using hreg'
  | cons h G' ih =>
      have hh : h ≠ κ := fun e => hκ (e ▸ List.mem_cons_self ..)
      have hκ' : κ ∉ G' := fun e => hκ (List.mem_cons_of_mem h e)
      obtain ⟨s₁, hev₁, hstk₁, hreg₁, hfr₁⟩ := drainToBody_ev (main := main) (k := k) (κ := κ)
        (g := g) (X := X) (h := h) (L := G' ++ κ :: B) (by rw [hX]; rfl)
      have hreg₁' : s₁.reg rLoopG = gCont := by rw [hreg₁]; simp [hh]
      obtain ⟨s₂, hrun₂, hstk₂, hreg₂, hfr₂⟩ := ih (g := s₁.reg) (X := s₁.stk) hreg₁' hκ' hstk₁
      refine ⟨s₂, loopRuns.succ'
        (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev₁ hrun₂
        (by simp only [List.length_cons]; omega), hstk₂, hreg₂, ?_⟩
      intro j hj
      rw [hfr₂ j hj, hfr₁ j hj]

theorem drainTo_ev {main : Cmd} {k : Stk} {κ : Glyph} {g : Reg → Glyph}
    {X : Stk → List Glyph} {G B : List Glyph} (hκ : κ ∉ G) (hX : X k = G ++ κ :: B) :
    ∃ s' n, Ev main (drainToProg k κ) ⟨g, X⟩ s' n ∧ n ≤ 6 * (G.length + 1) + 4 ∧
      s'.stk k = B ∧ (∀ j : Stk, j ≠ k → s'.stk j = X j) := by
  obtain ⟨s₁, hrun, hstk, hreg, hfr⟩ :=
    drainToLoop (main := main) (g := Function.update g rLoopG gCont) (by simp) hκ hX
  have hset : Ev main (.set rLoopG gCont) ⟨g, X⟩ ⟨Function.update g rLoopG gCont, X⟩ 1 :=
    ev_set' main rLoopG gCont g X
  have hloop : Ev main (.loop rLoopG gCont (drainToBody k κ))
      ⟨Function.update g rLoopG gCont, X⟩ s₁ (5 * (G.length + 1) + 1) :=
    loopRuns.eval hrun (by rw [hreg]; decide)
  have hmain : Ev main (drainToProg k κ) ⟨g, X⟩ s₁ (6 * (G.length + 1) + 4) := by
    unfold drainToProg
    exact Ev.seq' hset hloop (by omega)
  refine ⟨s₁, _, hmain, le_rfl, hstk, ?_⟩
  intro j hj
  rw [hfr j hj]

/-! ## Doubling -/

theorem doubMoveBody_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {L : List Glyph} (hh : X sM = gSent :: L) :
    ∃ s', Ev main doubMoveBody ⟨g, X⟩ s' 3 ∧ s'.stk sM = X sM ∧ s'.stk sT2 = X sT2 ∧
      s'.reg rLoopG = Glyph.eos ∧ (∀ j : Stk, s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁M, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sM) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rLoopG) (c := Glyph.eos) (g := s₁.reg) (X := s₁.stk)
  have hit : Ev main (.ite rE gSent (.set rLoopG Glyph.eos)
      (seqs [.pop sM rE, .push sT2 rE, .set rLoopG gCont])) s₁ s₂ 2 :=
    Ev.iteT hs₁r hev₂
  have hbody : Ev main doubMoveBody ⟨g, X⟩ s₂ 3 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₂, hbody, ?_, ?_, ?_, ?_⟩
  · rw [hs₂f sM, hs₁M]
    exact hh.symm
  · rw [hs₂f sT2, hs₁f sT2 (by decide)]
  · exact hs₂r
  · intro j
    rw [hs₂f j]
    rcases eq_or_ne j sM with rfl | hj
    · rw [hs₁M]
      exact hh.symm
    · exact hs₁f j hj

theorem doubMoveBody_move {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {h : Glyph} {L : List Glyph} (hh : X sM = h :: L) (hhs : h ≠ gSent) :
    ∃ s', Ev main doubMoveBody ⟨g, X⟩ s' 5 ∧ s'.stk sM = L ∧ s'.stk sT2 = h :: X sT2 ∧
      s'.reg rLoopG = gCont ∧
      (∀ j : Stk, j ≠ sM → j ≠ sT2 → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁M, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sM) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂M, hs₂r, hs₂f, -⟩ :=
    step_pop (main := main) (k := sM) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁M
  obtain ⟨s₃, hev₃, hs₃T, hs₃f, hs₃g⟩ :=
    step_push (main := main) (k := sT2) (r := rE) (g := s₂.reg) (X := s₂.stk) (v := h) hs₂r
  obtain ⟨s₄, hev₄, hs₄r, -, hs₄f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₃.reg) (X := s₃.stk)
  have h34 : Ev main (seqs [.push sT2 rE, .set rLoopG gCont]) s₂ s₄ 2 :=
    Ev.seq' hev₃ hev₄ (by omega)
  have hseq : Ev main (seqs [.pop sM rE, .push sT2 rE, .set rLoopG gCont]) s₁ s₄ 3 :=
    Ev.seq' hev₂ h34 (by omega)
  have hcond : ¬ (s₁.reg rE = gSent) := by rw [hs₁r]; exact hhs
  have hit : Ev main (.ite rE gSent (.set rLoopG Glyph.eos)
      (seqs [.pop sM rE, .push sT2 rE, .set rLoopG gCont])) s₁ s₄ 4 :=
    Ev.iteF hcond hseq
  have hbody : Ev main doubMoveBody ⟨g, X⟩ s₄ 5 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₄, hbody, ?_, ?_, ?_, ?_⟩
  · rw [hs₄f sM, hs₃f sM (by decide : sM ≠ sT2), hs₂M]
  · rw [hs₄f sT2, hs₃T, hs₂f sT2 (by decide : sT2 ≠ sM), hs₁f sT2 (by decide : sT2 ≠ sM)]
  · rw [hs₄r]
  · intro j hj1 hj2
    rw [hs₄f j, hs₃f j hj2, hs₂f j hj1, hs₁f j hj1]

theorem doubDupBody_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {L : List Glyph} (hh : X sT2 = gMark :: L) :
    ∃ s', Ev main doubDupBody ⟨g, X⟩ s' 3 ∧ s'.stk sM = X sM ∧ s'.stk sT2 = X sT2 ∧
      s'.reg rLoopG = Glyph.eos ∧ (∀ j : Stk, s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁T, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sT2) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rLoopG) (c := Glyph.eos) (g := s₁.reg) (X := s₁.stk)
  have hit : Ev main (.ite rE gMark (.set rLoopG Glyph.eos)
      (seqs [.pop sT2 rE, .push sM rE, .push sM rE, .set rLoopG gCont])) s₁ s₂ 2 :=
    Ev.iteT hs₁r hev₂
  have hbody : Ev main doubDupBody ⟨g, X⟩ s₂ 3 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₂, hbody, ?_, ?_, ?_, ?_⟩
  · rw [hs₂f sM, hs₁f sM (by decide : sM ≠ sT2)]
  · rw [hs₂f sT2, hs₁T]
    exact hh.symm
  · exact hs₂r
  · intro j
    rw [hs₂f j]
    rcases eq_or_ne j sT2 with rfl | hj
    · rw [hs₁T]
      exact hh.symm
    · exact hs₁f j hj

theorem doubDupBody_dup {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {h : Glyph} {L : List Glyph} (hh : X sT2 = h :: L) (hhs : h ≠ gMark) :
    ∃ s', Ev main doubDupBody ⟨g, X⟩ s' 6 ∧ s'.stk sT2 = L ∧ s'.stk sM = h :: h :: X sM ∧
      s'.reg rLoopG = gCont ∧
      (∀ j : Stk, j ≠ sM → j ≠ sT2 → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁T, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sT2) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂T, hs₂r, hs₂f, -⟩ :=
    step_pop (main := main) (k := sT2) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁T
  obtain ⟨s₃, hev₃, hs₃M, hs₃f, hs₃g⟩ :=
    step_push (main := main) (k := sM) (r := rE) (g := s₂.reg) (X := s₂.stk) (v := h) hs₂r
  have hr₃ : s₃.reg rE = h := by rw [hs₃g rE, hs₂r]
  obtain ⟨s₄, hev₄, hs₄M, hs₄f, hs₄g⟩ :=
    step_push (main := main) (k := sM) (r := rE) (g := s₃.reg) (X := s₃.stk) (v := h) hr₃
  obtain ⟨s₅, hev₅, hs₅r, -, hs₅f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₄.reg) (X := s₄.stk)
  have h45 : Ev main (seqs [.push sM rE, .set rLoopG gCont]) s₃ s₅ 2 :=
    Ev.seq' hev₄ hev₅ (by omega)
  have h345 : Ev main (seqs [.push sM rE, .push sM rE, .set rLoopG gCont]) s₂ s₅ 3 :=
    Ev.seq' hev₃ h45 (by omega)
  have hseq : Ev main (seqs [.pop sT2 rE, .push sM rE, .push sM rE, .set rLoopG gCont])
      s₁ s₅ 4 :=
    Ev.seq' hev₂ h345 (by omega)
  have hcond : ¬ (s₁.reg rE = gMark) := by rw [hs₁r]; exact hhs
  have hit : Ev main (.ite rE gMark (.set rLoopG Glyph.eos)
      (seqs [.pop sT2 rE, .push sM rE, .push sM rE, .set rLoopG gCont])) s₁ s₅ 5 :=
    Ev.iteF hcond hseq
  have hbody : Ev main doubDupBody ⟨g, X⟩ s₅ 6 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₅, hbody, ?_, ?_, ?_, ?_⟩
  · rw [hs₅f sT2, hs₄f sT2 (by decide : sT2 ≠ sM), hs₃f sT2 (by decide : sT2 ≠ sM), hs₂T]
  · rw [hs₅f sM, hs₄M, hs₃M, hs₂f sM (by decide : sM ≠ sT2),
      hs₁f sM (by decide : sM ≠ sT2)]
  · rw [hs₅r]
  · intro j hj1 hj2
    rw [hs₅f j, hs₄f j hj1, hs₃f j hj1, hs₂f j hj2, hs₁f j hj2]

/-! ## The two loops of `doubleProg` -/

theorem doubMoveLoop {main : Cmd} :
    ∀ (k : ℕ) (g : Reg → Glyph) (X : Stk → List Glyph) (M0 T20 : List Glyph),
      g rLoopG = gCont → X sM = List.replicate k gPend ++ gSent :: M0 → X sT2 = T20 →
      ∃ s', loopRuns main rLoopG gCont doubMoveBody (k + 1) ⟨g, X⟩ s' (6 * (k + 1)) ∧
        s'.stk sM = gSent :: M0 ∧ s'.stk sT2 = List.replicate k gPend ++ T20 ∧
        s'.reg rLoopG = Glyph.eos ∧
        (∀ j : Stk, j ≠ sM → j ≠ sT2 → s'.stk j = X j) := by
  intro k
  induction k with
  | zero =>
      intro g X M0 T20 hreg hM hT
      obtain ⟨s₁, hev₁, hsM₁, hsT₁, hreg₁, hfr₁⟩ :=
        doubMoveBody_stop (main := main) (g := g) (X := X) (L := M0) hM
      refine ⟨s₁, loopRuns.mono (by omega) (loopRuns.one
        (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev₁) (by omega),
        ?_, ?_, hreg₁, ?_⟩
      · rw [hsM₁, hM]
        simp
      · rw [hsT₁, hT]
        simp
      · intro j hj1 hj2
        rw [hfr₁ j]
  | succ k ih =>
      intro g X M0 T20 hreg hM hT
      have hM' : X sM = gPend :: (List.replicate k gPend ++ gSent :: M0) := by
        rw [hM, List.replicate_succ]; rfl
      obtain ⟨s₁, hev₁, hsM₁, hsT₂₁, hreg₁, hfr₁⟩ :=
        doubMoveBody_move (main := main) (g := g) (X := X) (h := gPend)
          (L := List.replicate k gPend ++ gSent :: M0) hM' (by simp [gPend_ne_gSent])
      obtain ⟨s₂, hrun₂, hsM₂, hsT₂₂, hreg₂, hfr₂⟩ :=
        ih s₁.reg s₁.stk M0 (s₁.stk sT2) hreg₁ hsM₁ rfl
      refine ⟨s₂, loopRuns.succ'
        (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev₁ hrun₂ (by omega),
        hsM₂, ?_, hreg₂, ?_⟩
      · rw [hsT₂₂, hsT₂₁, hT, show List.replicate k gPend ++ gPend :: T20
            = List.replicate (k + 1) gPend ++ T20 from replicate_succ_cons k gPend T20]
      · intro j hj1 hj2
        rw [hfr₂ j hj1 hj2, hfr₁ j hj1 hj2]

theorem doubDupLoop {main : Cmd} :
    ∀ (k : ℕ) (g : Reg → Glyph) (X : Stk → List Glyph) (T20 : List Glyph),
      g rLoopG = gCont → X sT2 = List.replicate k gPend ++ gMark :: T20 →
      ∃ s', loopRuns main rLoopG gCont doubDupBody (k + 1) ⟨g, X⟩ s' (7 * (k + 1)) ∧
        s'.stk sT2 = gMark :: T20 ∧
        s'.stk sM = List.replicate (2 * k) gPend ++ X sM ∧
        s'.reg rLoopG = Glyph.eos ∧
        (∀ j : Stk, j ≠ sM → j ≠ sT2 → s'.stk j = X j) := by
  intro k
  induction k with
  | zero =>
      intro g X T20 hreg hT
      obtain ⟨s₁, hev₁, hsM₁, hsT₁, hreg₁, hfr₁⟩ :=
        doubDupBody_stop (main := main) (g := g) (X := X) (L := T20) (by rw [hT]; rfl)
      refine ⟨s₁, loopRuns.mono (by omega) (loopRuns.one
        (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev₁) (by omega),
        ?_, ?_, hreg₁, ?_⟩
      · rw [hsT₁, hT]
        simp
      · rw [hsM₁]
        simp
      · intro j hj1 hj2
        rw [hfr₁ j]
  | succ k ih =>
      intro g X T20 hreg hT
      have hT' : X sT2 = gPend :: (List.replicate k gPend ++ gMark :: T20) := by
        rw [hT, List.replicate_succ]; rfl
      obtain ⟨s₁, hev₁, hsT₂₁, hsM₁, hreg₁, hfr₁⟩ :=
        doubDupBody_dup (main := main) (g := g) (X := X) (h := gPend)
          (L := List.replicate k gPend ++ gMark :: T20) hT' (by simp [gPend_ne_gMark])
      obtain ⟨s₂, hrun₂, hsT₂₂, hsM₂, hreg₂, hfr₂⟩ := ih s₁.reg s₁.stk T20 hreg₁ hsT₂₁
      refine ⟨s₂, loopRuns.succ'
        (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev₁ hrun₂ (by omega),
        hsT₂₂, ?_, hreg₂, ?_⟩
      · rw [hsM₂, hsM₁, show 2 * (k + 1) = 2 * k + 2 by ring,
          show List.replicate (2 * k) gPend ++ gPend :: gPend :: X sM
            = List.replicate (2 * k + 1) gPend ++ gPend :: X sM
            from replicate_succ_cons (2 * k) gPend (gPend :: X sM),
          show List.replicate (2 * k + 1) gPend ++ gPend :: X sM
            = List.replicate (2 * k + 1 + 1) gPend ++ X sM
            from replicate_succ_cons (2 * k + 1) gPend (X sM)]
      · intro j hj1 hj2
        rw [hfr₂ j hj1 hj2, hfr₁ j hj1 hj2]

theorem double_ev {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {k : ℕ}
    {M0 T0 : List Glyph} (hM : X sM = List.replicate k gPend ++ gSent :: M0)
    (hT : X sT2 = T0) :
    ∃ s' n, Ev main doubleProg ⟨g, X⟩ s' n ∧ n ≤ 14 * (k + 1) + 10 ∧
      s'.stk sM = List.replicate (2 * k) gPend ++ gSent :: M0 ∧ s'.stk sT2 = T0 ∧
      (∀ j : Stk, j ≠ sM → j ≠ sT2 → s'.stk j = X j) := by
  obtain ⟨s₀, hev₀, hs₀T, hs₀f, -, -⟩ :=
    step_pushK (main := main) (k := sT2) (c := gMark) (g := g) (X := X)
  obtain ⟨s₁, hev₁, hs₁r, -, hs₁f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₀.reg) (X := s₀.stk)
  have hM₁ : s₁.stk sM = List.replicate k gPend ++ gSent :: M0 := by
    rw [hs₁f sM, hs₀f sM (by decide : sM ≠ sT2)]
    exact hM
  obtain ⟨s₂, hrun₂, hsM₂, hsT₂₂, hreg₂, hfr₂⟩ :=
    doubMoveLoop (main := main) k s₁.reg s₁.stk M0 (gMark :: T0) (by rw [hs₁r])
      hM₁ (by rw [hs₁f sT2, hs₀T, hT])
  obtain ⟨s₃, hev₃, hs₃r, -, hs₃f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₂.reg) (X := s₂.stk)
  have hT₃ : s₃.stk sT2 = List.replicate k gPend ++ gMark :: T0 := by
    rw [hs₃f sT2, hsT₂₂]
  obtain ⟨s₄, hrun₄, hsT₂₄, hsM₄, hreg₄, hfr₄⟩ :=
    doubDupLoop (main := main) k s₃.reg s₃.stk T0 (by rw [hs₃r]) hT₃
  obtain ⟨s₅, hev₅, hs₅T, -, hs₅f, -⟩ :=
    step_pop (main := main) (k := sT2) (r := rE) (g := s₄.reg) (X := s₄.stk) hsT₂₄
  have h3 : Ev main (.loop rLoopG gCont doubMoveBody) s₁ s₂ (6 * (k + 1) + 1) :=
    loopRuns.eval hrun₂ (by rw [hreg₂]; decide)
  have h5 : Ev main (.loop rLoopG gCont doubDupBody) s₃ s₄ (7 * (k + 1) + 1) :=
    loopRuns.eval hrun₄ (by rw [hreg₄]; decide)
  have h56 : Ev main (seqs [.loop rLoopG gCont doubDupBody, .pop sT2 rE]) s₃ s₅
      (7 * (k + 1) + 1 + 1) := Ev.seq' h5 hev₅ (by omega)
  have h456 : Ev main (seqs [.set rLoopG gCont, .loop rLoopG gCont doubDupBody,
      .pop sT2 rE]) s₂ s₅ (1 + (7 * (k + 1) + 1 + 1)) := Ev.seq' hev₃ h56 (by omega)
  have h3456 : Ev main (seqs [.loop rLoopG gCont doubMoveBody, .set rLoopG gCont,
      .loop rLoopG gCont doubDupBody, .pop sT2 rE]) s₁ s₅
      ((6 * (k + 1) + 1) + (1 + (7 * (k + 1) + 1 + 1))) := Ev.seq' h3 h456 (by omega)
  have h23456 : Ev main (seqs [.set rLoopG gCont, .loop rLoopG gCont doubMoveBody,
      .set rLoopG gCont, .loop rLoopG gCont doubDupBody, .pop sT2 rE]) s₀ s₅
      (1 + ((6 * (k + 1) + 1) + (1 + (7 * (k + 1) + 1 + 1)))) := Ev.seq' hev₁ h3456 (by omega)
  have hmain : Ev main doubleProg ⟨g, X⟩ s₅ (14 * (k + 1) + 10) := by
    unfold doubleProg
    exact Ev.seq' hev₀ h23456 (by omega)
  refine ⟨s₅, _, hmain, le_rfl, ?_, ?_, ?_⟩
  · rw [hs₅f sM (by decide : sM ≠ sT2), hsM₄, hs₃f sM, hsM₂]
  · rw [hs₅T]
  · intro j hj1 hj2
    rw [hs₅f j hj2, hfr₄ j hj1 hj2, hs₃f j, hfr₂ j hj1 hj2, hs₁f j, hs₀f j hj2]

/-! ## Copying the counter -/

theorem cpyOutBody_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {L : List Glyph}
    (hh : X sM = gSent :: L) :
    ∃ s', Ev main cpyOutBody ⟨g, X⟩ s' 3 ∧ s'.stk sM = X sM ∧ s'.stk sT2 = X sT2 ∧
      s'.reg rF = Glyph.eos ∧ (∀ j : Stk, s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁M, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sM) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rF) (c := Glyph.eos) (g := s₁.reg) (X := s₁.stk)
  have hit : Ev main (.ite rE gSent (.set rF Glyph.eos)
      (seqs [.pop sM rE, .push sT2 rE, .set rF gCont])) s₁ s₂ 2 := Ev.iteT hs₁r hev₂
  have hbody : Ev main cpyOutBody ⟨g, X⟩ s₂ 3 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₂, hbody, ?_, ?_, hs₂r, ?_⟩
  · rw [hs₂f sM, hs₁M, hh]
  · rw [hs₂f sT2, hs₁f sT2 (by decide : sT2 ≠ sM)]
  · intro j
    rw [hs₂f j]
    rcases eq_or_ne j sM with rfl | hj
    · rw [hs₁M, hh]
    · exact hs₁f j hj

theorem cpyOutBody_move {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {h : Glyph}
    {L : List Glyph} (hh : X sM = h :: L) (hhs : h ≠ gSent) :
    ∃ s', Ev main cpyOutBody ⟨g, X⟩ s' 5 ∧ s'.stk sM = L ∧ s'.stk sT2 = h :: X sT2 ∧
      s'.reg rF = gCont ∧ (∀ j : Stk, j ≠ sM → j ≠ sT2 → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁M, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sM) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂M, hs₂r, hs₂f, -⟩ :=
    step_pop (main := main) (k := sM) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁M
  obtain ⟨s₃, hev₃, hs₃T, hs₃f, -⟩ :=
    step_push (main := main) (k := sT2) (r := rE) (g := s₂.reg) (X := s₂.stk) (v := h) hs₂r
  obtain ⟨s₄, hev₄, hs₄r, -, hs₄f⟩ :=
    step_set (main := main) (r := rF) (c := gCont) (g := s₃.reg) (X := s₃.stk)
  have h34 : Ev main (seqs [.push sT2 rE, .set rF gCont]) s₂ s₄ 2 := Ev.seq' hev₃ hev₄ (by omega)
  have hseq : Ev main (seqs [.pop sM rE, .push sT2 rE, .set rF gCont]) s₁ s₄ 3 :=
    Ev.seq' hev₂ h34 (by omega)
  have hcond : ¬ (s₁.reg rE = gSent) := by rw [hs₁r]; exact hhs
  have hit : Ev main (.ite rE gSent (.set rF Glyph.eos)
      (seqs [.pop sM rE, .push sT2 rE, .set rF gCont])) s₁ s₄ 4 := Ev.iteF hcond hseq
  have hbody : Ev main cpyOutBody ⟨g, X⟩ s₄ 5 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₄, hbody, ?_, ?_, hs₄r, ?_⟩
  · rw [hs₄f sM, hs₃f sM (by decide : sM ≠ sT2), hs₂M]
  · rw [hs₄f sT2, hs₃T, hs₂f sT2 (by decide : sT2 ≠ sM), hs₁f sT2 (by decide : sT2 ≠ sM)]
  · intro j hj1 hj2
    rw [hs₄f j, hs₃f j hj2, hs₂f j hj1, hs₁f j hj1]

theorem cpyBackBody_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {L : List Glyph}
    (hh : X sT2 = gMark :: L) :
    ∃ s', Ev main cpyBackBody ⟨g, X⟩ s' 3 ∧ s'.stk sM = X sM ∧ s'.stk sT2 = X sT2 ∧
      s'.stk sW = X sW ∧ s'.reg rF = Glyph.eos ∧ (∀ j : Stk, s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁T, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sT2) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rF) (c := Glyph.eos) (g := s₁.reg) (X := s₁.stk)
  have hit : Ev main (.ite rE gMark (.set rF Glyph.eos)
      (seqs [.pop sT2 rE, .push sM rE, .push sW rE, .set rF gCont])) s₁ s₂ 2 :=
    Ev.iteT hs₁r hev₂
  have hbody : Ev main cpyBackBody ⟨g, X⟩ s₂ 3 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₂, hbody, ?_, ?_, ?_, hs₂r, ?_⟩
  · rw [hs₂f sM, hs₁f sM (by decide : sM ≠ sT2)]
  · rw [hs₂f sT2, hs₁T, hh]
  · rw [hs₂f sW, hs₁f sW (by decide : sW ≠ sT2)]
  · intro j
    rw [hs₂f j]
    rcases eq_or_ne j sT2 with rfl | hj
    · rw [hs₁T, hh]
    · exact hs₁f j hj

theorem cpyBackBody_move {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {h : Glyph}
    {L : List Glyph} (hh : X sT2 = h :: L) (hhs : h ≠ gMark) :
    ∃ s', Ev main cpyBackBody ⟨g, X⟩ s' 6 ∧ s'.stk sT2 = L ∧ s'.stk sM = h :: X sM ∧
      s'.stk sW = h :: X sW ∧ s'.reg rF = gCont ∧
      (∀ j : Stk, j ≠ sM → j ≠ sW → j ≠ sT2 → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁T, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sT2) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂T, hs₂r, hs₂f, -⟩ :=
    step_pop (main := main) (k := sT2) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁T
  obtain ⟨s₃, hev₃, hs₃M, hs₃f, hs₃g⟩ :=
    step_push (main := main) (k := sM) (r := rE) (g := s₂.reg) (X := s₂.stk) (v := h) hs₂r
  have hr₃ : s₃.reg rE = h := by rw [hs₃g rE, hs₂r]
  obtain ⟨s₄, hev₄, hs₄W, hs₄f, hs₄g⟩ :=
    step_push (main := main) (k := sW) (r := rE) (g := s₃.reg) (X := s₃.stk) (v := h) hr₃
  obtain ⟨s₅, hev₅, hs₅r, -, hs₅f⟩ :=
    step_set (main := main) (r := rF) (c := gCont) (g := s₄.reg) (X := s₄.stk)
  have h45 : Ev main (seqs [.push sW rE, .set rF gCont]) s₃ s₅ 2 := Ev.seq' hev₄ hev₅ (by omega)
  have h345 : Ev main (seqs [.push sM rE, .push sW rE, .set rF gCont]) s₂ s₅ 3 :=
    Ev.seq' hev₃ h45 (by omega)
  have hseq : Ev main (seqs [.pop sT2 rE, .push sM rE, .push sW rE, .set rF gCont]) s₁ s₅ 4 :=
    Ev.seq' hev₂ h345 (by omega)
  have hcond : ¬ (s₁.reg rE = gMark) := by rw [hs₁r]; exact hhs
  have hit : Ev main (.ite rE gMark (.set rF Glyph.eos)
      (seqs [.pop sT2 rE, .push sM rE, .push sW rE, .set rF gCont])) s₁ s₅ 5 :=
    Ev.iteF hcond hseq
  have hbody : Ev main cpyBackBody ⟨g, X⟩ s₅ 6 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₅, hbody, ?_, ?_, ?_, hs₅r, ?_⟩
  · rw [hs₅f sT2, hs₄f sT2 (by decide : sT2 ≠ sW), hs₃f sT2 (by decide : sT2 ≠ sM), hs₂T]
  · rw [hs₅f sM, hs₄f sM (by decide : sM ≠ sW), hs₃M,
      hs₂f sM (by decide : sM ≠ sT2), hs₁f sM (by decide : sM ≠ sT2)]
  · rw [hs₅f sW, hs₄W, hs₃f sW (by decide : sW ≠ sM),
      hs₂f sW (by decide : sW ≠ sT2), hs₁f sW (by decide : sW ≠ sT2)]
  · intro j hj1 hj2 hj3
    rw [hs₅f j, hs₄f j hj2, hs₃f j hj1, hs₂f j hj3, hs₁f j hj3]

theorem cpyOutLoop {main : Cmd} {G : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    {M0 T20 : List Glyph} (hreg : g rF = gCont) (hGs : gSent ∉ G)
    (hM : X sM = G ++ gSent :: M0) (hT : X sT2 = T20) :
    ∃ s', loopRuns main rF gCont cpyOutBody (G.length + 1) ⟨g, X⟩ s' (6 * (G.length + 1)) ∧
      s'.stk sM = gSent :: M0 ∧ s'.stk sT2 = G.reverse ++ T20 ∧
      s'.reg rF = Glyph.eos ∧ (∀ j : Stk, j ≠ sM → j ≠ sT2 → s'.stk j = X j) := by
  induction G generalizing g X T20 with
  | nil =>
      obtain ⟨s₁, hev₁, hsM₁, hsT₁, hreg₁, hfr₁⟩ :=
        cpyOutBody_stop (main := main) (g := g) (X := X) (L := M0) (by rw [hM]; rfl)
      refine ⟨s₁, loopRuns.mono (by omega) (loopRuns.one
        (show (⟨g, X⟩ : State).reg rF = gCont from hreg) hev₁) (by omega),
        ?_, ?_, hreg₁, ?_⟩
      · simp only [hsM₁, hM, List.reverse_nil, List.nil_append]
      · simp only [hsT₁, hT, List.reverse_nil, List.nil_append]
      · intro j hj1 hj2
        rw [hfr₁ j]
  | cons h G' ih =>
      have hh : h ≠ gSent := fun e => hGs (e ▸ List.mem_cons_self ..)
      have hGs' : gSent ∉ G' := fun e => hGs (List.mem_cons_of_mem h e)
      obtain ⟨s₁, hev₁, hsM₁, hsT₂₁, hreg₁, hfr₁⟩ :=
        cpyOutBody_move (main := main) (g := g) (X := X) (h := h)
          (L := G' ++ gSent :: M0) (by rw [hM]; rfl) hh
      obtain ⟨s₂, hrun₂, hsM₂, hsT₂₂, hreg₂, hfr₂⟩ :=
        ih (g := s₁.reg) (X := s₁.stk) (T20 := s₁.stk sT2) hreg₁ hGs' hsM₁ rfl
      refine ⟨s₂, loopRuns.succ'
        (show (⟨g, X⟩ : State).reg rF = gCont from hreg) hev₁ hrun₂
        (by simp only [List.length_cons]; omega),
        hsM₂, ?_, hreg₂, ?_⟩
      · simp only [hsT₂₂, hsT₂₁, hT, List.reverse_cons, List.append_assoc,
          List.singleton_append]
      · intro j hj1 hj2
        rw [hfr₂ j hj1 hj2, hfr₁ j hj1 hj2]

theorem cpyBackLoop {main : Cmd} {P : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    {T20 : List Glyph} (hreg : g rF = gCont) (hP : gMark ∉ P) (hT : X sT2 = P ++ gMark :: T20) :
    ∃ s', loopRuns main rF gCont cpyBackBody (P.length + 1) ⟨g, X⟩ s' (7 * (P.length + 1)) ∧
      s'.stk sT2 = gMark :: T20 ∧ s'.stk sM = P.reverse ++ X sM ∧
      s'.stk sW = P.reverse ++ X sW ∧ s'.reg rF = Glyph.eos ∧
      (∀ j : Stk, j ≠ sM → j ≠ sW → j ≠ sT2 → s'.stk j = X j) := by
  induction P generalizing g X with
  | nil =>
      obtain ⟨s₁, hev₁, hsM₁, hsT₁, hsW₁, hreg₁, hfr₁⟩ :=
        cpyBackBody_stop (main := main) (g := g) (X := X) (L := T20) (by rw [hT]; rfl)
      refine ⟨s₁, loopRuns.mono (by omega) (loopRuns.one
        (show (⟨g, X⟩ : State).reg rF = gCont from hreg) hev₁) (by omega),
        ?_, ?_, ?_, hreg₁, ?_⟩
      · simp only [hsT₁, hT, List.reverse_nil, List.nil_append]
      · simp only [hsM₁, List.reverse_nil, List.nil_append]
      · simp only [hsW₁, List.reverse_nil, List.nil_append]
      · intro j hj1 hj2 hj3
        rw [hfr₁ j]
  | cons h P' ih =>
      have hh : h ≠ gMark := fun e => hP (e ▸ List.mem_cons_self ..)
      have hP' : gMark ∉ P' := fun e => hP (List.mem_cons_of_mem h e)
      obtain ⟨s₁, hev₁, hsT₂₁, hsM₁, hsW₁, hreg₁, hfr₁⟩ :=
        cpyBackBody_move (main := main) (g := g) (X := X) (h := h)
          (L := P' ++ gMark :: T20) (by rw [hT]; rfl) hh
      obtain ⟨s₂, hrun₂, hsT₂₂, hsM₂, hsW₂, hreg₂, hfr₂⟩ :=
        ih (g := s₁.reg) (X := s₁.stk) hreg₁ hP' hsT₂₁
      refine ⟨s₂, loopRuns.succ'
        (show (⟨g, X⟩ : State).reg rF = gCont from hreg) hev₁ hrun₂
        (by simp only [List.length_cons]; omega),
        hsT₂₂, ?_, ?_, hreg₂, ?_⟩
      · rw [hsM₂, hsM₁, List.reverse_cons, List.append_assoc, List.singleton_append]
      · rw [hsW₂, hsW₁, List.reverse_cons, List.append_assoc, List.singleton_append]
      · intro j hj1 hj2 hj3
        rw [hfr₂ j hj1 hj2 hj3, hfr₁ j hj1 hj2 hj3]

theorem copy_ev {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {G M0 W0 T20 : List Glyph}
    (hGm : gMark ∉ G) (hGs : gSent ∉ G) (hM : X sM = G ++ gSent :: M0)
    (hT2 : X sT2 = T20) (hW : X sW = W0) :
    ∃ s' n, Ev main copyProg ⟨g, X⟩ s' n ∧ n ≤ 40 * (G.length + 1) + 40 ∧
      s'.stk sM = G ++ gSent :: M0 ∧ s'.stk sW = G ++ gSent :: W0 ∧
      s'.stk sT2 = T20 ∧
      (∀ j : Stk, j ≠ sM → j ≠ sW → j ≠ sT2 → s'.stk j = X j) := by
  obtain ⟨s₀, hev₀, hs₀T, hs₀f, -, -⟩ :=
    step_pushK (main := main) (k := sT2) (c := gMark) (g := g) (X := X)
  have hM₀ : s₀.stk sM = G ++ gSent :: M0 := by
    rw [hs₀f sM (by decide : sM ≠ sT2)]; exact hM
  obtain ⟨s₁, hev₁, hs₁r, -, hs₁f⟩ :=
    step_set (main := main) (r := rF) (c := gCont) (g := s₀.reg) (X := s₀.stk)
  obtain ⟨s₂, hrun₂, hsM₂, hsT₂₂, hreg₂, hfr₂⟩ :=
    cpyOutLoop (main := main) (G := G) (g := s₁.reg) (X := s₁.stk) (M0 := M0) (T20 := gMark :: T20)
      (by rw [hs₁r]) hGs (by rw [hs₁f sM]; exact hM₀) (by rw [hs₁f sT2, hs₀T, hT2])
  obtain ⟨s₃, hev₃, hs₃M, hs₃r, hs₃f, -⟩ :=
    step_pop (main := main) (k := sM) (r := rE) (g := s₂.reg) (X := s₂.stk) hsM₂
  obtain ⟨s₄, hev₄, hs₄T, hs₄f, -⟩ :=
    step_push (main := main) (k := sT2) (r := rE) (g := s₃.reg) (X := s₃.stk) (v := gSent) hs₃r
  have hP : gMark ∉ gSent :: G.reverse := by
    intro h
    rcases List.mem_cons.mp h with h1 | h2
    · exact gMark_ne_gSent h1
    · exact hGm (List.mem_reverse.mp h2)
  have hs₄T' : s₄.stk sT2 = (gSent :: G.reverse) ++ gMark :: T20 := by
    rw [hs₄T, hs₃f sT2 (by decide : sT2 ≠ sM), hsT₂₂, List.cons_append]
  obtain ⟨s₅, hev₅, hs₅r, -, hs₅f⟩ :=
    step_set (main := main) (r := rF) (c := gCont) (g := s₄.reg) (X := s₄.stk)
  obtain ⟨s₆, hrun₆, hsT₆, hsM₆, hsW₆, hreg₆, hfr₆⟩ :=
    cpyBackLoop (main := main) (P := gSent :: G.reverse) (g := s₅.reg) (X := s₅.stk)
      (T20 := T20) (by rw [hs₅r]) hP (by rw [hs₅f sT2, hs₄T'])
  obtain ⟨s₇, hev₇, hsT₇, -, hs₇f, -⟩ :=
    step_pop (main := main) (k := sT2) (r := rE) (g := s₆.reg) (X := s₆.stk) hsT₆
  have h3 : Ev main (.loop rF gCont cpyOutBody) s₁ s₂ (6 * (G.length + 1) + 1) :=
    loopRuns.eval hrun₂ (by rw [hreg₂]; decide)
  have h7 : Ev main (.loop rF gCont cpyBackBody) s₅ s₆
      (7 * ((gSent :: G.reverse).length + 1) + 1) :=
    loopRuns.eval hrun₆ (by rw [hreg₆]; decide)
  have h8 : Ev main (.pop sT2 rE) s₆ s₇ 1 := hev₇
  have e78 : Ev main (seqs [.loop rF gCont cpyBackBody, .pop sT2 rE]) s₅ s₇
      (7 * ((gSent :: G.reverse).length + 1) + 1 + 1) := Ev.seq' h7 h8 (by omega)
  have e678 : Ev main (seqs [.set rF gCont, .loop rF gCont cpyBackBody, .pop sT2 rE]) s₄ s₇
      (1 + (7 * ((gSent :: G.reverse).length + 1) + 1 + 1)) := Ev.seq' hev₅ e78 (by omega)
  have e5678 : Ev main (seqs [.push sT2 rE, .set rF gCont, .loop rF gCont cpyBackBody,
        .pop sT2 rE]) s₃ s₇ (1 + (1 + (7 * ((gSent :: G.reverse).length + 1) + 1 + 1))) :=
    Ev.seq' hev₄ e678 (by omega)
  have e45678 : Ev main (seqs [.pop sM rE, .push sT2 rE, .set rF gCont,
        .loop rF gCont cpyBackBody, .pop sT2 rE]) s₂ s₇
      (1 + (1 + (1 + (7 * ((gSent :: G.reverse).length + 1) + 1 + 1)))) :=
    Ev.seq' hev₃ e5678 (by omega)
  have e345678 : Ev main (seqs [.loop rF gCont cpyOutBody, .pop sM rE, .push sT2 rE,
        .set rF gCont, .loop rF gCont cpyBackBody, .pop sT2 rE]) s₁ s₇
      ((6 * (G.length + 1) + 1) + (1 + (1 + (1 + (7 * ((gSent :: G.reverse).length + 1) + 1
        + 1))))) := Ev.seq' h3 e45678 (by omega)
  have e2345678 : Ev main (seqs [.set rF gCont, .loop rF gCont cpyOutBody, .pop sM rE,
        .push sT2 rE, .set rF gCont, .loop rF gCont cpyBackBody, .pop sT2 rE]) s₀ s₇
      (1 + ((6 * (G.length + 1) + 1) + (1 + (1 + (1 + (7 *
        ((gSent :: G.reverse).length + 1) + 1 + 1)))))) := Ev.seq' hev₁ e345678 (by omega)
  have hmain : Ev main copyProg ⟨g, X⟩ s₇ (40 * (G.length + 1) + 40) := by
    unfold copyProg
    refine Ev.seq' hev₀ e2345678 (by
      simp only [List.length_cons, List.length_reverse]; omega)
  refine ⟨s₇, _, hmain, le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [hs₇f sM (by decide : sM ≠ sT2), hsM₆, hs₅f sM,
      hs₄f sM (by decide : sM ≠ sT2), hs₃M, List.reverse_cons, List.reverse_reverse,
      List.append_assoc, List.singleton_append]
  · rw [hs₇f sW (by decide : sW ≠ sT2), hsW₆, hs₅f sW,
      hs₄f sW (by decide : sW ≠ sT2), hs₃f sW (by decide : sW ≠ sM),
      hfr₂ sW (by decide : sW ≠ sM) (by decide : sW ≠ sT2), hs₁f sW,
      hs₀f sW (by decide : sW ≠ sT2), hW,
      List.reverse_cons, List.reverse_reverse, List.append_assoc, List.singleton_append]
  · exact hsT₇
  · intro j hj1 hj2 hj3
    rw [hs₇f j hj3, hfr₆ j hj1 hj2 hj3, hs₅f j, hs₄f j hj3, hs₃f j hj1,
      hfr₂ j hj1 hj3, hs₁f j, hs₀f j hj3]

/-! ## The element loop -/

theorem elemBody_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {W0 : List Glyph}
    (hh : X sW = gSent :: W0) :
    ∃ s', Ev main elemBody ⟨g, X⟩ s' 3 ∧ s'.stk 0 = X 0 ∧ s'.stk sT = X sT ∧
      s'.stk sW = X sW ∧ s'.reg rH = Glyph.eos ∧ (∀ j : Stk, s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁W, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sW) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rH) (c := Glyph.eos) (g := s₁.reg) (X := s₁.stk)
  have hit : Ev main (.ite rE gSent (.set rH Glyph.eos)
      (seqs [.pop sW rE, mvVal sT 0 sB sC, pushK 0 Glyph.cons, .set rH gCont])) s₁ s₂ 2 :=
    Ev.iteT hs₁r hev₂
  have hbody : Ev main elemBody ⟨g, X⟩ s₂ 3 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₂, hbody, ?_, ?_, ?_, hs₂r, ?_⟩
  · rw [hs₂f 0, hs₁f 0 (by decide : 0 ≠ sW)]
  · rw [hs₂f sT, hs₁f sT (by decide : sT ≠ sW)]
  · rw [hs₂f sW, hs₁W]
    exact hh.symm
  · intro j
    rw [hs₂f j]
    rcases eq_or_ne j sW with rfl | hj
    · rw [hs₁W]
      exact hh.symm
    · exact hs₁f j hj

theorem elemBody_move {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {y : Val}
    {ys' : List Val} {k' : ℕ} {A0 T0 W0 : List Glyph}
    (hW : X sW = gPend :: (List.replicate k' gPend ++ gSent :: W0))
    (hT : X sT = y.enc ++ ((ys'.map Val.enc).flatten ++ T0)) (h0 : X 0 = A0) :
    ∃ s', Ev main elemBody ⟨g, X⟩ s' (16 * (vsz y + 1) + 8) ∧
      s'.stk 0 = Glyph.cons :: y.enc ++ A0 ∧
      s'.stk sT = (ys'.map Val.enc).flatten ++ T0 ∧
      s'.stk sW = List.replicate k' gPend ++ gSent :: W0 ∧
      s'.reg rH = gCont ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sW → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁W, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := sW) (r := rE) hW
  obtain ⟨s₂, hev₂, hs₂W, hs₂r, hs₂f, -⟩ :=
    step_pop (main := main) (k := sW) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁W
  have hT₂ : s₂.stk sT = y.enc ++ ((ys'.map Val.enc).flatten ++ T0) := by
    rw [hs₂f sT (by decide : sT ≠ sW), hs₁f sT (by decide : sT ≠ sW), hT]
  have h0₂ : s₂.stk 0 = A0 := by
    rw [hs₂f 0 (by decide : 0 ≠ sW), hs₁f 0 (by decide : 0 ≠ sW), h0]
  obtain ⟨s₃, hn₃, hev₃, hb₃, hs₃T, hs₃0, -, -, hs₃f⟩ :=
    mvVal_ev_full (main := main) (a := sT) (b := 0) (c := sB) (d := sC)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₂.reg) (X := s₂.stk) (v := y) (A := (ys'.map Val.enc).flatten ++ T0) (B := A0)
      hT₂ h0₂
  have h3 : Ev main (mvVal sT 0 sB sC) s₂ s₃ (16 * (vsz y + 1)) := hev₃.mono hb₃
  obtain ⟨s₄, hev₄, hs₄0, hs₄f, hs₄r, -⟩ :=
    step_pushK (main := main) (k := 0) (c := Glyph.cons) (g := s₃.reg) (X := s₃.stk)
  obtain ⟨s₅, hev₅, hs₅r, -, hs₅f⟩ :=
    step_set (main := main) (r := rH) (c := gCont) (g := s₄.reg) (X := s₄.stk)
  have hcond : ¬ (s₁.reg rE = gSent) := by rw [hs₁r]; exact gPend_ne_gSent
  have h34 : Ev main (seqs [pushK 0 Glyph.cons, .set rH gCont]) s₃ s₅ 3 :=
    Ev.seq' hev₄ hev₅ (by omega)
  have h234 : Ev main (seqs [mvVal sT 0 sB sC, pushK 0 Glyph.cons, .set rH gCont]) s₂ s₅
      (16 * (vsz y + 1) + 3) := Ev.seq' h3 h34 (by omega)
  have h1234 : Ev main (seqs [.pop sW rE, mvVal sT 0 sB sC, pushK 0 Glyph.cons,
      .set rH gCont]) s₁ s₅ (1 + (16 * (vsz y + 1) + 3)) := Ev.seq' hev₂ h234 (by omega)
  have hbody : Ev main elemBody ⟨g, X⟩ s₅ (16 * (vsz y + 1) + 8) :=
    Ev.seq' hev₁ (Ev.iteF hcond h1234) (by omega)
  refine ⟨s₅, hbody, ?_, ?_, ?_, hs₅r, ?_⟩
  · simp only [hs₅f 0, hs₄0, hs₃0, List.cons_append]
  · rw [hs₅f sT, hs₄f sT (by decide : sT ≠ 0), hs₃T]
  · rw [hs₅f sW, hs₄f sW (by decide : sW ≠ 0),
      hs₃f sW (by decide : sW ≠ sT) (by decide : sW ≠ 0) (by decide : sW ≠ sB)
        (by decide : sW ≠ sC), hs₂W]
  · intro j hj1 hj2 hj3 hj4 hj5
    rw [hs₅f j, hs₄f j hj1,
      hs₃f j hj2 hj1 hj4 hj5, hs₂f j hj3, hs₁f j hj3]

theorem elemLoop {main : Cmd} :
    ∀ (ys : List Val) (g : Reg → Glyph) (X : Stk → List Glyph) (A0 T0 W0 : List Glyph),
      g rH = gCont → X sW = List.replicate ys.length gPend ++ gSent :: W0 →
      X sT = (ys.map Val.enc).flatten ++ T0 → X 0 = A0 →
      ∃ s', loopRuns main rH gCont elemBody (ys.length + 1) ⟨g, X⟩ s'
          (30 * ((ys.map vsz).sum + ys.length + 1)) ∧
        s'.stk 0 = twist ys ++ A0 ∧ s'.stk sT = T0 ∧ s'.stk sW = gSent :: W0 ∧
        s'.reg rH = Glyph.eos ∧
        (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sW → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  intro ys
  induction ys with
  | nil =>
      intro g X A0 T0 W0 hreg hW hT h0
      have hW' : X sW = gSent :: W0 := by simpa using hW
      obtain ⟨s₁, hev₁, hs₁0, hs₁T, hs₁W, hreg₁, hfr₁⟩ :=
        elemBody_stop (main := main) (g := g) (X := X) (W0 := W0) hW'
      refine ⟨s₁, loopRuns.mono (by omega) (loopRuns.one
        (show (⟨g, X⟩ : State).reg rH = gCont from hreg) hev₁) (by omega),
        ?_, ?_, ?_, hreg₁, ?_⟩
      · simp only [hs₁0, h0, twist, List.reverse_nil, List.map_nil, List.flatten_nil,
          List.nil_append]
      · simp only [hs₁T, hT, List.reverse_nil, List.map_nil, List.flatten_nil,
          List.nil_append]
      · simp only [hs₁W, hW']
      · intro j hj1 hj2 hj3 hj4 hj5
        rw [hfr₁ j]
  | cons y ys' ih =>
      intro g X A0 T0 W0 hreg hW hT h0
      have hT' : X sT = y.enc ++ ((ys'.map Val.enc).flatten ++ T0) := by
        rw [hT, List.map_cons, List.flatten_cons, List.append_assoc]
      have hW' : X sW = gPend :: (List.replicate ys'.length gPend ++ gSent :: W0) := by
        have hlen : (y :: ys').length = ys'.length + 1 := rfl
        rw [hW, hlen, List.replicate_succ, List.cons_append]
      obtain ⟨s₁, hev₁, hs₁0, hs₁T, hs₁W, hreg₁, hfr₁⟩ :=
        elemBody_move (main := main) (g := g) (X := X) (y := y) (ys' := ys')
          (k' := ys'.length) hW' hT' h0
      obtain ⟨s₂, hrun₂, hs₂0, hs₂T, hs₂W, hreg₂, hfr₂⟩ :=
        ih s₁.reg s₁.stk (Glyph.cons :: y.enc ++ A0) T0 W0 hreg₁ hs₁W hs₁T hs₁0
      refine ⟨s₂, loopRuns.succ'
        (show (⟨g, X⟩ : State).reg rH = gCont from hreg) hev₁ hrun₂
        (by simp only [List.length_cons, List.map_cons, List.sum_cons]; omega),
        ?_, ?_, ?_, hreg₂, ?_⟩
      · rw [hs₂0, twist_cons, List.append_assoc]
      · exact hs₂T
      · exact hs₂W
      · intro j hj1 hj2 hj3 hj4 hj5
        rw [hfr₂ j hj1 hj2 hj3 hj4 hj5, hfr₁ j hj1 hj2 hj3 hj4 hj5]

theorem inner_ev {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {ys : List Val} {k : ℕ}
    {A0 T0 W0 : List Glyph} (hk : ys.length = k)
    (hW : X sW = List.replicate k gPend ++ gSent :: W0)
    (hT : X sT = (ys.map Val.enc).flatten ++ T0) (h0 : X 0 = A0) :
    ∃ s' n, Ev main innerProg ⟨g, X⟩ s' n ∧ n ≤ 40 * ((ys.map vsz).sum + k + 1) ∧
      s'.stk 0 = twist ys ++ A0 ∧ s'.stk sT = T0 ∧ s'.stk sW = gSent :: W0 ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sW → j ≠ sB → j ≠ sC → s'.stk j = X j) := by
  obtain ⟨s₀, hev₀, hr₀, -, hf₀⟩ :=
    step_set (main := main) (r := rH) (c := gCont) (g := g) (X := X)
  have hW' : s₀.stk sW = List.replicate ys.length gPend ++ gSent :: W0 := by
    rw [hf₀ sW, hW, hk]
  have hT' : s₀.stk sT = (ys.map Val.enc).flatten ++ T0 := by rw [hf₀ sT, hT]
  have h0' : s₀.stk 0 = A0 := by rw [hf₀ 0, h0]
  obtain ⟨s₁, hrun₁, hs₁0, hs₁T, hs₁W, hreg₁, hfr₁⟩ :=
    elemLoop (main := main) ys s₀.reg s₀.stk A0 T0 W0 (by rw [hr₀]) hW' hT' h0'
  have hmain : Ev main innerProg ⟨g, X⟩ s₁ (40 * ((ys.map vsz).sum + k + 1)) := by
    unfold innerProg
    refine Ev.seq' hev₀ (loopRuns.eval hrun₁ (by rw [hreg₁]; decide)) (by rw [hk]; omega)
  refine ⟨s₁, _, hmain, le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [hs₁0]
  · rw [hs₁T]
  · rw [hs₁W]
  · intro j hj1 hj2 hj3 hj4 hj5
    rw [hfr₁ j hj1 hj2 hj3 hj4 hj5, hf₀ j]

end Work.Resample.PBChunk