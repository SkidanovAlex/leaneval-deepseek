import Mathlib
import Submission.Work.Kernel.mapListDefs
import Submission.Work.Kernel.mapListPhaseA

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Kernel

open HvdH
open Work.Layout

/-! ## The two branches of one `mapList_bodyR` iteration -/

/-- The head of `v.enc ++ A` is never the frame marker `gMark` (`gMark = Glyph.mk 7` does not occur
in a `Val.enc`, and `v.enc` is never empty, so the head really is a glyph of `v.enc`). -/
theorem mapListRebuild_headD_ne_gMark (v : HvdH.Val) (A : List HvdH.Glyph) :
    (v.enc ++ A).headD HvdH.Glyph.eos ≠ Work.Layout.gMark := by
  intro h
  cases v with
  | int z =>
    by_cases hz : z < 0
    · exact Work.Layout.gMark_ne_neg (by simpa [HvdH.Val.enc, hz] using h.symm)
    · exact Work.Layout.gMark_ne_pos (by simpa [HvdH.Val.enc, hz] using h.symm)
  | nil => exact Work.Layout.gMark_ne_nil (by simpa [HvdH.Val.enc] using h.symm)
  | cons a b => exact Work.Layout.gMark_ne_cons (by simpa [HvdH.Val.enc] using h.symm)

/-- One `mapList_bodyR` iteration in the *hit* case: the top glyph of stack 3 is exactly the boundary
marker `gMark`, so `mapList_bodyR` sets the loop flag to `eos`, stopping the loop.  Nothing else is
changed.  Cost: `1` (`peek`) `+ 1` (`ite` test) `+ 1` (`set`) `= 3`. -/
theorem mapListRebuild_bodyR_hit {main : Cmd} {s : State} {X3 : List Glyph}
    (h3 : s.stk 3 = gMark :: X3) :
    ∃ (s' : State) (C : ℕ), Ev main mapList_bodyR s s' C ∧ C ≤ 3 ∧
      s'.stk 3 = gMark :: X3 ∧ s'.reg rLoopG = Glyph.eos ∧
      (∀ k : Stk, k ≠ 3 → s'.stk k = s.stk k) := by
  have hpeek : Ev main (.peek (3 : Stk) rA) s
      ⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ 1 :=
    ev_peek main 3 rA s
  have hit : (⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ : State).reg rA = gMark := by
    simp only [Function.update_self]
    rw [h3]
    rfl
  have hset : Ev main (.set rLoopG Glyph.eos)
      (⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ : State)
      (State.tSet (⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ : State)
        rLoopG Glyph.eos) 1 :=
    ev_set main rLoopG Glyph.eos _
  have hbody : Ev main mapList_bodyR s
      (State.tSet (⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ : State)
        rLoopG Glyph.eos) 3 := by
    unfold mapList_bodyR
    exact (Ev.seq hpeek (Ev.iteT hit hset)).mono (by omega)
  refine ⟨_, 3, hbody, le_rfl, ?_, ?_, ?_⟩
  · show (State.tSet (⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ : State)
      rLoopG Glyph.eos).stk 3 = gMark :: X3
    simp [State.tSet, State.updReg_stk, h3]
  · show (State.tSet (⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ : State)
      rLoopG Glyph.eos).reg rLoopG = Glyph.eos
    simp [State.tSet, State.updReg_apply]
  · intro k hk3
    show (State.tSet (⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ : State)
      rLoopG Glyph.eos).stk k = s.stk k
    simp [State.tSet, State.updReg_stk]

/-- One `mapList_bodyR` iteration in the *moving* case: the top glyph of stack 3 is not the boundary
marker, so the value `v` sitting on top of stack 3 is moved to stack 0 and a `cons` glyph is pushed
on top of it, and the loop flag is reset to `cons`.

Cost: `1` (`peek`) `+ 1` (`ite` test) `+ 16 * (vsz v + 1)` (`mvVal`) `+ 2` (`pushConst`) `+ 1`
(`set`) `= 16 * (vsz v + 1) + 5`. -/
theorem mapListRebuild_bodyR_miss {main : Cmd} {s : State} {v : Val} {A : List Glyph}
    (h3 : s.stk 3 = v.enc ++ A) (hhead : (v.enc ++ A).headD Glyph.eos ≠ gMark) :
    ∃ (s' : State) (C : ℕ), Ev main mapList_bodyR s s' C ∧ C ≤ 16 * (vsz v + 1) + 5 ∧
      s'.stk 3 = A ∧ s'.stk 0 = Glyph.cons :: (v.enc ++ s.stk 0) ∧
      s'.reg rLoopG = Glyph.cons ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 3 → s'.stk k = s.stk k) := by
  -- the test of the `ite`: `peek` reads the head of stack 3, a glyph of `v.enc`, never the marker
  have hpeek : Ev main (.peek (3 : Stk) rA) s
      ⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ 1 :=
    ev_peek main 3 rA s
  have hne : (⟨Function.update s.reg rA ((s.stk 3).headD .eos), s.stk⟩ : State).reg rA ≠ gMark := by
    simp only [Function.update_self]
    rw [h3]
    exact hhead
  -- move the value `v` from stack 3 to the value stack
  obtain ⟨s₁, n₁, hmv, hn₁, h1_3, h1_0, h1_4, h1_5, h1_fr⟩ :=
    mvVal_ev_full (main := main) (a := (3 : Stk)) (b := (0 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update s.reg rA ((s.stk 3).headD .eos)) (X := s.stk)
      (v := v) (A := A) (B := s.stk 0) h3 rfl
  -- push the `cons` glyph on top of it
  obtain ⟨s₂, n₂, hpush, hn₂, h2_0, h2_fr, -, -⟩ :=
    pushConst_ev (main := main) (k := (0 : Stk)) (cst := Glyph.cons) (g := s₁.reg) (X := s₁.stk)
  -- reset the loop flag
  have hset : Ev main (.set rLoopG Glyph.cons) s₂ (State.tSet s₂ rLoopG Glyph.cons) 1 :=
    ev_set main rLoopG Glyph.cons s₂
  have hbody : Ev main mapList_bodyR s (State.tSet s₂ rLoopG Glyph.cons)
      (16 * (vsz v + 1) + 5) := by
    unfold mapList_bodyR
    exact (Ev.seq hpeek (Ev.iteF hne (Ev.seq hmv (Ev.seq hpush hset)))).mono (by omega)
  refine ⟨State.tSet s₂ rLoopG Glyph.cons, _, hbody, le_rfl, ?_, ?_, ?_, ?_⟩
  · show s₂.stk 3 = A
    rw [h2_fr 3 (by decide), h1_3]
  · show s₂.stk 0 = Glyph.cons :: (v.enc ++ s.stk 0)
    rw [h2_0, h1_0]
  · simp [State.tSet, State.updReg_apply]
  · intro k hk0 hk3
    show s₂.stk k = s.stk k
    rcases eq_or_ne k (4 : Stk) with h4 | h4
    · rw [h4, h2_fr 4 (by decide), h1_4]
    · rcases eq_or_ne k (5 : Stk) with h5 | h5
      · rw [h5, h2_fr 5 (by decide), h1_5]
      · rw [h2_fr k hk0, h1_fr k hk3 hk0 h4 h5]

/-! ## The rebuild loop -/

set_option maxHeartbeats 1600000 in
/-- `mapList` rebuild phase: `Work.Kernel.mapList_bodyR` (defined in `Submission/Work/Kernel/mapListDefs.lean`), run as `Cmd.loop Work.Layout.rLoopG Glyph.cons mapList_bodyR`.  The state has stack 3 = `encs bs ++ gMark :: X3` (values head on top) and stack 0 = `encs (ofList cs :: rest) ++ R`.  While the top glyph of stack 3 is not `gMark`, the body moves the top value of stack 3 to stack 0 and then pushes a single `cons` glyph on top of it, so that stack 0 becomes `encs (ofList (b :: cs) :: rest) ++ R` for the moved value `b` (note `ofList (b :: cs) = cons b (ofList cs)` has encoding `cons :: b.enc ++ (ofList cs).enc`, hence the order "move the value, then push `cons`"); it stops at the marker, leaving stack 3 = `gMark :: X3`.  Processing `bs` head first gives `bs.reverse ++ cs`.  `Work.Layout.mvVal_ev_full` (cost `≤ 16 * (vsz v + 1)`, restores stacks 4,5) and `Work.Layout.pushConst` (2 steps) are the tools.  Template: `Work.Kernel.mapList_phaseA` in `Submission/Work/Kernel/mapListPhaseA.lean`.  To be placed in namespace `Work.Kernel`. -/
theorem mapListRebuild (main : HvdH.Cmd) (bs cs rest : List HvdH.Val) (R : List HvdH.Glyph)
    (s : HvdH.State) (L : ℕ) (X3 : List HvdH.Glyph)
    (hr : s.reg Work.Layout.rLoopG = HvdH.Glyph.cons)
    (hsz : ∀ x ∈ bs, HvdH.vsz x ≤ L)
    (h3 : s.stk 3 = HvdH.encs bs ++ Work.Layout.gMark :: X3)
    (h0 : s.stk 0 = HvdH.encs (HvdH.ofList cs :: rest) ++ R) :
    ∃ (s' : HvdH.State) (C : ℕ),
      Work.Layout.loopRuns main Work.Layout.rLoopG HvdH.Glyph.cons Work.Kernel.mapList_bodyR
        (bs.length + 1) s s' C ∧
      C ≤ bs.length * (16 * (L + 1) + 6) + 5 ∧
      s'.stk 3 = Work.Layout.gMark :: X3 ∧
      s'.stk 0 = HvdH.encs (HvdH.ofList (bs.reverse ++ cs) :: rest) ++ R ∧
      s'.reg Work.Layout.rLoopG = HvdH.Glyph.eos ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 3 → s'.stk k = s.stk k) := by
  -- everything is generalised so that the induction hypothesis is available for `v :: cs`
  have key : ∀ (bs cs rest : List HvdH.Val) (R : List HvdH.Glyph) (s : HvdH.State)
      (X3 : List HvdH.Glyph),
      s.reg Work.Layout.rLoopG = HvdH.Glyph.cons →
      (∀ x ∈ bs, HvdH.vsz x ≤ L) →
      s.stk 3 = HvdH.encs bs ++ Work.Layout.gMark :: X3 →
      s.stk 0 = HvdH.encs (HvdH.ofList cs :: rest) ++ R →
      ∃ (s' : HvdH.State) (C : ℕ),
        Work.Layout.loopRuns main Work.Layout.rLoopG HvdH.Glyph.cons Work.Kernel.mapList_bodyR
          (bs.length + 1) s s' C ∧
        C ≤ bs.length * (16 * (L + 1) + 6) + 5 ∧
        s'.stk 3 = Work.Layout.gMark :: X3 ∧
        s'.stk 0 = HvdH.encs (HvdH.ofList (bs.reverse ++ cs) :: rest) ++ R ∧
        s'.reg Work.Layout.rLoopG = HvdH.Glyph.eos ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 3 → s'.stk k = s.stk k) := by
    intro bs
    induction bs with
    | nil =>
      intro cs rest R s X3 hr hsz h3 h0
      -- the marker is already on top of stack 3: one iteration (cost `3`) stops the loop
      have h3' : s.stk 3 = gMark :: X3 := by simpa [encs_nil] using h3
      obtain ⟨s', C', hev, hC', hs'3, hs'r, hfr⟩ := mapListRebuild_bodyR_hit (main := main) h3'
      refine ⟨s', C' + 1, loopRuns.one hr hev, ?_, hs'3, ?_, hs'r, ?_⟩
      · simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]; omega
      · simp only [List.reverse_nil, List.nil_append]
        rw [hfr 0 (by decide)]
        exact h0
      · intro k hk0 hk3; exact hfr k hk3
    | cons v ws ih =>
      intro cs rest R s X3 hr hsz h3 h0
      have hv : vsz v ≤ L := hsz v (by simp)
      have hsz' : ∀ x ∈ ws, vsz x ≤ L := fun x hx => hsz x (List.mem_cons_of_mem v hx)
      -- the top glyph of stack 3 is the head of `v.enc`, never the marker: the moving branch runs
      have h3' : s.stk 3 = v.enc ++ (encs ws ++ gMark :: X3) := by
        rw [h3, encs_cons, List.append_assoc]
      obtain ⟨s₁, n₁, hev₁, hn₁, hs₁3, hs₁0, hs₁r, hfr₁⟩ :=
        mapListRebuild_bodyR_miss (main := main) (A := encs ws ++ gMark :: X3) h3'
          (mapListRebuild_headD_ne_gMark v (encs ws ++ gMark :: X3))
      have hn₁' : n₁ ≤ 16 * (L + 1) + 5 := by omega
      -- the moved value `v` becomes the head of the rebuilt list
      have h0₁' : s₁.stk 0 = encs (ofList (v :: cs) :: rest) ++ R := by
        rw [hs₁0, h0, mapList_encs_ofList_cons]
        simp only [List.cons_append, List.append_assoc]
      obtain ⟨s₂, C₂, hrun₂, hC₂, hs₂3, hs₂0, hs₂r, hfr₂⟩ :=
        ih (v :: cs) rest R s₁ X3 hs₁r hsz' hs₁3 h0₁'
      have hrev : (v :: ws).reverse ++ cs = ws.reverse ++ (v :: cs) := by
        rw [List.reverse_cons, List.append_assoc, List.singleton_append]
      refine ⟨s₂, 16 * (L + 1) + 5 + C₂ + 1, ?_, ?_, hs₂3, ?_, hs₂r, ?_⟩
      · exact loopRuns.succ' hr hev₁ hrun₂ (by omega)
      · have hkey : (v :: ws).length * (16 * (L + 1) + 6) + 5
            = ws.length * (16 * (L + 1) + 6) + 5 + (16 * (L + 1) + 6) := by
          simp only [List.length_cons]; ring
        rw [hkey]; omega
      · rw [hrev, hs₂0]
      · intro k hk0 hk3; rw [hfr₂ k hk0 hk3, hfr₁ k hk0 hk3]
  exact key bs cs rest R s X3 hr hsz h3 h0

end Work.Kernel
