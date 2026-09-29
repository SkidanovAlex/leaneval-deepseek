import Mathlib
import Submission.Work.Kernel.mapListDefs
import Submission.Work.Kernel.mapListPhaseA

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Kernel

open HvdH
open Work.Layout

/-! ## Elementary: no `Val` encoding starts with the frame marker -/

/-- The head of `v.enc ++ A` is never the boundary marker `gMark` (`gMark = Glyph.mk 7` does not
occur in a `Val.enc`, and `v.enc` is never empty so the head really is a glyph of `v.enc`). -/
theorem mapList_enc_headD_ne_gMark (v : HvdH.Val) (A : List HvdH.Glyph) :
    (v.enc ++ A).headD HvdH.Glyph.eos ≠ Work.Layout.gMark := by
  intro h
  cases v with
  | int z =>
    by_cases hz : z < 0
    · exact Work.Layout.gMark_ne_neg (by simpa [HvdH.Val.enc, hz] using h.symm)
    · exact Work.Layout.gMark_ne_pos (by simpa [HvdH.Val.enc, hz] using h.symm)
  | nil => exact Work.Layout.gMark_ne_nil (by simpa [HvdH.Val.enc] using h.symm)
  | cons a b => exact Work.Layout.gMark_ne_cons (by simpa [HvdH.Val.enc] using h.symm)

/-! ## The two branches of one `mapList_bodyRev` iteration -/

/-- One `mapList_bodyRev` iteration when the top glyph of stack 1 is the marker `gMark`: nothing is
moved, the loop register is set to `eos`, so the loop stops.  Cost `1` (`peek`) `+ 1` (`ite` test)
`+ 1` (`set`) `= 3`. -/
theorem mapList_bodyRev_hit {main : Cmd} {s : State} {X1 : List Glyph}
    (h1 : s.stk 1 = gMark :: X1) :
    ∃ (s' : State) (C : ℕ), Ev main mapList_bodyRev s s' C ∧ C ≤ 3 ∧
      s'.stk 1 = s.stk 1 ∧ s'.stk 2 = s.stk 2 ∧ s'.reg rLoopG = Glyph.eos ∧
      (∀ k : Stk, k ≠ 1 → s'.stk k = s.stk k) := by
  have hpeek : Ev main (.peek (1 : Stk) rA) s
      ⟨Function.update s.reg rA ((s.stk 1).headD .eos), s.stk⟩ 1 :=
    ev_peek main 1 rA s
  have hne : (⟨Function.update s.reg rA ((s.stk 1).headD .eos), s.stk⟩ : State).reg rA = gMark := by
    simp only [Function.update_self]
    rw [h1]
    rfl
  have hset : Ev main (.set rLoopG Glyph.eos)
      (⟨Function.update s.reg rA ((s.stk 1).headD .eos), s.stk⟩ : State)
      (State.tSet (⟨Function.update s.reg rA ((s.stk 1).headD .eos), s.stk⟩ : State)
        rLoopG Glyph.eos) 1 :=
    ev_set main rLoopG Glyph.eos _
  have hbody : Ev main mapList_bodyRev s
      (State.tSet (⟨Function.update s.reg rA ((s.stk 1).headD .eos), s.stk⟩ : State)
        rLoopG Glyph.eos) 3 := by
    unfold mapList_bodyRev
    exact (Ev.seq hpeek (Ev.iteT hne hset)).mono (by omega)
  refine ⟨_, 3, hbody, le_rfl, ?_, ?_, ?_, ?_⟩
  · show s.stk 1 = s.stk 1; rfl
  · show s.stk 2 = s.stk 2; rfl
  · simp [State.tSet, State.updReg]
  · intro k hk1
    show s.stk k = s.stk k; rfl

/-- One `mapList_bodyRev` iteration in the *moving* case: the top glyph of stack 1 is not the marker,
so the value `v` sitting on top of stack 1 is moved to stack 2 and the loop register is reset to
`cons`.  Cost `1` (`peek`) `+ 1` (`ite` test) `+ 16 * (vsz v + 1)` (`mvVal`) `+ 1` (`set`)
`= 16 * (vsz v + 1) + 3`. -/
theorem mapList_bodyRev_miss {main : Cmd} {s : State} {v : Val} {A : List Glyph}
    (h1 : s.stk 1 = v.enc ++ A) (hhead : (v.enc ++ A).headD Glyph.eos ≠ gMark) :
    ∃ (s' : State) (C : ℕ), Ev main mapList_bodyRev s s' C ∧ C ≤ 16 * (vsz v + 1) + 3 ∧
      s'.stk 1 = A ∧ s'.stk 2 = v.enc ++ s.stk 2 ∧ s'.reg rLoopG = Glyph.cons ∧
      (∀ k : Stk, k ≠ 1 → k ≠ 2 → s'.stk k = s.stk k) := by
  have hpeek : Ev main (.peek (1 : Stk) rA) s
      ⟨Function.update s.reg rA ((s.stk 1).headD .eos), s.stk⟩ 1 :=
    ev_peek main 1 rA s
  have hne :
      (⟨Function.update s.reg rA ((s.stk 1).headD .eos), s.stk⟩ : State).reg rA ≠ gMark := by
    simp only [Function.update_self]
    rw [h1]
    exact hhead
  obtain ⟨s₁, n₁, hmv, hn₁, h1_1, h1_2, h1_4, h1_5, h1_fr⟩ :=
    mvVal_ev_full (main := main) (a := (1 : Stk)) (b := (2 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := Function.update s.reg rA ((s.stk 1).headD .eos)) (X := s.stk)
      (v := v) (A := A) (B := s.stk 2) h1 rfl
  have hset : Ev main (.set rLoopG Glyph.cons) s₁ (State.tSet s₁ rLoopG Glyph.cons) 1 :=
    ev_set main rLoopG Glyph.cons s₁
  have hbody : Ev main mapList_bodyRev s (State.tSet s₁ rLoopG Glyph.cons)
      (16 * (vsz v + 1) + 3) := by
    unfold mapList_bodyRev
    exact (Ev.seq hpeek (Ev.iteF hne (Ev.seq hmv hset))).mono (by omega)
  refine ⟨_, _, hbody, le_rfl, ?_, ?_, ?_, ?_⟩
  · show s₁.stk 1 = A; exact h1_1
  · show s₁.stk 2 = v.enc ++ s.stk 2; exact h1_2
  · simp [State.tSet, State.updReg]
  · intro k hk1 hk2
    show s₁.stk k = s.stk k
    rcases eq_or_ne k (4 : Stk) with h4 | h4
    · rw [h4]; exact h1_4
    · rcases eq_or_ne k (5 : Stk) with h5 | h5
      · rw [h5]; exact h1_5
      · exact h1_fr k hk1 hk2 h4 h5

/-! ## Phase B (reversal): the loop -/

/-- `mapList` phase "reversal": `Work.Kernel.mapList_bodyRev` (defined in `Submission/Work/Kernel/mapListDefs.lean`, together with its value mover `Work.Layout.mvVal` and the marker `Work.Layout.gMark`) run as `Cmd.loop Work.Layout.rLoopG Glyph.cons mapList_bodyRev`.  It moves the values of `bs` one by one, top first, from stack 1 to stack 2, stopping when the top glyph of stack 1 is the marker `gMark` (which it leaves in place); `Work.Layout.mvVal` moves one value at cost `≤ 16 * (vsz v + 1)` (see `Work.Layout.mvVal_ev_full`).  A worked template of the same shape is `Work.Kernel.mapList_phaseA` in `Submission/Work/Kernel/mapListPhaseA.lean`.  To be placed in namespace `Work.Kernel`. -/
theorem mapListPhaseRev (main : HvdH.Cmd) (bs : List HvdH.Val) (s : HvdH.State) (L : ℕ)
    (X1 : List HvdH.Glyph)
    (hr : s.reg Work.Layout.rLoopG = HvdH.Glyph.cons)
    (hsz : ∀ x ∈ bs, HvdH.vsz x ≤ L)
    (h1 : s.stk 1 = HvdH.encs bs ++ Work.Layout.gMark :: X1) :
    ∃ (s' : HvdH.State) (C : ℕ),
      Work.Layout.loopRuns main Work.Layout.rLoopG HvdH.Glyph.cons Work.Kernel.mapList_bodyRev
        (bs.length + 1) s s' C ∧
      C ≤ bs.length * (16 * (L + 1) + 4) + 5 ∧
      s'.stk 1 = Work.Layout.gMark :: X1 ∧
      s'.stk 2 = HvdH.encs bs.reverse ++ s.stk 2 ∧
      s'.reg Work.Layout.rLoopG = HvdH.Glyph.eos ∧
      (∀ k : HvdH.Stk, k ≠ 1 → k ≠ 2 → s'.stk k = s.stk k) := by
  induction bs generalizing s with
  | nil =>
    have h1' : s.stk 1 = gMark :: X1 := by simpa [encs_nil] using h1
    obtain ⟨s', C', hev, hC', hs'1, hs'2, hs'r, hfr⟩ := mapList_bodyRev_hit (main := main) h1'
    refine ⟨s', C' + 1, loopRuns.one hr hev, ?_, ?_, ?_, hs'r, ?_⟩
    · simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]; omega
    · rw [hs'1]; exact h1'
    · simp only [List.reverse_nil, encs_nil, List.nil_append]; exact hs'2
    · intro k hk1 hk2; exact hfr k hk1
  | cons x xs ih =>
    have h1' : s.stk 1 = x.enc ++ (encs xs ++ gMark :: X1) := by
      rw [h1, encs_cons, List.append_assoc]
    obtain ⟨s₁, C₁, hev₁, hC₁, hs₁1, hs₁2, hs₁r, hfr₁⟩ :=
      mapList_bodyRev_miss (main := main) (s := s) (v := x) (A := encs xs ++ gMark :: X1) h1'
        (mapList_enc_headD_ne_gMark x (encs xs ++ gMark :: X1))
    have hC₁' : C₁ ≤ 16 * (L + 1) + 3 := by
      have hx := hsz x (by simp)
      omega
    obtain ⟨s₂, C₂, hrun₂, hC₂, hs₂1, hs₂2, hs₂r, hfr₂⟩ :=
      ih (s := s₁) hs₁r (fun y hy => hsz y (List.mem_cons_of_mem x hy)) hs₁1
    refine ⟨s₂, (16 * (L + 1) + 3) + C₂ + 1, ?_, ?_, hs₂1, ?_, hs₂r, ?_⟩
    · exact loopRuns.succ' hr (hev₁.mono hC₁') hrun₂ (le_refl _)
    · have hkey : (x :: xs).length * (16 * (L + 1) + 4) + 5
          = xs.length * (16 * (L + 1) + 4) + 5 + (16 * (L + 1) + 4) := by
        simp only [List.length_cons]; ring
      rw [hkey]; omega
    · rw [hs₂2, hs₁2, mapList_encs_reverse_cons, List.append_assoc]
    · intro k hk1 hk2; rw [hfr₂ k hk1 hk2, hfr₁ k hk1 hk2]

end Work.Kernel
