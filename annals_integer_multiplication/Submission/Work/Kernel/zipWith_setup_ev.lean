import Mathlib
import Submission.Work.Kernel.zipWithDefs

namespace Work.Kernel

open HvdH
open Work.Layout

/-- Setup of `zipWith`: push the frame marker `gMark` on stack 3, move the two `cons`-chains
`ofList X0` and `ofList Y0` from the value stack to stacks 1 and 2, and set the loop flag.

Each chain is moved by a single `Work.Layout.mvVal` (cost `≤ 16 * (vsz + 1)`); the scratch stacks
`4` and `5` used by the mover are restored, so the only stacks that change are `0, 1, 2, 3`. -/
theorem zipWith_setup_ev (main : HvdH.Cmd) :
    ∀ (X0 Y0 rest0 : List HvdH.Val) (R : List HvdH.Glyph) (s : HvdH.State),
      s.stk 0 = HvdH.encs (HvdH.ofList X0 :: HvdH.ofList Y0 :: rest0) ++ R →
      ∃ s' n, HvdH.Eval main Work.Kernel.zipWith_setupCmd s s' n ∧
        n ≤ 3 + 16 * (HvdH.vsz (HvdH.ofList X0) + 1) + 16 * (HvdH.vsz (HvdH.ofList Y0) + 1) ∧
        s'.stk 0 = HvdH.encs rest0 ++ R ∧
        s'.stk 1 = (HvdH.ofList X0).enc ++ s.stk 1 ∧
        s'.stk 2 = (HvdH.ofList Y0).enc ++ s.stk 2 ∧
        s'.stk 3 = Work.Layout.gMark :: s.stk 3 ∧
        s'.reg Work.Layout.rLoopG = HvdH.Glyph.cons ∧
        (∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → s'.stk j = s.stk j) := by
  intro X0 Y0 rest0 R s h0
  -- 1. push the boundary marker on stack 3
  obtain ⟨s1, n1, hev1, hn1, h1_3, h1_fr, -, -⟩ :=
    pushConst_ev (main := main) (k := (3 : Stk)) (cst := gMark) (g := s.reg) (X := s.stk)
  -- 2. move `ofList X0` from the value stack to stack 1
  have h1_0 : s1.stk 0 = (ofList X0).enc ++ (encs (ofList Y0 :: rest0) ++ R) := by
    rw [h1_fr 0 (by decide), h0, encs_cons, List.append_assoc]
  obtain ⟨s2, n2, hev2, hn2, h2_0, h2_1, h2_4, h2_5, h2_fr⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := (1 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s1.reg) (X := s1.stk) (v := ofList X0)
      (A := encs (ofList Y0 :: rest0) ++ R) (B := s1.stk 1) h1_0 rfl
  -- 3. move `ofList Y0` from the value stack to stack 2
  have h2_0' : s2.stk 0 = (ofList Y0).enc ++ (encs rest0 ++ R) := by
    rw [h2_0, encs_cons, List.append_assoc]
  obtain ⟨s3, n3, hev3, hn3, h3_0, h3_2, h3_4, h3_5, h3_fr⟩ :=
    mvVal_ev_full (main := main) (a := (0 : Stk)) (b := (2 : Stk)) (c := (4 : Stk))
      (d := (5 : Stk))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s2.reg) (X := s2.stk) (v := ofList Y0)
      (A := encs rest0 ++ R) (B := s2.stk 2) h2_0' rfl
  -- 4. set the loop flag
  have hev4 : Ev main (.set rLoopG Glyph.cons) s3 (State.tSet s3 rLoopG Glyph.cons) 1 :=
    ev_set main rLoopG Glyph.cons s3
  -- glue the four chunks together
  have h234 : Ev main (seqs [mvVal 0 1 4 5, mvVal 0 2 4 5, .set rLoopG Glyph.cons]) s1
      (State.tSet s3 rLoopG Glyph.cons) (n2 + (n3 + 1)) := by
    show Ev main (.seq (mvVal 0 1 4 5) (.seq (mvVal 0 2 4 5) (.set rLoopG Glyph.cons))) s1
      (State.tSet s3 rLoopG Glyph.cons) (n2 + (n3 + 1))
    exact Ev.seq hev2 (Ev.seq hev3 hev4)
  have hall : Ev main
      (seqs [pushConst 3 gMark, mvVal 0 1 4 5, mvVal 0 2 4 5, .set rLoopG Glyph.cons])
      ⟨s.reg, s.stk⟩ (State.tSet s3 rLoopG Glyph.cons) (n1 + (n2 + (n3 + 1))) := by
    show Ev main (.seq (pushConst 3 gMark)
        (.seq (mvVal 0 1 4 5) (.seq (mvVal 0 2 4 5) (.set rLoopG Glyph.cons)))) ⟨s.reg, s.stk⟩
      (State.tSet s3 rLoopG Glyph.cons) (n1 + (n2 + (n3 + 1)))
    exact Ev.seq hev1 h234
  -- read off what the run establishes about `s3`
  have hs3_0 : s3.stk 0 = encs rest0 ++ R := h3_0
  have hs3_1 : s3.stk 1 = (ofList X0).enc ++ s.stk 1 := by
    rw [h3_fr 1 (by decide) (by decide) (by decide) (by decide), h2_1, h1_fr 1 (by decide)]
  have hs3_2 : s3.stk 2 = (ofList Y0).enc ++ s.stk 2 := by
    rw [h3_2, h2_fr 2 (by decide) (by decide) (by decide) (by decide), h1_fr 2 (by decide)]
  have hs3_3 : s3.stk 3 = gMark :: s.stk 3 := by
    rw [h3_fr 3 (by decide) (by decide) (by decide) (by decide),
      h2_fr 3 (by decide) (by decide) (by decide) (by decide), h1_3]
  have hs3_fr : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → s3.stk j = s.stk j := by
    intro j hj0 hj1 hj2 hj3
    rcases eq_or_ne j (4 : Stk) with h4 | h4
    · subst h4; rw [h3_4, h2_4, h1_fr 4 (by decide)]
    · rcases eq_or_ne j (5 : Stk) with h5 | h5
      · subst h5; rw [h3_5, h2_5, h1_fr 5 (by decide)]
      · rw [h3_fr j hj0 hj2 h4 h5, h2_fr j hj0 hj1 h4 h5, h1_fr j hj3]
  obtain ⟨nf, heval, hnf⟩ := hall
  refine ⟨State.tSet s3 rLoopG Glyph.cons, nf, ?_, ?_, hs3_0, hs3_1, hs3_2, hs3_3, ?_, hs3_fr⟩
  · exact heval
  · have h1 : n1 ≤ 2 := hn1
    have h2 : n2 ≤ 16 * (vsz (ofList X0) + 1) := hn2
    have h3 : n3 ≤ 16 * (vsz (ofList Y0) + 1) := hn3
    omega
  · simp [State.tSet, State.updReg]

end Work.Kernel
