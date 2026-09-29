import Mathlib
import Submission.Work.Layout.ReplicateDefs
import Submission.Work.Kernel.encodeNatBits

namespace Work.Layout

open HvdH

/-- `(HvdH.Val.int 0).enc = [HvdH.Glyph.pos, HvdH.Glyph.iend]`: zero has no bits
(`Computability.encodeNat 0 = Nat.bits 0 = []`). -/
theorem int_zero_enc : (Val.int 0).enc = [Glyph.pos, Glyph.iend] := by
  simp [Val.enc, Work.Kernel.encodeNatBits, Nat.zero_bits]

/-- Head of a concatenation, the left factor being nonempty. -/
theorem headD_append_ne_nil {l₁ l₂ : List Glyph} (h : l₁ ≠ []) (d : Glyph) :
    (l₁ ++ l₂).headD d = l₁.headD d := by
  cases l₁ with
  | nil => exact absurd rfl h
  | cons x t => rfl

/-- Work in `Submission/Work/Layout/repBodyEv.lean`.

One iteration of the `replicate` loop (`Work.Layout.repBody`, defined in
`Submission/Work/Layout/ReplicateDefs.lean` as
`seqs [Cmd.pop 1 rB, Cmd.pop 1 rB, Cmd.pop 1 rB, dupFrom 3, pushConst 0 Glyph.cons, Cmd.peek 1 rLoopG]`).
Hypothesis `hdup` is the specification of the sub-word `dupFrom 3` (copy the top value of stack 3 onto
the top of stack 0, keeping stack 3), *assumed* rather than proved here so that this file is
independent of `Submission/Work/Layout/dupFromEv.lean` (instantiate `Cd n = 16 * (n + 1)` there).
`h1` is the loop invariant for the counter on stack 1: it is a `cons`-chain of `.int 0` (i.e.
`(HvdH.intList (List.replicate j 0)).enc` for some remaining number `j` of elements), so consuming one
element means popping the three glyphs `cons`, `pos`, `iend`; this uses
`(HvdH.Val.int 0).enc = [HvdH.Glyph.pos, HvdH.Glyph.iend]`, which follows from
`Work.Kernel.encodeNatBits` (`Computability.encodeNat n = n.bits`) and `Nat.zero_bits` in
`Submission/Work/Kernel/encodeNatBits.lean`.  The last command `Cmd.peek 1 rLoopG` reads the counter's
next glyph into the loop register (`cons` = continue, `nil` = stop).  Cost: 3 pops + `Cd (vsz v)` +
`pushConst` (≤ 2) + peek (1) = `Cd (vsz v) + 6`. -/
theorem repBodyEv {main : HvdH.Cmd} {Cd : ℕ → ℕ}
    (hdup : ∀ (v : HvdH.Val) (S3 B : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      X 3 = v.enc ++ S3 → X 0 = B →
      ∃ s' n, Work.Layout.Ev main (Work.Layout.dupFrom 3) ⟨g, X⟩ s' n ∧ n ≤ Cd (HvdH.vsz v) ∧
        s'.stk 0 = v.enc ++ B ∧ s'.stk 3 = v.enc ++ S3 ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 3 → s'.stk k = X k))
    (v acc : HvdH.Val) (L' : HvdH.Val) (F S1 S3 : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h0 : X 0 = acc.enc ++ F) (h1 : X 1 = (HvdH.Val.cons (.int 0) L').enc ++ S1)
    (h3 : X 3 = v.enc ++ S3) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.repBody ⟨g, X⟩ s' n ∧ n ≤ Cd (HvdH.vsz v) + 6 ∧
      s'.stk 0 = (HvdH.Val.cons v acc).enc ++ F ∧ s'.stk 1 = L'.enc ++ S1 ∧
      s'.stk 3 = v.enc ++ S3 ∧ s'.reg Work.Layout.rLoopG = (L'.enc).headD HvdH.Glyph.eos ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 1 → k ≠ 3 → s'.stk k = X k) := by
  -- the counter on stack 1 starts with one `cons (.int 0)` cell: `cons`, `pos`, `iend`
  have hX1 : X 1 = Glyph.cons :: Glyph.pos :: Glyph.iend :: (L'.enc ++ S1) := by
    rw [h1]; simp [Val.enc, Work.Kernel.encodeNatBits, Nat.zero_bits]
  -- states of the three pops (registers are irrelevant, but `Ev` is a state-level statement)
  let G1 : Reg → Glyph := Function.update g rB Glyph.cons
  let X1 : Stk → List Glyph := Function.update X 1 (Glyph.pos :: Glyph.iend :: (L'.enc ++ S1))
  let G2 : Reg → Glyph := Function.update G1 rB Glyph.pos
  let X2 : Stk → List Glyph := Function.update X1 1 (Glyph.iend :: (L'.enc ++ S1))
  let G3 : Reg → Glyph := Function.update G2 rB Glyph.iend
  let X3 : Stk → List Glyph := Function.update X2 1 (L'.enc ++ S1)
  have e1 : Ev main (.pop 1 rB) ⟨g, X⟩ ⟨G1, X1⟩ 1 := by
    have h' := ev_pop' main 1 rB g X
    rw [hX1] at h'
    simp only [List.headD_cons, List.tail_cons] at h'
    exact h'
  have e2 : Ev main (.pop 1 rB) ⟨G1, X1⟩ ⟨G2, X2⟩ 1 := by
    have h' := ev_pop' main 1 rB G1 X1
    simp only [X1, Function.update_self, List.headD_cons, List.tail_cons] at h'
    exact h'
  have e3 : Ev main (.pop 1 rB) ⟨G2, X2⟩ ⟨G3, X3⟩ 1 := by
    have h' := ev_pop' main 1 rB G2 X2
    simp only [X2, X1, Function.update_self, List.headD_cons, List.tail_cons] at h'
    exact h'
  -- what the counter looks like after the three pops
  have hX3_0 : X3 0 = acc.enc ++ F := by
    simp only [X3, X2, X1, Function.update_of_ne (show (0 : Stk) ≠ 1 by decide)]
    exact h0
  have hX3_3 : X3 3 = v.enc ++ S3 := by
    simp only [X3, X2, X1, Function.update_of_ne (show (3 : Stk) ≠ 1 by decide)]
    exact h3
  have hX3_1 : X3 1 = L'.enc ++ S1 := by simp only [X3, X2, X1, Function.update_self]
  have hfr3 : ∀ k : Stk, k ≠ 1 → X3 k = X k := by
    intro k hk
    simp only [X3, X2, X1, Function.update_of_ne hk]
  -- copy `v` from stack 3 onto stack 0
  obtain ⟨s₂, n₂, he₂, hn₂, hs₂_0, hs₂_3, hf₂⟩ := hdup v S3 (acc.enc ++ F) G3 X3 hX3_3 hX3_0
  -- push the `cons` of the accumulator
  obtain ⟨s₃, n₃, he₃, hn₃, hs₃_0, hf₃, -, -⟩ :=
    pushConst_ev (main := main) (k := 0) (cst := Glyph.cons) (g := s₂.reg) (X := s₂.stk)
  -- read the counter's next glyph into the loop register
  let s₄ : State := ⟨Function.update s₃.reg rLoopG ((s₃.stk 1).headD Glyph.eos), s₃.stk⟩
  have e4 : Ev main (.peek 1 rLoopG) ⟨s₃.reg, s₃.stk⟩ s₄ 1 :=
    ev_peek' main 1 rLoopG s₃.reg s₃.stk
  have hZ0 : Ev main repBody ⟨g, X⟩ s₄ (1 + (1 + (1 + (n₂ + (n₃ + 1))))) := by
    show Ev main (seqs [Cmd.pop 1 rB, Cmd.pop 1 rB, Cmd.pop 1 rB, dupFrom 3, pushConst 0 Glyph.cons,
      Cmd.peek 1 rLoopG]) ⟨g, X⟩ s₄ (1 + (1 + (1 + (n₂ + (n₃ + 1)))))
    exact Ev.seqs_cons e1 (Ev.seqs_cons e2 (Ev.seqs_cons e3 (Ev.seqs_cons he₂ (Ev.seqs_cons he₃ e4))))
  refine ⟨s₄, 1 + (1 + (1 + (n₂ + (n₃ + 1)))), hZ0, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [s₄, hs₃_0, hs₂_0]
    simp [Val.enc]
  · simp only [s₄, hf₃ 1 (by decide), hf₂ 1 (by decide) (by decide), hX3_1]
  · simp only [s₄, hf₃ 3 (by decide)]
    exact hs₂_3
  · show (Function.update s₃.reg rLoopG ((s₃.stk 1).headD Glyph.eos)) rLoopG = (L'.enc).headD Glyph.eos
    rw [Function.update_self]
    have hs1 : s₃.stk 1 = L'.enc ++ S1 := by
      rw [hf₃ 1 (by decide), hf₂ 1 (by decide) (by decide), hX3_1]
    rw [hs1]
    exact headD_append_ne_nil (by
      have hv := one_le_vsz L'
      simp only [vsz] at hv
      exact List.ne_nil_of_length_pos (by omega)) Glyph.eos
  · intro k hk0 hk1 hk3
    show s₃.stk k = X k
    rw [hf₃ k hk0, hf₂ k hk0 hk3]
    exact hfr3 k hk1

end Work.Layout
