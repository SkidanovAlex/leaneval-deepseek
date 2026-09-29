import Mathlib
import Submission.Work.IntLib.evCarryDefs

/-!
# `IntLib` / `evCA` / `stepAEv`

`EvC.stepA` is one iteration (the arithmetic part) of the streaming window addition of
`EvC.evCarryProg`: it peeks the current bit of the window `W` (stack `aW`), pops the current bit of
the digit `hbits` (stack `aB`) when there is one, runs the one-bit adder `EvC.stepAdd` and leaves the
sum bit in `rSa` and the new carry in `rKa`.

`stepAEv` is the corresponding loop-step lemma: from the invariant `EvC.strP` at step `k` (with the
carry register holding `EvC.carryC W hbits false k` and `k < EvC.addN W hbits`, so the two bit
streams are not both exhausted) the program reaches, in at most `12` steps, a state still satisfying
`EvC.strP` at step `k+1`, with `rSa`/`rKa` holding the sum/carry bit of the two current bits, and all
stacks but `aW` and `aB` untouched.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.evCA

open HvdH

/-! ## Small helpers -/

theorem stepAEv_bit_ne_iend (b : Bool) : Glyph.bit b ≠ Glyph.iend := fun h => by cases h

theorem stepAEv_sumBit_swap (a b c : Bool) : EvC.sumBit a b c = EvC.sumBit b a c := by
  rcases a <;> rcases b <;> rcases c <;> decide

theorem stepAEv_carryBit_swap (a b c : Bool) : EvC.carryBit a b c = EvC.carryBit b a c := by
  rcases a <;> rcases b <;> rcases c <;> decide

theorem stepAEv_drop_ne_nil_iff (xs : List Bool) (k : ℕ) : xs.drop k ≠ [] ↔ k < xs.length := by
  constructor
  · intro h
    by_contra hk
    exact h (List.drop_eq_nil_of_le (by omega))
  · intro h
    exact List.ne_nil_of_length_pos (by rw [List.length_drop]; omega)

/-! ## The three configurations of `stepA` -/

/-- `EvC.stepA` with a bit on top of both the window (`aW`) and the digit buffer (`aB`). -/
theorem stepA_bit_bit_loc (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (restW restB : List Glyph) (a b c : Bool)
    (hW : X aW = Glyph.bit a :: restW)
    (hB : X aB = Glyph.bit b :: restB)
    (hc : g EvC.rKa = Glyph.bit c) :
    ∃ (s' : State) (n : ℕ), Work.Layout.Ev main EvC.stepA ⟨g, X⟩ s' n ∧ n ≤ 12 ∧
      s'.stk aW = restW ∧ s'.stk aB = restB ∧
      s'.reg EvC.rSa = Glyph.bit (EvC.sumBit a b c) ∧
      s'.reg EvC.rKa = Glyph.bit (EvC.carryBit a b c) ∧
      (∀ j : Stk, j ≠ aW → j ≠ aB → s'.stk j = X j) := by
  let G1 : Reg → Glyph := Function.update g EvC.rWa (Glyph.bit a)
  have e1 : Work.Layout.Ev main (.peek aW EvC.rWa) ⟨g, X⟩ ⟨G1, X⟩ 1 := by
    have h := Work.Layout.ev_peek' main aW EvC.rWa g X
    simp only [hW, List.headD_cons] at h
    simpa [G1] using h
  have ht1 : G1 EvC.rWa ≠ Shift.gmk aW := by
    have h : G1 EvC.rWa = Glyph.bit a := by simp [G1]
    rw [h]
    exact Shift.bit_ne_gmk aW a
  let X2 : Stk → List Glyph := Function.update X aW restW
  let G2 : Reg → Glyph := Function.update G1 EvC.rWa (Glyph.bit a)
  have e2 : Work.Layout.Ev main (.pop aW EvC.rWa) ⟨G1, X⟩ ⟨G2, X2⟩ 1 := by
    have h := Work.Layout.ev_pop' main aW EvC.rWa G1 X
    simp only [hW, List.headD_cons, List.tail_cons] at h
    simpa [G2, X2] using h
  have hX2B : X2 aB = Glyph.bit b :: restB := by
    simp only [X2, Function.update_of_ne (by decide : aB ≠ aW)]
    exact hB
  let G3 : Reg → Glyph := Function.update G2 EvC.rHa (Glyph.bit b)
  have e3 : Work.Layout.Ev main (.peek aB EvC.rHa) ⟨G2, X2⟩ ⟨G3, X2⟩ 1 := by
    have h := Work.Layout.ev_peek' main aB EvC.rHa G2 X2
    simp only [hX2B, List.headD_cons] at h
    simpa [G3] using h
  have ht2 : G3 EvC.rHa ≠ Glyph.iend := by
    have h : G3 EvC.rHa = Glyph.bit b := by simp [G3]
    rw [h]
    exact stepAEv_bit_ne_iend b
  let X4 : Stk → List Glyph := Function.update X2 aB restB
  let G4 : Reg → Glyph := Function.update G3 EvC.rHa (Glyph.bit b)
  have e4 : Work.Layout.Ev main (.pop aB EvC.rHa) ⟨G3, X2⟩ ⟨G4, X4⟩ 1 := by
    have h := Work.Layout.ev_pop' main aB EvC.rHa G3 X2
    simp only [hX2B, List.headD_cons, List.tail_cons] at h
    simpa [G4, X4] using h
  have hG4w : G4 EvC.rWa = Glyph.bit a := by
    simp only [G4, G3, G2, Function.update_of_ne (by decide : EvC.rWa ≠ EvC.rHa),
      Function.update_self]
  have hG4h : G4 EvC.rHa = Glyph.bit b := by simp only [G4, Function.update_self]
  have hG4k : G4 EvC.rKa = Glyph.bit c := by
    simp only [G4, G3, G2, G1, Function.update_of_ne (by decide : EvC.rKa ≠ EvC.rHa),
      Function.update_of_ne (by decide : EvC.rKa ≠ EvC.rWa)]
    exact hc
  let s' : State := ((⟨G4, X4⟩ : State).updReg EvC.rSa (Glyph.bit (EvC.sumBit a b c))).updReg
    EvC.rKa (Glyph.bit (EvC.carryBit a b c))
  have e5 : Work.Layout.Ev main (EvC.stepAdd EvC.rWa EvC.rHa EvC.rKa EvC.rSa) ⟨G4, X4⟩ s' 5 :=
    ⟨5, EvC.stepAddEv main EvC.rWa EvC.rHa EvC.rKa EvC.rSa ⟨G4, X4⟩ a b c hG4w hG4h hG4k,
      le_rfl⟩
  have e6 : Work.Layout.Ev main
      (Work.Layout.seqs [Cmd.pop aB EvC.rHa, EvC.stepAdd EvC.rWa EvC.rHa EvC.rKa EvC.rSa])
      ⟨G3, X2⟩ s' 6 := Work.Layout.Ev.seq e4 e5
  have e7 : Work.Layout.Ev main
      (Cmd.ite EvC.rHa Glyph.iend
        (Work.Layout.seqs [Cmd.set EvC.rZa (Glyph.bit false),
          EvC.stepAdd EvC.rWa EvC.rZa EvC.rKa EvC.rSa])
        (Work.Layout.seqs [Cmd.pop aB EvC.rHa, EvC.stepAdd EvC.rWa EvC.rHa EvC.rKa EvC.rSa]))
      ⟨G3, X2⟩ s' 7 := Work.Layout.Ev.iteF ht2 e6
  have e8 : Work.Layout.Ev main
      (Work.Layout.seqs [Cmd.pop aW EvC.rWa, Cmd.peek aB EvC.rHa,
        Cmd.ite EvC.rHa Glyph.iend
          (Work.Layout.seqs [Cmd.set EvC.rZa (Glyph.bit false),
            EvC.stepAdd EvC.rWa EvC.rZa EvC.rKa EvC.rSa])
          (Work.Layout.seqs [Cmd.pop aB EvC.rHa,
            EvC.stepAdd EvC.rWa EvC.rHa EvC.rKa EvC.rSa])])
      ⟨G1, X⟩ s' 9 := Work.Layout.Ev.seq e2 (Work.Layout.Ev.seq e3 e7)
  have e9 : Work.Layout.Ev main EvC.stepA ⟨g, X⟩ s' 11 :=
    Work.Layout.Ev.seq e1 (Work.Layout.Ev.iteF ht1 e8)
  refine ⟨s', 11, e9, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · show X4 aW = restW
    simp only [X4, X2, Function.update_of_ne (by decide : aW ≠ aB), Function.update_self]
  · show X4 aB = restB
    simp only [X4, Function.update_self]
  · show (Function.update (Function.update G4 EvC.rSa (Glyph.bit (EvC.sumBit a b c))) EvC.rKa
      (Glyph.bit (EvC.carryBit a b c))) EvC.rSa = Glyph.bit (EvC.sumBit a b c)
    rw [Function.update_of_ne (by decide : EvC.rSa ≠ EvC.rKa), Function.update_self]
  · show (Function.update (Function.update G4 EvC.rSa (Glyph.bit (EvC.sumBit a b c))) EvC.rKa
      (Glyph.bit (EvC.carryBit a b c))) EvC.rKa = Glyph.bit (EvC.carryBit a b c)
    rw [Function.update_self]
  · intro j hjW hjB
    show X4 j = X j
    simp only [X4, X2, Function.update_of_ne hjB, Function.update_of_ne hjW]

/-- `EvC.stepA` with a bit on top of the window (`aW`) and the digit buffer exhausted (`iend`). -/
theorem stepA_bit_eos_loc (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (restW Bs : List Glyph) (a c : Bool)
    (hW : X aW = Glyph.bit a :: restW)
    (hB : X aB = Glyph.iend :: Shift.gmk aB :: Bs)
    (hc : g EvC.rKa = Glyph.bit c) :
    ∃ (s' : State) (n : ℕ), Work.Layout.Ev main EvC.stepA ⟨g, X⟩ s' n ∧ n ≤ 12 ∧
      s'.stk aW = restW ∧
      s'.stk aB = Glyph.iend :: Shift.gmk aB :: Bs ∧
      s'.reg EvC.rSa = Glyph.bit (EvC.sumBit a false c) ∧
      s'.reg EvC.rKa = Glyph.bit (EvC.carryBit a false c) ∧
      (∀ j : Stk, j ≠ aW → j ≠ aB → s'.stk j = X j) := by
  let G1 : Reg → Glyph := Function.update g EvC.rWa (Glyph.bit a)
  have e1 : Work.Layout.Ev main (.peek aW EvC.rWa) ⟨g, X⟩ ⟨G1, X⟩ 1 := by
    have h := Work.Layout.ev_peek' main aW EvC.rWa g X
    simp only [hW, List.headD_cons] at h
    simpa [G1] using h
  have ht1 : G1 EvC.rWa ≠ Shift.gmk aW := by
    have h : G1 EvC.rWa = Glyph.bit a := by simp [G1]
    rw [h]
    exact Shift.bit_ne_gmk aW a
  let X2 : Stk → List Glyph := Function.update X aW restW
  let G2 : Reg → Glyph := Function.update G1 EvC.rWa (Glyph.bit a)
  have e2 : Work.Layout.Ev main (.pop aW EvC.rWa) ⟨G1, X⟩ ⟨G2, X2⟩ 1 := by
    have h := Work.Layout.ev_pop' main aW EvC.rWa G1 X
    simp only [hW, List.headD_cons, List.tail_cons] at h
    simpa [G2, X2] using h
  have hX2B : X2 aB = Glyph.iend :: Shift.gmk aB :: Bs := by
    simp only [X2, Function.update_of_ne (by decide : aB ≠ aW)]
    exact hB
  let G3 : Reg → Glyph := Function.update G2 EvC.rHa Glyph.iend
  have e3 : Work.Layout.Ev main (.peek aB EvC.rHa) ⟨G2, X2⟩ ⟨G3, X2⟩ 1 := by
    have h := Work.Layout.ev_peek' main aB EvC.rHa G2 X2
    simp only [hX2B, List.headD_cons] at h
    simpa [G3] using h
  have ht2 : G3 EvC.rHa = Glyph.iend := by simp [G3]
  let G4 : Reg → Glyph := Function.update G3 EvC.rZa (Glyph.bit false)
  have e4 : Work.Layout.Ev main (Cmd.set EvC.rZa (Glyph.bit false)) ⟨G3, X2⟩ ⟨G4, X2⟩ 1 := by
    have h := Work.Layout.ev_set' main EvC.rZa (Glyph.bit false) G3 X2
    simpa [G4] using h
  have hG4w : G4 EvC.rWa = Glyph.bit a := by
    simp only [G4, G3, G2, Function.update_of_ne (by decide : EvC.rWa ≠ EvC.rZa),
      Function.update_of_ne (by decide : EvC.rWa ≠ EvC.rHa), Function.update_self]
  have hG4z : G4 EvC.rZa = Glyph.bit false := by simp only [G4, Function.update_self]
  have hG4k : G4 EvC.rKa = Glyph.bit c := by
    simp only [G4, G3, G2, G1, Function.update_of_ne (by decide : EvC.rKa ≠ EvC.rZa),
      Function.update_of_ne (by decide : EvC.rKa ≠ EvC.rHa),
      Function.update_of_ne (by decide : EvC.rKa ≠ EvC.rWa)]
    exact hc
  let s' : State := ((⟨G4, X2⟩ : State).updReg EvC.rSa (Glyph.bit (EvC.sumBit a false c))).updReg
    EvC.rKa (Glyph.bit (EvC.carryBit a false c))
  have e5 : Work.Layout.Ev main (EvC.stepAdd EvC.rWa EvC.rZa EvC.rKa EvC.rSa) ⟨G4, X2⟩ s' 5 :=
    ⟨5, EvC.stepAddEv main EvC.rWa EvC.rZa EvC.rKa EvC.rSa ⟨G4, X2⟩ a false c hG4w hG4z hG4k,
      le_rfl⟩
  have e6 : Work.Layout.Ev main
      (Work.Layout.seqs [Cmd.set EvC.rZa (Glyph.bit false),
        EvC.stepAdd EvC.rWa EvC.rZa EvC.rKa EvC.rSa])
      ⟨G3, X2⟩ s' 6 := Work.Layout.Ev.seq e4 e5
  have e7 : Work.Layout.Ev main
      (Cmd.ite EvC.rHa Glyph.iend
        (Work.Layout.seqs [Cmd.set EvC.rZa (Glyph.bit false),
          EvC.stepAdd EvC.rWa EvC.rZa EvC.rKa EvC.rSa])
        (Work.Layout.seqs [Cmd.pop aB EvC.rHa, EvC.stepAdd EvC.rWa EvC.rHa EvC.rKa EvC.rSa]))
      ⟨G3, X2⟩ s' 7 := Work.Layout.Ev.iteT ht2 e6
  have e8 : Work.Layout.Ev main
      (Work.Layout.seqs [Cmd.pop aW EvC.rWa, Cmd.peek aB EvC.rHa,
        Cmd.ite EvC.rHa Glyph.iend
          (Work.Layout.seqs [Cmd.set EvC.rZa (Glyph.bit false),
            EvC.stepAdd EvC.rWa EvC.rZa EvC.rKa EvC.rSa])
          (Work.Layout.seqs [Cmd.pop aB EvC.rHa,
            EvC.stepAdd EvC.rWa EvC.rHa EvC.rKa EvC.rSa])])
      ⟨G1, X⟩ s' 9 := Work.Layout.Ev.seq e2 (Work.Layout.Ev.seq e3 e7)
  have e9 : Work.Layout.Ev main EvC.stepA ⟨g, X⟩ s' 11 :=
    Work.Layout.Ev.seq e1 (Work.Layout.Ev.iteF ht1 e8)
  refine ⟨s', 11, e9, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · show X2 aW = restW
    simp only [X2, Function.update_self]
  · show X2 aB = Glyph.iend :: Shift.gmk aB :: Bs
    exact hX2B
  · show (Function.update (Function.update G4 EvC.rSa (Glyph.bit (EvC.sumBit a false c))) EvC.rKa
      (Glyph.bit (EvC.carryBit a false c))) EvC.rSa = Glyph.bit (EvC.sumBit a false c)
    rw [Function.update_of_ne (by decide : EvC.rSa ≠ EvC.rKa), Function.update_self]
  · show (Function.update (Function.update G4 EvC.rSa (Glyph.bit (EvC.sumBit a false c))) EvC.rKa
      (Glyph.bit (EvC.carryBit a false c))) EvC.rKa = Glyph.bit (EvC.carryBit a false c)
    rw [Function.update_self]
  · intro j hjW hjB
    show X2 j = X j
    simp only [X2, Function.update_of_ne hjW]

/-- `EvC.stepA` with the window (`aW`) exhausted (its marker on top) and a bit on `aB`. -/
theorem stepA_eos_bit_loc (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (restB Ws : List Glyph) (b c : Bool)
    (hW : X aW = Shift.gmk aW :: Ws)
    (hB : X aB = Glyph.bit b :: restB)
    (hc : g EvC.rKa = Glyph.bit c) :
    ∃ (s' : State) (n : ℕ), Work.Layout.Ev main EvC.stepA ⟨g, X⟩ s' n ∧ n ≤ 12 ∧
      s'.stk aW = Shift.gmk aW :: Ws ∧ s'.stk aB = restB ∧
      s'.reg EvC.rSa = Glyph.bit (EvC.sumBit false b c) ∧
      s'.reg EvC.rKa = Glyph.bit (EvC.carryBit false b c) ∧
      (∀ j : Stk, j ≠ aW → j ≠ aB → s'.stk j = X j) := by
  let G1 : Reg → Glyph := Function.update g EvC.rWa (Shift.gmk aW)
  have e1 : Work.Layout.Ev main (.peek aW EvC.rWa) ⟨g, X⟩ ⟨G1, X⟩ 1 := by
    have h := Work.Layout.ev_peek' main aW EvC.rWa g X
    simp only [hW, List.headD_cons] at h
    simpa [G1] using h
  have ht1 : G1 EvC.rWa = Shift.gmk aW := by simp [G1]
  let X2 : Stk → List Glyph := Function.update X aB restB
  let G2 : Reg → Glyph := Function.update G1 EvC.rHa (Glyph.bit b)
  have e2 : Work.Layout.Ev main (.pop aB EvC.rHa) ⟨G1, X⟩ ⟨G2, X2⟩ 1 := by
    have h := Work.Layout.ev_pop' main aB EvC.rHa G1 X
    simp only [hB, List.headD_cons, List.tail_cons] at h
    simpa [G2, X2] using h
  let G3 : Reg → Glyph := Function.update G2 EvC.rZa (Glyph.bit false)
  have e3 : Work.Layout.Ev main (Cmd.set EvC.rZa (Glyph.bit false)) ⟨G2, X2⟩ ⟨G3, X2⟩ 1 := by
    have h := Work.Layout.ev_set' main EvC.rZa (Glyph.bit false) G2 X2
    simpa [G3] using h
  have hG3h : G3 EvC.rHa = Glyph.bit b := by
    simp only [G3, G2, Function.update_of_ne (by decide : EvC.rHa ≠ EvC.rZa),
      Function.update_self]
  have hG3z : G3 EvC.rZa = Glyph.bit false := by simp only [G3, Function.update_self]
  have hG3k : G3 EvC.rKa = Glyph.bit c := by
    simp only [G3, G2, G1, Function.update_of_ne (by decide : EvC.rKa ≠ EvC.rZa),
      Function.update_of_ne (by decide : EvC.rKa ≠ EvC.rHa),
      Function.update_of_ne (by decide : EvC.rKa ≠ EvC.rWa)]
    exact hc
  let s' : State := ((⟨G3, X2⟩ : State).updReg EvC.rSa (Glyph.bit (EvC.sumBit b false c))).updReg
    EvC.rKa (Glyph.bit (EvC.carryBit b false c))
  have e4 : Work.Layout.Ev main (EvC.stepAdd EvC.rHa EvC.rZa EvC.rKa EvC.rSa) ⟨G3, X2⟩ s' 5 :=
    ⟨5, EvC.stepAddEv main EvC.rHa EvC.rZa EvC.rKa EvC.rSa ⟨G3, X2⟩ b false c hG3h hG3z hG3k,
      le_rfl⟩
  have e5 : Work.Layout.Ev main
      (Work.Layout.seqs [Cmd.pop aB EvC.rHa, Cmd.set EvC.rZa (Glyph.bit false),
        EvC.stepAdd EvC.rHa EvC.rZa EvC.rKa EvC.rSa])
      ⟨G1, X⟩ s' 7 := Work.Layout.Ev.seq e2 (Work.Layout.Ev.seq e3 e4)
  have e6 : Work.Layout.Ev main
      (Cmd.ite EvC.rWa (Shift.gmk aW)
        (Work.Layout.seqs [Cmd.pop aB EvC.rHa, Cmd.set EvC.rZa (Glyph.bit false),
          EvC.stepAdd EvC.rHa EvC.rZa EvC.rKa EvC.rSa])
        (Work.Layout.seqs [Cmd.pop aW EvC.rWa, Cmd.peek aB EvC.rHa,
          Cmd.ite EvC.rHa Glyph.iend
            (Work.Layout.seqs [Cmd.set EvC.rZa (Glyph.bit false),
              EvC.stepAdd EvC.rWa EvC.rZa EvC.rKa EvC.rSa])
            (Work.Layout.seqs [Cmd.pop aB EvC.rHa,
              EvC.stepAdd EvC.rWa EvC.rHa EvC.rKa EvC.rSa])]))
      ⟨G1, X⟩ s' 8 := Work.Layout.Ev.iteT ht1 e5
  have e7 : Work.Layout.Ev main EvC.stepA ⟨g, X⟩ s' 9 :=
    Work.Layout.Ev.seq e1 e6
  refine ⟨s', 9, e7, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · show X2 aW = Shift.gmk aW :: Ws
    simp only [X2, Function.update_of_ne (by decide : aW ≠ aB)]
    exact hW
  · show X2 aB = restB
    simp only [X2, Function.update_self]
  · show (Function.update (Function.update G3 EvC.rSa (Glyph.bit (EvC.sumBit b false c))) EvC.rKa
      (Glyph.bit (EvC.carryBit b false c))) EvC.rSa = Glyph.bit (EvC.sumBit false b c)
    rw [Function.update_of_ne (by decide : EvC.rSa ≠ EvC.rKa), Function.update_self]
    exact congrArg Glyph.bit (stepAEv_sumBit_swap b false c)
  · show (Function.update (Function.update G3 EvC.rSa (Glyph.bit (EvC.sumBit b false c))) EvC.rKa
      (Glyph.bit (EvC.carryBit b false c))) EvC.rKa = Glyph.bit (EvC.carryBit false b c)
    rw [Function.update_self]
    exact congrArg Glyph.bit (stepAEv_carryBit_swap b false c)
  · intro j hjW hjB
    show X2 j = X j
    simp only [X2, Function.update_of_ne hjB]

/-! ## The loop-step lemma -/

theorem stepAEv (main : HvdH.Cmd) (W hbits : List Bool) (Ws Bs : List HvdH.Glyph) (k : ℕ)
    (s : HvdH.State) (hstr : Work.IntLib.EvC.strP W hbits Ws Bs k s)
    (hk : k < Work.IntLib.EvC.addN W hbits)
    (hc : s.reg Work.IntLib.EvC.rKa = HvdH.Glyph.bit (Work.IntLib.EvC.carryC W hbits false k)) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main Work.IntLib.EvC.stepA s s' n ∧ n ≤ 12 ∧
      Work.IntLib.EvC.strP W hbits Ws Bs (k + 1) s' ∧
      s'.reg Work.IntLib.EvC.rSa = HvdH.Glyph.bit
        (Work.IntLib.EvC.sumBit (W.getD k false) (hbits.getD k false) (Work.IntLib.EvC.carryC W hbits false k)) ∧
      s'.reg Work.IntLib.EvC.rKa = HvdH.Glyph.bit
        (Work.IntLib.EvC.carryBit (W.getD k false) (hbits.getD k false) (Work.IntLib.EvC.carryC W hbits false k)) ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.aW → j ≠ Work.IntLib.aB → s'.stk j = s.stk j) := by
  obtain ⟨g, X⟩ := s
  obtain ⟨hXW, hXB⟩ := hstr
  simp only [Work.Layout.stk_mk, Work.Layout.reg_mk] at hXW hXB hc
  by_cases hWnil : W.drop k = []
  · -- the window is exhausted: `aB` still has a bit
    have hlenW : W.length ≤ k := by
      have h := congrArg List.length hWnil
      rw [List.length_drop, List.length_nil] at h
      omega
    have hltB : k < hbits.length := by
      by_contra hle
      have h3 : max W.length hbits.length ≤ k := max_le hlenW (not_lt.mp hle)
      have h := hk
      rw [EvC.addN] at h
      omega
    have hA : X aW = Shift.gmk aW :: Ws := by
      have h := hXW
      rw [hWnil] at h
      simpa using h
    have hB : X aB = Glyph.bit (hbits.getD k false) ::
        ((hbits.drop (k + 1)).map Glyph.bit ++ Glyph.iend :: Shift.gmk aB :: Bs) := by
      rw [hXB, EvC.drop_map_cons hbits hltB]
      rfl
    obtain ⟨s', n, he, hn, hsW, hsB, hsS, hsK, hfr⟩ :=
      stepA_eos_bit_loc main g X _ _ (hbits.getD k false) (EvC.carryC W hbits false k) hA hB hc
    refine ⟨s', n, he, hn, ⟨?_, hsB⟩, ?_, ?_, ?_⟩
    · rw [hsW, List.drop_eq_nil_of_le (by omega : W.length ≤ k + 1)]
      rfl
    · rw [hsS, EvC.getD_eq_false_of_le hlenW]
    · rw [hsK, EvC.getD_eq_false_of_le hlenW]
    · intro j hjW hjB
      simpa using hfr j hjW hjB
  · -- the window still has a bit
    have hltW : k < W.length := (stepAEv_drop_ne_nil_iff W k).mp hWnil
    have hA : X aW = Glyph.bit (W.getD k false) ::
        ((W.drop (k + 1)).map Glyph.bit ++ Shift.gmk aW :: Ws) := by
      rw [hXW, EvC.drop_map_cons W hltW]
      rfl
    by_cases hBnil : hbits.drop k = []
    · -- the digit buffer is exhausted
      have hlenB : hbits.length ≤ k := by
        have h := congrArg List.length hBnil
        rw [List.length_drop, List.length_nil] at h
        omega
      have hB : X aB = Glyph.iend :: Shift.gmk aB :: Bs := by
        have h := hXB
        rw [hBnil] at h
        simpa using h
      obtain ⟨s', n, he, hn, hsW, hsB, hsS, hsK, hfr⟩ :=
        stepA_bit_eos_loc main g X _ _ (W.getD k false) (EvC.carryC W hbits false k) hA hB hc
      refine ⟨s', n, he, hn, ⟨hsW, ?_⟩, ?_, ?_, ?_⟩
      · rw [hsB, List.drop_eq_nil_of_le (by omega : hbits.length ≤ k + 1)]
        rfl
      · rw [hsS, EvC.getD_eq_false_of_le hlenB]
      · rw [hsK, EvC.getD_eq_false_of_le hlenB]
      · intro j hjW hjB
        simpa using hfr j hjW hjB
    · -- both streams still have a bit
      have hltB : k < hbits.length := (stepAEv_drop_ne_nil_iff hbits k).mp hBnil
      have hB : X aB = Glyph.bit (hbits.getD k false) ::
          ((hbits.drop (k + 1)).map Glyph.bit ++ Glyph.iend :: Shift.gmk aB :: Bs) := by
        rw [hXB, EvC.drop_map_cons hbits hltB]
        rfl
      obtain ⟨s', n, he, hn, hsW, hsB, hsS, hsK, hfr⟩ :=
        stepA_bit_bit_loc main g X _ _ (W.getD k false) (hbits.getD k false)
          (EvC.carryC W hbits false k) hA hB hc
      refine ⟨s', n, he, hn, ⟨hsW, hsB⟩, hsS, hsK, ?_⟩
      · intro j hjW hjB
        simpa using hfr j hjW hjB

end Work.IntLib.evCA
