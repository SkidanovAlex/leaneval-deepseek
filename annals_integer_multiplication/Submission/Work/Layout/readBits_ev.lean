import Mathlib
import Submission.Work.Layout.chunksOfDefs
import Submission.Work.Layout.chunksProof

/-!
# `LayoutLib.chunksOf`: reading the bits of the integer on top of stack 0

Raw `Ev` proof for the first phase of `Work.Layout.mainProg` (see `chunksOfDefs.lean`):
`readBitsProg` pops the sign and then the bits of the integer on top of stack 0, pushing the bits
(most significant first) onto stack `sBits`, above the `gMark` sentinel it pushes first; the `iend`
is dropped as well.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-- The size of an integer value, in terms of the bit list of its absolute value. -/
theorem isz_eq_bits_length (m : ℕ) : isz (m : ℤ) = m.bits.length + 2 := by
  have h1 := enc_int_nat_length m
  rw [enc_int_nat m] at h1
  simp [bitsG_length] at h1
  omega

/-- `(bitsG (P ++ [b])).reverse` prepends the glyph of `b` to `(bitsG P).reverse`: reading the
bits least significant first accumulates them reversed. -/
theorem bitsG_append_singleton_reverse (P : List Bool) (b : Bool) :
    (bitsG (P ++ [b])).reverse = Glyph.bit b :: (bitsG P).reverse := by
  simp [bitsG, List.reverse_append]

/-! ## The two branch bodies of `readBitBody` -/

/-- `readBitBody` on the `iend`: it pops the `iend`, drops it and stops the loop (`rLoopG = eos`);
`sBits` and every other stack are untouched.  Cost 4. -/
theorem rbBodyStop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {L : List Glyph}
    (hh : X 0 = Glyph.iend :: L) :
    ∃ s', Ev main readBitBody ⟨g, X⟩ s' 4 ∧ s'.stk 0 = L ∧ s'.stk sBits = X sBits ∧
      s'.reg rLoopG = Glyph.eos ∧ (∀ j : Stk, j ≠ 0 → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁0, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := 0) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂0, -, hs₂f, -⟩ :=
    step_pop (main := main) (k := 0) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁0
  obtain ⟨s₃, hev₃, hs₃r, -, hs₃f⟩ :=
    step_set (main := main) (r := rLoopG) (c := Glyph.eos) (g := s₂.reg) (X := s₂.stk)
  have h2 : Ev main (seqs [.pop 0 rE, .set rLoopG Glyph.eos]) s₁ s₃ 2 :=
    Ev.seq' hev₂ hev₃ (by omega)
  have hit : Ev main (.ite rE Glyph.iend (seqs [.pop 0 rE, .set rLoopG Glyph.eos])
      (seqs [.pop 0 rE, .push sBits rE, .set rLoopG gCont])) s₁ s₃ 3 := Ev.iteT hs₁r h2
  have hbody : Ev main readBitBody ⟨g, X⟩ s₃ 4 := by
    unfold readBitBody
    exact Ev.seq' hev₁ hit (by omega)
  refine ⟨s₃, hbody, ?_, ?_, hs₃r, ?_⟩
  · rw [hs₃f 0, hs₂0]
  · rw [hs₃f sBits, hs₂f sBits (by decide : sBits ≠ (0 : Stk)),
      hs₁f sBits (by decide : sBits ≠ (0 : Stk))]
  · intro j hj
    rw [hs₃f j, hs₂f j hj, hs₁f j hj]

/-- `readBitBody` on a glyph `c ≠ iend`: it pops `c`, pushes it on `sBits` and sets `rLoopG = gCont`
so that the loop continues.  Cost 5. -/
theorem rbBodyPush {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {c : Glyph}
    {L : List Glyph} (hc : c ≠ Glyph.iend) (hh : X 0 = c :: L) :
    ∃ s', Ev main readBitBody ⟨g, X⟩ s' 5 ∧ s'.stk 0 = L ∧ s'.stk sBits = c :: X sBits ∧
      s'.reg rLoopG = gCont ∧ (∀ j : Stk, j ≠ 0 → j ≠ sBits → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁0, hs₁r, hs₁f, -⟩ := step_peek (main := main) (k := 0) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂0, hs₂r, hs₂f, -⟩ :=
    step_pop (main := main) (k := 0) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁0
  obtain ⟨s₃, hev₃, hs₃B, hs₃f, -⟩ :=
    step_push (main := main) (k := sBits) (r := rE) (g := s₂.reg) (X := s₂.stk) (v := c) hs₂r
  obtain ⟨s₄, hev₄, hs₄r, -, hs₄f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₃.reg) (X := s₃.stk)
  have h3 : Ev main (seqs [.push sBits rE, .set rLoopG gCont]) s₂ s₄ 2 :=
    Ev.seq' hev₃ hev₄ (by omega)
  have h2 : Ev main (seqs [.pop 0 rE, .push sBits rE, .set rLoopG gCont]) s₁ s₄ 3 :=
    Ev.seq' hev₂ h3 (by omega)
  have hcond : ¬ (s₁.reg rE = Glyph.iend) := by rw [hs₁r]; exact hc
  have hit : Ev main (.ite rE Glyph.iend (seqs [.pop 0 rE, .set rLoopG Glyph.eos])
      (seqs [.pop 0 rE, .push sBits rE, .set rLoopG gCont])) s₁ s₄ 4 := Ev.iteF hcond h2
  have hbody : Ev main readBitBody ⟨g, X⟩ s₄ 5 := by
    unfold readBitBody
    exact Ev.seq' hev₁ hit (by omega)
  refine ⟨s₄, hbody, ?_, ?_, hs₄r, ?_⟩
  · rw [hs₄f 0, hs₃f 0 (by decide : (0 : Stk) ≠ sBits), hs₂0]
  · rw [hs₄f sBits, hs₃B, hs₂f sBits (by decide : sBits ≠ (0 : Stk)),
      hs₁f sBits (by decide : sBits ≠ (0 : Stk))]
  · intro j hj0 hjs
    rw [hs₄f j, hs₃f j hjs, hs₂f j hj0, hs₁f j hj0]

/-! ## The bit-reading loop -/

/-- The bit-reading loop of `readBitsProg`.  `P` collects the bits already read, so that `sBits`
holds `(bitsG P).reverse` above its `gMark` sentinel, and `rest` is still on stack 0 (least
significant bit first) followed by the `iend`.  Every iteration costs at most 6 (the test plus
`readBitBody`), including the last one, which pops the `iend`. -/
theorem readBitsLoop {main : Cmd} :
    ∀ (rest P : List Bool) (g : Reg → Glyph) (X : Stk → List Glyph) (A B : List Glyph),
      g rLoopG = gCont → X 0 = bitsG rest ++ Glyph.iend :: A →
      X sBits = (bitsG P).reverse ++ gMark :: B →
      ∃ s', loopRuns main rLoopG gCont readBitBody (rest.length + 1) ⟨g, X⟩ s'
          (6 * (rest.length + 1)) ∧
        s'.stk 0 = A ∧ s'.stk sBits = (bitsG (P ++ rest)).reverse ++ gMark :: B ∧
        s'.reg rLoopG = Glyph.eos ∧
        (∀ j : Stk, j ≠ 0 → j ≠ sBits → s'.stk j = X j) := by
  intro rest
  induction rest with
  | nil =>
      intro P g X A B hreg h0 hB
      simp only [List.length_nil]
      obtain ⟨s', hev, hs0, hsB, hsreg, hfr⟩ :=
        rbBodyStop (main := main) (g := g) (X := X) (L := A) (by simpa using h0)
      refine ⟨s', ?_, hs0, ?_, hsreg, ?_⟩
      · exact loopRuns.mono (by decide)
          (loopRuns.one (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev) (by decide)
      · rw [hsB, hB, List.append_nil]
      · intro j hj1 _
        exact hfr j hj1
  | cons b t ih =>
      intro P g X A B hreg h0 hB
      simp only [List.length_cons]
      have h0' : X 0 = Glyph.bit b :: (bitsG t ++ Glyph.iend :: A) := by
        simpa only [bitsG, List.map_cons, List.cons_append] using h0
      have hc : Glyph.bit b ≠ Glyph.iend := fun h => by cases h
      obtain ⟨s₁, hev₁, hs₁0, hs₁B, hs₁r, hfr₁⟩ :=
        rbBodyPush (main := main) (g := g) (X := X) (c := Glyph.bit b)
          (L := bitsG t ++ Glyph.iend :: A) hc h0'
      have hB₁ : s₁.stk sBits = (bitsG (P ++ [b])).reverse ++ gMark :: B := by
        rw [hs₁B, hB, bitsG_append_singleton_reverse]
        rfl
      obtain ⟨s₂, hrun₂, hs₂0, hs₂B, hs₂r, hfr₂⟩ :=
        ih (P ++ [b]) s₁.reg s₁.stk A B hs₁r hs₁0 hB₁
      refine ⟨s₂, ?_, hs₂0, ?_, hs₂r, ?_⟩
      · exact loopRuns.succ' (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev₁ hrun₂
          (by omega)
      · rw [hs₂B, List.append_assoc, List.singleton_append]
      · intro j hj1 hj2
        rw [hfr₂ j hj1 hj2, hfr₁ j hj1 hj2]

/-- Requires the import of `Submission.Work.Layout.chunksOfDefs`.

`readBitsProg` pops the sign and the bits of the integer value on top of stack 0, leaving the bits
in *reversed* order (most significant first) on `sBits`, above a `gMark` sentinel; the sign and the
`iend` are dropped.  Cost `O(isz m)`.

`Work.Layout.enc_int_nat` gives `(Val.int (m : ℤ)).enc = Glyph.pos :: (bitsG m.bits ++
[Glyph.iend])`, and `gMark ∉ bitsG l` is `Work.Layout.gMark_notMem_bitsG`. -/
theorem readBits_ev {main : HvdH.Cmd} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {m : ℕ} {A B : List HvdH.Glyph}
    (h0 : X 0 = (HvdH.Val.int (m : ℤ)).enc ++ A) (hB : X Work.Layout.sBits = B) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.readBitsProg ⟨g, X⟩ s' n ∧
      n ≤ 8 * HvdH.isz (m : ℤ) + 10 ∧
      s'.stk 0 = A ∧
      s'.stk Work.Layout.sBits = (Work.Layout.bitsG m.bits).reverse ++ Work.Layout.gMark :: B ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.Layout.sBits → s'.stk j = X j) := by
  have h0a : X 0 = Glyph.pos :: ((bitsG m.bits ++ [Glyph.iend]) ++ A) := by
    rw [h0, enc_int_nat]
    rfl
  obtain ⟨s₁, hev₁, hs₁0, -, hs₁f, -⟩ := step_pop (main := main) (k := 0) (r := rE) h0a
  have hs₁B : s₁.stk sBits = B := by rw [hs₁f sBits (by decide : sBits ≠ (0 : Stk)), hB]
  obtain ⟨s₂, hev₂, hs₂B, hs₂f, -, -⟩ :=
    step_pushK (main := main) (k := sBits) (c := gMark) (g := s₁.reg) (X := s₁.stk)
  obtain ⟨s₃, hev₃, hs₃r, -, hs₃f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₂.reg) (X := s₂.stk)
  have hs₃0 : s₃.stk 0 = bitsG m.bits ++ Glyph.iend :: A := by
    rw [hs₃f 0, hs₂f 0 (by decide : (0 : Stk) ≠ sBits), hs₁0, List.append_assoc,
      List.singleton_append]
  have hs₃B : s₃.stk sBits = (bitsG ([] : List Bool)).reverse ++ gMark :: B := by
    rw [hs₃f sBits, hs₂B, hs₁B]
    rfl
  obtain ⟨s₄, hrun, hs₄0, hs₄B, hs₄r, hfr₄⟩ :=
    readBitsLoop (main := main) (rest := m.bits) (P := []) (g := s₃.reg) (X := s₃.stk)
      (A := A) (B := B) hs₃r hs₃0 hs₃B
  have hloop : Ev main (.loop rLoopG gCont readBitBody) ⟨s₃.reg, s₃.stk⟩ s₄
      (6 * (m.bits.length + 1) + 1) := loopRuns.eval hrun (by rw [hs₄r]; decide)
  have h34 : Ev main (seqs [.set rLoopG gCont, .loop rLoopG gCont readBitBody]) s₂ s₄
      (1 + (6 * (m.bits.length + 1) + 1)) := Ev.seq' hev₃ hloop (by omega)
  have h234 : Ev main (seqs [pushK sBits gMark, .set rLoopG gCont,
      .loop rLoopG gCont readBitBody]) s₁ s₄ (2 + (1 + (6 * (m.bits.length + 1) + 1))) :=
    Ev.seq' hev₂ h34 (by omega)
  have hmain : Ev main readBitsProg ⟨g, X⟩ s₄
      (1 + (2 + (1 + (6 * (m.bits.length + 1) + 1)))) := by
    unfold readBitsProg
    exact Ev.seq' hev₁ h234 (by omega)
  have hbnd : 1 + (2 + (1 + (6 * (m.bits.length + 1) + 1))) ≤ 8 * isz (m : ℤ) + 10 := by
    rw [isz_eq_bits_length]
    omega
  refine ⟨s₄, 8 * isz (m : ℤ) + 10, Ev.mono hmain hbnd, le_rfl, hs₄0, ?_, ?_⟩
  · rw [hs₄B, List.nil_append]
  · intro j hj1 hj2
    rw [hfr₄ j hj1 hj2, hs₃f j, hs₂f j hj2, hs₁f j hj1]

end Work.Layout
