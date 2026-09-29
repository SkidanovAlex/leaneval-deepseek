import Mathlib
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.Basic
import Submission.Work.IntLib.AddSub.EvKit
import Submission.Work.IntLib.AddSub.asw_addTree_ev
import Submission.Work.IntLib.AddSub.asw_subLoop_spec

/-!
# `IntLib` / add–sub: specification of the magnitude adder `asw_addLoop`

`asw_addLoop a b out` ripples through the two marked bit lists on `a` and `b` (least
significant digit first) and pushes the digits of `|a| + |b|` (plus the incoming carry) on
`out`.  The emitted list `em'` satisfies
`ofBits em' = ofBits em + 2 ^ em.length * (ofBits ra + ofBits rb + c.toNat)`,
i.e. the low digits of the sum, at cost `≤ 31 * (ra.length + rb.length + 2)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Work.IntLib
namespace AddSub

open HvdH

/-! ## Arithmetic of one adder digit -/

/-- One digit of the addition `x + y + c`: the output bit and the outgoing carry satisfy
`out + 2 * carry = x + y + c`. -/
theorem asw_add_digit_key (x y c : Bool) :
    (asw_addOutBit x y c).toNat + 2 * (asw_addCarry x y c).toNat = x.toNat + y.toNat + c.toNat := by
  cases x <;> cases y <;> cases c <;> decide

/-- The natural-number form of `ofBits_head`. -/
theorem ofBits_headNat (xs : List Bool) :
    ofBits xs = (xs.headD false).toNat + 2 * ofBits xs.tail := by
  cases xs with
  | nil => simp [ofBits]
  | cons b t => simp [ofBits_cons]

@[simp] theorem ofBits_nil' : ofBits ([] : List Bool) = 0 := rfl

@[simp] theorem ofBits_singleton (b : Bool) : ofBits [b] = b.toNat := by
  simp [ofBits_cons, ofBits_nil']

/-- The invariant step of the adder for one consumed digit. -/
theorem tail_length_le {α : Type} (l : List α) : l.tail.length ≤ l.length := by
  cases l <;> simp

theorem tail_length_lt {α : Type} (l : List α) (h : l ≠ []) : l.tail.length < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp

@[simp] theorem asw_addOutBit_nilD (c : Bool) :
    asw_addOutBit (([] : List Bool).headD false) (([] : List Bool).headD false) c = c := by
  cases c <;> rfl

@[simp] theorem asw_addCarry_nilD (c : Bool) :
    asw_addCarry (([] : List Bool).headD false) (([] : List Bool).headD false) c = false := by
  cases c <;> rfl

@[simp] theorem asw_addOutBit_ff (c : Bool) : asw_addOutBit false false c = c := by
  cases c <;> rfl

@[simp] theorem asw_addCarry_ff (c : Bool) : asw_addCarry false false c = false := by
  cases c <;> rfl

theorem asw_add_cons_step (ra rb e : List Bool) (c : Bool) :
    ofBits (e ++ [asw_addOutBit (ra.headD false) (rb.headD false) c])
      + 2 ^ (e ++ [asw_addOutBit (ra.headD false) (rb.headD false) c]).length
          * (ofBits ra.tail + ofBits rb.tail
              + (asw_addCarry (ra.headD false) (rb.headD false) c).toNat)
      = ofBits e + 2 ^ e.length * (ofBits ra + ofBits rb + c.toNat) := by
  have hk := asw_add_digit_key (ra.headD false) (rb.headD false) c
  have hA := ofBits_headNat ra
  have hB := ofBits_headNat rb
  rw [ofBits_append, ofBits_singleton, List.length_append, List.length_singleton, pow_succ, hA, hB]
  have hkey : (ra.headD false).toNat + 2 * ofBits ra.tail
        + ((rb.headD false).toNat + 2 * ofBits rb.tail) + c.toNat
      = ((asw_addOutBit (ra.headD false) (rb.headD false) c).toNat
          + 2 * (asw_addCarry (ra.headD false) (rb.headD false) c).toNat)
        + 2 * (ofBits ra.tail + ofBits rb.tail) := by
    rw [show (ra.headD false).toNat + 2 * ofBits ra.tail
            + ((rb.headD false).toNat + 2 * ofBits rb.tail) + c.toNat
          = ((ra.headD false).toNat + (rb.headD false).toNat + c.toNat)
            + 2 * (ofBits ra.tail + ofBits rb.tail) from by ring, hk.symm]
  rw [hkey]
  ring

/-- The concrete step when both regions are empty: the emitted digit is the carry itself. -/
theorem asw_add_cons_step_nil (em : List Bool) (c : Bool) :
    ofBits (em ++ [c]) = ofBits em + 2 ^ em.length * c.toNat := by
  rw [ofBits_append, ofBits_singleton]

/-! ## The final flag test -/

/-- The final flag test of the adder: after `set rF gGo`, if both marked regions are exhausted
*and* the carry is `false`, the flag becomes `gStop`; otherwise it stays `gGo`.  Cost `≤ 5`;
no stack is touched. -/
theorem asw_addStop_test {main : Cmd} {a b : Stk} {ra rb : List Bool} {A B : List Glyph}
    {g : Reg → Glyph} {X : Stk → List Glyph} {cc : Bool}
    (hu : g rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos)
    (hv : g rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos)
    (hc : g rC = Glyph.bit cc) (hF : g rF = gGo) :
    ∃ s' n, Ev main (seqs [.set rF gGo, .ite rC (.bit false)
        (.ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip]) ⟨g, X⟩ s' n ∧
      n ≤ 5 ∧ s'.stk = X ∧ s'.reg rC = g rC ∧
      s'.reg rF = (if ra = [] ∧ rb = [] ∧ cc = false then gStop else gGo) := by
  let g5 : Reg → Glyph := Function.update g rF gGo
  have hset : Ev main (.set rF gGo) ⟨g, X⟩ ⟨g5, X⟩ 1 := ev_set' main rF gGo g X
  have hu5 : g5 rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos := by
    simp only [g5, upReg_ne (show rU ≠ rF by decide)]; exact hu
  have hv5 : g5 rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos := by
    simp only [g5, upReg_ne (show rV ≠ rF by decide)]; exact hv
  have hc5 : g5 rC = Glyph.bit cc := by
    simp only [g5, upReg_ne (show rC ≠ rF by decide)]; exact hc
  cases cc with
  | false =>
      have hcf : g5 rC = Glyph.bit false := by simpa using hc5
      rcases ra with _ | ⟨hx, ra'⟩
      · rcases rb with _ | ⟨hy, rb'⟩
        · have hT1 : g5 rU = gmk a := by simpa using hu5
          have hT2 : g5 rV = gmk b := by simpa using hv5
          have h2 : Ev main (.ite rV (gmk b) (.set rF gStop) .skip) ⟨g5, X⟩
              ⟨Function.update g5 rF gStop, X⟩ 2 := Ev.iteT hT2 (ev_set' main rF gStop g5 X)
          have h3 : Ev main (.ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip)
              ⟨g5, X⟩ ⟨Function.update g5 rF gStop, X⟩ 3 := Ev.iteT hT1 h2
          have h4 : Ev main (.ite rC (.bit false) (.ite rU (gmk a)
              (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip) ⟨g5, X⟩
              ⟨Function.update g5 rF gStop, X⟩ 4 := Ev.iteT hcf h3
          have hmain : Ev main (seqs [.set rF gGo, .ite rC (.bit false) (.ite rU (gmk a)
              (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip]) ⟨g, X⟩
              ⟨Function.update g5 rF gStop, X⟩ 5 := by
            simp only [seqs]; exact Ev.seq hset h4
          refine ⟨⟨Function.update g5 rF gStop, X⟩, 5, hmain, le_rfl, rfl, ?_, ?_⟩
          · simp only [upReg_ne (show rC ≠ rF by decide), g5, upReg_ne (show rC ≠ rF by decide)]
          · simp [g5, upReg_same]
        · have hT1 : g5 rU = gmk a := by simpa using hu5
          have hT2 : g5 rV ≠ gmk b := by
            rw [hv5]; simp only [List.map_cons, List.headD_cons]; exact fun h => by cases h
          have h2 : Ev main (.ite rV (gmk b) (.set rF gStop) .skip) ⟨g5, X⟩ ⟨g5, X⟩ 2 :=
            Ev.iteF hT2 (ev_skip main ⟨g5, X⟩)
          have h3 : Ev main (.ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip)
              ⟨g5, X⟩ ⟨g5, X⟩ 3 := Ev.iteT hT1 h2
          have h4 : Ev main (.ite rC (.bit false) (.ite rU (gmk a)
              (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip) ⟨g5, X⟩ ⟨g5, X⟩ 4 :=
            Ev.iteT hcf h3
          have hmain : Ev main (seqs [.set rF gGo, .ite rC (.bit false) (.ite rU (gmk a)
              (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip]) ⟨g, X⟩ ⟨g5, X⟩ 5 := by
            simp only [seqs]; exact Ev.seq hset h4
          refine ⟨⟨g5, X⟩, 5, hmain, le_rfl, rfl, ?_, ?_⟩
          · simp only [g5, upReg_ne (show rC ≠ rF by decide)]
          · simp [g5, upReg_same]
      · have hT1 : g5 rU ≠ gmk a := by
          rw [hu5]; simp only [List.map_cons, List.headD_cons]; exact fun h => by cases h
        have h2 : Ev main (.ite rU (gmk a) (.ite rV (gmk b) (.set rF gStop) .skip) .skip)
            ⟨g5, X⟩ ⟨g5, X⟩ 2 := Ev.iteF hT1 (ev_skip main ⟨g5, X⟩)
        have h4 : Ev main (.ite rC (.bit false) (.ite rU (gmk a)
            (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip) ⟨g5, X⟩ ⟨g5, X⟩ 3 :=
          Ev.iteT hcf h2
        have hmain : Ev main (seqs [.set rF gGo, .ite rC (.bit false) (.ite rU (gmk a)
            (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip]) ⟨g, X⟩ ⟨g5, X⟩ 4 := by
          simp only [seqs]; exact Ev.seq hset h4
        refine ⟨⟨g5, X⟩, 4, hmain, by omega, rfl, ?_, ?_⟩
        · simp only [g5, upReg_ne (show rC ≠ rF by decide)]
        · simp [g5, upReg_same]
  | true =>
      have hcf : g5 rC ≠ Glyph.bit false := by rw [hc5]; decide
      have h2 : Ev main (.ite rC (.bit false) (.ite rU (gmk a)
          (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip) ⟨g5, X⟩ ⟨g5, X⟩ 2 :=
        Ev.iteF hcf (ev_skip main ⟨g5, X⟩)
      have hmain : Ev main (seqs [.set rF gGo, .ite rC (.bit false) (.ite rU (gmk a)
          (.ite rV (gmk b) (.set rF gStop) .skip) .skip) .skip]) ⟨g, X⟩ ⟨g5, X⟩ 3 := by
        simp only [seqs]; exact Ev.seq hset h2
      refine ⟨⟨g5, X⟩, 3, hmain, by omega, rfl, ?_, ?_⟩
      · simp only [g5, upReg_ne (show rC ≠ rF by decide)]
      · simp [g5, upReg_same]

/-! ## One iteration -/

/-- One iteration of the adder: read one digit of each operand (a `false` digit when the region
is exhausted), emit the sum digit on `out` and update the carry; the flag is set to `gStop`
exactly when both regions are exhausted and the carry is `false`.  Cost `≤ 20`. -/
theorem asw_addBody_ev {main : Cmd} {a b out : Stk} (hab : a ≠ b) (hao : a ≠ out) (hbo : b ≠ out)
    {ra rb em : List Bool} {A B C : List Glyph} {c : Bool}
    {g : Reg → Glyph} {X : Stk → List Glyph}
    (hF : g rF = gGo) (hC : g rC = Glyph.bit c)
    (ha : X a = ra.map Glyph.bit ++ gmk a :: A)
    (hb : X b = rb.map Glyph.bit ++ gmk b :: B)
    (ho : X out = (em.map Glyph.bit).reverse ++ gmk out :: C) :
    ∃ s' n, Ev main (asw_addBody a b out rC rT rX rY rU rV rF) ⟨g, X⟩ s' n ∧ n ≤ 20 ∧
      s'.stk a = ra.tail.map Glyph.bit ++ gmk a :: A ∧
      s'.stk b = rb.tail.map Glyph.bit ++ gmk b :: B ∧
      s'.stk out = ((em ++ [asw_addOutBit (ra.headD false) (rb.headD false) c]).map Glyph.bit).reverse
        ++ gmk out :: C ∧
      s'.reg rC = Glyph.bit (asw_addCarry (ra.headD false) (rb.headD false) c) ∧
      (s'.reg rF = gStop ↔ ra = [] ∧ rb = [] ∧ asw_addCarry (ra.headD false) (rb.headD false) c
        = false) ∧
      (s'.reg rF = gGo ∨ s'.reg rF = gStop) := by
  let g1 : Reg → Glyph := Function.update g rU ((X a).headD Glyph.eos)
  have hpeekA : Ev main (.peek a rU) ⟨g, X⟩ ⟨g1, X⟩ 1 := ev_peek' main a rU g X
  have hu1 : g1 rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos := by
    simp only [g1, upReg_same, ha]
  obtain ⟨s1, n1, hiteA, hn1, h1a, h1X, hf1, hs1⟩ :=
    asw_readStep_ev (main := main) (k := a) (rU := rU) (rX := rX) ha hu1
  have kbs1 : s1.stk b = rb.map Glyph.bit ++ gmk b :: B := by rw [hs1 b hab.symm]; exact hb
  let g3 : Reg → Glyph := Function.update s1.reg rV ((s1.stk b).headD Glyph.eos)
  have hpeekB : Ev main (.peek b rV) s1 ⟨g3, s1.stk⟩ 1 := ev_peek' main b rV s1.reg s1.stk
  have hu3 : g3 rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos := by
    simp only [g3, upReg_same, kbs1]
  obtain ⟨s2, n2, hiteB, hn2, h2b, h2Y, hf2, hs2⟩ :=
    asw_readStep_ev (main := main) (k := b) (rU := rV) (rX := rY) kbs1 hu3
  have kA2 : s2.stk a = ra.tail.map Glyph.bit ++ gmk a :: A := by rw [hs2 a hab]; exact h1a
  have kX2 : s2.reg rX = Glyph.bit (ra.headD false) := by rw [hf2 rX (by decide)]; exact h1X
  have kY2 : s2.reg rY = Glyph.bit (rb.headD false) := h2Y
  have kC2 : s2.reg rC = Glyph.bit c := by
    rw [hf2 rC (by decide)]
    simp only [g3, upReg_ne (show rC ≠ rV by decide)]
    rw [hf1 rC (by decide)]
    exact hC
  have kF2 : s2.reg rF = gGo := by
    rw [hf2 rF (by decide)]
    simp only [g3, upReg_ne (show rF ≠ rV by decide)]
    rw [hf1 rF (by decide)]
    exact hF
  have kU2 : s2.reg rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos := by
    rw [hf2 rU (by decide)]
    simp only [g3, upReg_ne (show rU ≠ rV by decide)]
    rw [hf1 rU (by decide)]
    exact hu1
  have kV2 : s2.reg rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos := by
    rw [hf2 rV (by decide)]; exact hu3
  have kO2 : s2.stk out = (em.map Glyph.bit).reverse ++ gmk out :: C := by
    rw [hs2 out hbo.symm, hs1 out hao.symm]; exact ho
  -- the tree
  let g4 : Reg → Glyph := Function.update (Function.update s2.reg rT
    (Glyph.bit (asw_addOutBit (ra.headD false) (rb.headD false) c))) rC
    (Glyph.bit (asw_addCarry (ra.headD false) (rb.headD false) c))
  let X4 : Stk → List Glyph := Function.update s2.stk out
    (Glyph.bit (asw_addOutBit (ra.headD false) (rb.headD false) c) :: s2.stk out)
  have htree : Ev main (asw_addTree rX rY rC rT out) s2 ⟨g4, X4⟩ 6 := by
    have h := asw_addTree_ev (main := main) rX rY rC rT out (ra.headD false) (rb.headD false) c
      s2 kX2 kY2 kC2
    simpa only [g4, X4] using h
  have kC3 : g4 rC = Glyph.bit (asw_addCarry (ra.headD false) (rb.headD false) c) := by
    simp only [g4, upReg_same]
  have kO3 : X4 out = ((em ++ [asw_addOutBit (ra.headD false) (rb.headD false) c]).map Glyph.bit).reverse
      ++ gmk out :: C := by
    simp only [X4, upStk_same, kO2, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.append_nil,
      List.singleton_append, List.append_assoc, List.cons_append]
  have kB3 : X4 b = rb.tail.map Glyph.bit ++ gmk b :: B := by
    simp only [X4, upStk_ne hbo]; exact h2b
  have kA3 : X4 a = ra.tail.map Glyph.bit ++ gmk a :: A := by
    simp only [X4, upStk_ne hao]; exact kA2
  have kU3 : g4 rU = (ra.map Glyph.bit ++ gmk a :: A).headD Glyph.eos := by
    simp only [g4, upReg_ne (show rU ≠ rC by decide), upReg_ne (show rU ≠ rT by decide)]
    exact kU2
  have kV3 : g4 rV = (rb.map Glyph.bit ++ gmk b :: B).headD Glyph.eos := by
    simp only [g4, upReg_ne (show rV ≠ rC by decide), upReg_ne (show rV ≠ rT by decide)]
    exact kV2
  have kF3 : g4 rF = gGo := by
    simp only [g4, upReg_ne (show rF ≠ rC by decide), upReg_ne (show rF ≠ rT by decide)]
    exact kF2
  obtain ⟨s4, n4, hstop, hn4, h4stk, h4C, h4F⟩ :=
    asw_addStop_test (main := main) (a := a) (b := b) (ra := ra) (rb := rb) (A := A) (B := B)
      (g := g4) (X := X4) (cc := asw_addCarry (ra.headD false) (rb.headD false) c)
      kU3 kV3 kC3 kF3
  have hbody : Ev main (asw_addBody a b out rC rT rX rY rU rV rF) ⟨g, X⟩ s4
      (1 + (n1 + (1 + (n2 + (6 + n4))))) := by
    simp only [asw_addBody, seqs]
    exact Ev.seq hpeekA (Ev.seq hiteA (Ev.seq hpeekB (Ev.seq hiteB (Ev.seq htree hstop))))
  refine ⟨s4, _, hbody, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4stk]; exact kA3
  · rw [h4stk]; exact kB3
  · rw [h4stk]; exact kO3
  · rw [h4C]; exact kC3
  · constructor
    · intro h
      by_cases hc : ra = [] ∧ rb = [] ∧ asw_addCarry (ra.headD false) (rb.headD false) c = false
      · exact hc
      · rw [h4F, if_neg hc] at h
        exact absurd h (by decide)
    · intro hc
      rw [h4F, if_pos hc]
  · by_cases hc : ra = [] ∧ rb = [] ∧ asw_addCarry (ra.headD false) (rb.headD false) c = false
    · right; rw [h4F, if_pos hc]
    · left; rw [h4F, if_neg hc]

/-! ## The loop -/

/-- The adder loop: consumes both marked regions and emits the digits of the sum (plus the
incoming carry) on `out`. -/
theorem asw_addLoop_loop_ev {main : Cmd} {a b out : Stk} (hab : a ≠ b) (hao : a ≠ out)
    (hbo : b ≠ out) :
    ∀ (m : ℕ) (ra rb : List Bool), ra.length + rb.length ≤ m →
      ∀ (em : List Bool) (c : Bool) (A B C : List Glyph)
        (g : Reg → Glyph) (X : Stk → List Glyph),
        g rF = gGo → g rC = Glyph.bit c →
        X a = ra.map Glyph.bit ++ gmk a :: A → X b = rb.map Glyph.bit ++ gmk b :: B →
        X out = (em.map Glyph.bit).reverse ++ gmk out :: C →
        ∃ s' n em', Ev main (.loop rF gGo (asw_addBody a b out rC rT rX rY rU rV rF))
            ⟨g, X⟩ s' n ∧ n ≤ 21 * (ra.length + rb.length + 2) ∧
          s'.stk a = gmk a :: A ∧ s'.stk b = gmk b :: B ∧
          s'.reg rC = Glyph.bit false ∧ s'.reg rF ≠ gGo ∧
          s'.stk out = (em'.map Glyph.bit).reverse ++ gmk out :: C ∧
          ofBits em' = ofBits em + 2 ^ em.length * (ofBits ra + ofBits rb + c.toNat) := by
  intro m
  induction m with
  | zero =>
      intro ra rb hlen em c A B C g X hF hC ha hb ho
      have hra : ra = [] := List.length_eq_zero_iff.mp (by omega)
      have hrb : rb = [] := List.length_eq_zero_iff.mp (by omega)
      subst hra; subst hrb
      obtain ⟨s1, n1, hbody, hn1, h1a, h1b, h1o, h1C, h1F, h1F2⟩ :=
        asw_addBody_ev (main := main) hab hao hbo hF hC ha hb ho
      have hstop : s1.reg rF = gStop := by
        rw [h1F]
        exact ⟨rfl, rfl, by cases c <;> rfl⟩
      have hne : s1.reg rF ≠ gGo := by rw [hstop]; decide
      have hloop : Ev main (.loop rF gGo (asw_addBody a b out rC rT rX rY rU rV rF)) ⟨g, X⟩ s1
          (n1 + 1 + 1) := Ev.loopT hF hbody (Ev.loopF hne)
      refine ⟨s1, _, em ++ [asw_addOutBit false false c], hloop, by omega, ?_, ?_, ?_, hne, ?_, ?_⟩
      · simpa using h1a
      · simpa using h1b
      · rw [h1C]; cases c <;> rfl
      · simpa using h1o
      · rw [asw_addOutBit_ff, asw_add_cons_step_nil em c]
        simp [ofBits_nil']
  | succ m ih =>
      intro ra rb hlen em c A B C g X hF hC ha hb ho
      obtain ⟨s1, n1, hbody, hn1, h1a, h1b, h1o, h1C, h1F, h1F2⟩ :=
        asw_addBody_ev (main := main) hab hao hbo hF hC ha hb ho
      have hstep := asw_add_cons_step ra rb em c
      by_cases hstop : s1.reg rF = gStop
      · obtain ⟨hra, hrb, hcar⟩ := h1F.mp hstop
        have hloop : Ev main (.loop rF gGo (asw_addBody a b out rC rT rX rY rU rV rF)) ⟨g, X⟩ s1
            (n1 + 1 + 1) := Ev.loopT hF hbody (Ev.loopF (by rw [hstop]; decide))
        refine ⟨s1, _, em ++ [asw_addOutBit (ra.headD false) (rb.headD false) c], hloop, by omega,
          ?_, ?_, ?_, by rw [hstop]; decide, ?_, ?_⟩
        · rw [h1a, hra]; simp
        · rw [h1b, hrb]; simp
        · rw [h1C, hcar]
        · exact h1o
        · rw [hra, hrb] at hstep hcar ⊢
          rw [asw_addOutBit_nilD, asw_add_cons_step_nil em c]
          simp [ofBits_nil']
      · have hgo : s1.reg rF = gGo := by
          rcases h1F2 with h | h
          · exact h
          · exact absurd h hstop
        have hne : ra ≠ [] ∨ rb ≠ [] := by
          by_contra hc
          push_neg at hc
          exact hstop (h1F.mpr ⟨hc.1, hc.2, by rw [hc.1, hc.2]; cases c <;> rfl⟩)
        have hrel : ra.tail.length + rb.tail.length + 1 ≤ ra.length + rb.length := by
          rcases hne with h | h
          · have h1 := tail_length_lt ra h
            have h2 := tail_length_le rb
            omega
          · have h1 := tail_length_le ra
            have h2 := tail_length_lt rb h
            omega
        have hdec : ra.tail.length + rb.tail.length ≤ m := by omega
        obtain ⟨s2, n2, em2, hloop, hn2, h2a, h2b, h2C, h2F, h2o, h2v⟩ :=
          ih ra.tail rb.tail hdec (em ++ [asw_addOutBit (ra.headD false) (rb.headD false) c])
            (asw_addCarry (ra.headD false) (rb.headD false) c) A B C s1.reg s1.stk
            hgo h1C h1a h1b h1o
        refine ⟨s2, _, em2, Ev.loopT hF hbody hloop, ?_, h2a, h2b, h2C, h2F, h2o, ?_⟩
        · omega
        · rw [h2v]; exact hstep

/-! ## The specified word -/

theorem asw_addLoop_spec {main : HvdH.Cmd} (a b out : HvdH.Stk) (hab : a ≠ b) (hao : a ≠ out)
    (hbo : b ≠ out) :
    ∀ (ra rb em : List Bool) (c : Bool) (A B C : List HvdH.Glyph)
      (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      g Work.IntLib.AddSub.rC = HvdH.Glyph.bit c →
      g Work.IntLib.AddSub.rF = Work.IntLib.AddSub.gGo →
      X a = ra.map HvdH.Glyph.bit ++ Work.IntLib.AddSub.gmk a :: A →
      X b = rb.map HvdH.Glyph.bit ++ Work.IntLib.AddSub.gmk b :: B →
      X out = (em.map HvdH.Glyph.bit).reverse ++ Work.IntLib.AddSub.gmk out :: C →
      ∃ s' n, Work.IntLib.AddSub.Ev main (Work.IntLib.AddSub.asw_addLoop a b out) ⟨g, X⟩ s' n ∧
        n ≤ 31 * (ra.length + rb.length + 2) ∧
        s'.stk a = Work.IntLib.AddSub.gmk a :: A ∧
        s'.stk b = Work.IntLib.AddSub.gmk b :: B ∧
        s'.reg Work.IntLib.AddSub.rC = HvdH.Glyph.bit false ∧
        s'.reg Work.IntLib.AddSub.rF ≠ Work.IntLib.AddSub.gGo ∧
        (∃ em' : List Bool,
          s'.stk out = (em'.map HvdH.Glyph.bit).reverse ++ Work.IntLib.AddSub.gmk out :: C ∧
          Work.IntLib.ofBits em' = Work.IntLib.ofBits em +
            2 ^ em.length * (Work.IntLib.ofBits ra + Work.IntLib.ofBits rb + c.toNat)) := by
  intro ra rb em c A B C g X hC hF ha hb ho
  let g1 : Reg → Glyph := Function.update g rF gGo
  have hset : Ev main (.set rF gGo) ⟨g, X⟩ ⟨g1, X⟩ 1 := ev_set' main rF gGo g X
  have hC1 : g1 rC = Glyph.bit c := by
    simp only [g1, upReg_ne (show rC ≠ rF by decide), hC]
  have hF1 : g1 rF = gGo := by simp only [g1, upReg_same]
  obtain ⟨s', n, em', hloop, hn, hsa, hsb, hsC, hsF, hso, hsv⟩ :=
    asw_addLoop_loop_ev (main := main) hab hao hbo (ra.length + rb.length) ra rb le_rfl
      em c A B C g1 X hF1 hC1 ha hb ho
  have hmain : Ev main (asw_addLoop a b out) ⟨g, X⟩ s' (1 + n) := by
    simp only [asw_addLoop, seqs]
    exact Ev.seq hset hloop
  exact ⟨s', 1 + n, hmain, by omega, hsa, hsb, hsC, hsF, ⟨em', hso, hsv⟩⟩

end AddSub
end Work.IntLib
