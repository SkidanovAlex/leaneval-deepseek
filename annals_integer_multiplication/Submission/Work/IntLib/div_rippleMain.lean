import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.divPush
import Submission.Work.IntLib.rippleArith
import Submission.Work.IntLib.div_rippleProgBR_eval
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.eval_subBitProg

/-!
# `div_rippleMain`: the ripple subtraction of the long-division core, mirrored

`Div.rippleMain = Div.rippleProg Div.stR Div.stB gR gB` consumes the bit region `bitsG X` of stack
`Div.stR` and, for each bit, ripples through the corresponding bit of the region `bitsG Y` of stack
`Div.stB`; it accumulates the bits of `Y` (reversed) on `Div.stC`, the bits of `X` (reversed) on
`Div.stD`, the result bits (reversed) on `Div.stS` and leaves the final borrow in `Div.rgC`.

The companion module `Submission/Work/IntLib/div_rippleProgBR_eval.lean` proves the *other*
orientation (`Div.rippleProg Div.stB Div.stR gB gR`, i.e. `X` on `Div.stB`, `Y` on `Div.stR`),
through the invariant `ripSt` and the unrolling lemma `ripSt_loop`.

The two orientations differ only by the involution of the 16 stacks that swaps `Div.stB` and
`Div.stR`, together with the involution of `Glyph` that swaps the two markers `gB` and `gR`.
This file proves that `Eval` is equivariant under the induced map on states and commands
(`eval_cmap`), and then transports `ripSt_loop` along it.  The frame property of `Eval` comes for
free from `ripSt`'s own frame lemmas.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.IntLib

open HvdH

/-! ## 1. The stack involution -/

/-- The involution of the 16 stacks that swaps `Div.stB` and `Div.stR`. -/
def pst (j : Stk) : Stk := if j = Div.stB then Div.stR else if j = Div.stR then Div.stB else j

@[simp] theorem pst_stB : pst Div.stB = Div.stR := by decide
@[simp] theorem pst_stR : pst Div.stR = Div.stB := by decide
@[simp] theorem pst_stS : pst Div.stS = Div.stS := by decide
@[simp] theorem pst_stC : pst Div.stC = Div.stC := by decide
@[simp] theorem pst_stD : pst Div.stD = Div.stD := by decide
@[simp] theorem pst_st0 : pst (0 : Stk) = 0 := by decide
@[simp] theorem pst_stP : pst Div.stP = Div.stP := by decide
@[simp] theorem pst_stQ : pst Div.stQ = Div.stQ := by decide

theorem pst_of_ne {j : Stk} (h1 : j ≠ Div.stB) (h2 : j ≠ Div.stR) : pst j = j := by
  simp [pst, h1, h2]

@[simp] theorem pst_apply_apply (j : Stk) : pst (pst j) = j := by
  by_cases h1 : j = Div.stB
  · subst h1; rw [pst_stB, pst_stR]
  · by_cases h2 : j = Div.stR
    · subst h2; rw [pst_stR, pst_stB]
    · rw [pst_of_ne h1 h2, pst_of_ne h1 h2]

theorem pst_eq_iff {j k : Stk} : pst j = k ↔ j = pst k := by
  constructor
  · intro h; rw [← pst_apply_apply j, h]
  · intro h; rw [h, pst_apply_apply]

@[simp] theorem pst_eq_eq (j k : Stk) : (pst j = k) = (j = pst k) := propext pst_eq_iff

/-! ## 2. The glyph involution -/

/-- The involution of `Glyph` that swaps the markers `gB` and `gR`. -/
def gsw : Glyph → Glyph
  | .mk i => .mk (pst i)
  | g => g

@[simp] theorem gsw_mk (i : Stk) : gsw (Glyph.mk i) = Glyph.mk (pst i) := rfl
@[simp] theorem gsw_bit (b : Bool) : gsw (Glyph.bit b) = Glyph.bit b := rfl
@[simp] theorem gsw_eos : gsw Glyph.eos = Glyph.eos := rfl
@[simp] theorem gsw_gB : gsw gB = gR := by decide
@[simp] theorem gsw_gR : gsw gR = gB := by decide
@[simp] theorem gsw_gS : gsw gS = gS := by decide
@[simp] theorem gsw_gC : gsw gC = gC := by decide
@[simp] theorem gsw_gD : gsw gD = gD := by decide
@[simp] theorem gsw_gX : gsw gX = gX := by decide
@[simp] theorem gsw_gY : gsw gY = gY := by decide
@[simp] theorem gsw_gP : gsw gP = gP := by decide
@[simp] theorem gsw_gQ : gsw gQ = gQ := by decide
@[simp] theorem gsw_mk0 : gsw (Glyph.mk 0) = Glyph.mk 0 := by decide

@[simp] theorem gsw_gsw (g : Glyph) : gsw (gsw g) = g := by
  cases g with
  | mk i => rw [gsw_mk, gsw_mk, pst_apply_apply]
  | eos => rfl
  | inp a b => rfl
  | bit b => rfl
  | pos => rfl
  | neg => rfl
  | iend => rfl
  | nil => rfl
  | cons => rfl

@[simp] theorem map_gsw_gsw (l : List Glyph) : (l.map gsw).map gsw = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

@[simp] theorem bitsG_map_gsw (l : List Bool) : (bitsG l).map gsw = bitsG l := by
  induction l with
  | nil => rfl
  | cons b t ih => simp [bitsG, ih]

@[simp] theorem headD_map_gsw (l : List Glyph) :
    (l.map gsw).headD Glyph.eos = gsw (l.headD Glyph.eos) := by
  cases l <;> simp

@[simp] theorem option_getD_map_gsw (l : List Glyph) :
    (Option.map gsw l.head?).getD Glyph.eos = gsw (l.head?.getD Glyph.eos) := by
  cases l <;> simp

@[simp] theorem gsw_comp_bit : (gsw ∘ Glyph.bit) = Glyph.bit := funext gsw_bit

@[simp] theorem gsw_comp_gsw : (gsw ∘ gsw) = id := funext gsw_gsw


theorem gsw_injective : Function.Injective gsw := fun a b h => by
  have := congrArg gsw h
  simpa using this

/-! ## 3. The state map -/

/-- The map on states induced by `pst` and `gsw`: stack `j` becomes (the `gsw`-image of) the contents
of stack `pst j`, and every register is `gsw`-mapped. -/
def ssw (s : State) : State := ⟨fun r => gsw (s.reg r), fun j => (s.stk (pst j)).map gsw⟩

@[simp] theorem ssw_reg (s : State) (r : Reg) : (ssw s).reg r = gsw (s.reg r) := rfl
@[simp] theorem ssw_stk (s : State) (j : Stk) : (ssw s).stk j = (s.stk (pst j)).map gsw := rfl

@[simp] theorem ssw_ssw (s : State) : ssw (ssw s) = s := by
  refine State.ext_mk ?_ ?_
  · funext r; simp only [ssw_reg]; exact gsw_gsw _
  · funext j; simp only [ssw_stk, pst_apply_apply]; exact map_gsw_gsw _

@[simp] theorem ssw_updReg (s : State) (r : Reg) (g : Glyph) :
    ssw (s.updReg r g) = (ssw s).updReg r (gsw g) := by
  refine State.ext_mk ?_ ?_
  · funext r'
    by_cases h : r' = r
    · subst h; simp [ssw, State.updReg, Function.update_apply]
    · simp [ssw, State.updReg, Function.update_apply, h]
  · funext j; simp [ssw, State.updReg]

@[simp] theorem ssw_updStk (s : State) (k : Stk) (l : List Glyph) :
    ssw (s.updStk k l) = (ssw s).updStk (pst k) (l.map gsw) := by
  refine State.ext_mk ?_ ?_
  · funext r; simp [ssw, State.updStk]
  · funext j
    by_cases h : pst j = k
    · have h' : j = pst k := pst_eq_iff.mp h
      simp [ssw, State.updStk, State.updStk_apply, h, h']
    · have h' : ¬ (j = pst k) := fun hj => h (pst_eq_iff.mpr hj)
      simp [ssw, State.updStk, State.updStk_apply, h, h']

/-! ## 4. Commutation with the primitive commands -/

theorem ssw_pop (s : State) (k : Stk) (r : Reg) :
    ssw ⟨Function.update s.reg r ((s.stk k).headD Glyph.eos), Function.update s.stk k (s.stk k).tail⟩
      = ⟨Function.update (ssw s).reg r (((ssw s).stk (pst k)).headD Glyph.eos),
          Function.update (ssw s).stk (pst k) (((ssw s).stk (pst k)).tail)⟩ := by
  refine State.ext_mk ?_ ?_
  · funext r'
    by_cases h : r' = r
    · subst h
      simp [ssw, Function.update_apply, headD_map_gsw]
    · simp [ssw, Function.update_apply, h]
  · funext j
    by_cases h : pst j = k
    · have h' : j = pst k := pst_eq_iff.mp h
      simp [ssw, Function.update_apply, h, h']
    · have h' : ¬ (j = pst k) := fun hj => h (pst_eq_iff.mpr hj)
      simp [ssw, Function.update_apply, h, h']

theorem ssw_peek (s : State) (k : Stk) (r : Reg) :
    ssw ⟨Function.update s.reg r ((s.stk k).headD Glyph.eos), s.stk⟩
      = ⟨Function.update (ssw s).reg r (((ssw s).stk (pst k)).headD Glyph.eos), (ssw s).stk⟩ := by
  refine State.ext_mk ?_ ?_
  · funext r'
    by_cases h : r' = r
    · subst h
      simp [ssw, Function.update_apply, headD_map_gsw]
    · simp [ssw, Function.update_apply, h]
  · funext j; simp [ssw]

theorem ssw_push (s : State) (k : Stk) (r : Reg) :
    ssw ⟨s.reg, Function.update s.stk k (s.reg r :: s.stk k)⟩
      = ⟨(ssw s).reg, Function.update (ssw s).stk (pst k) ((ssw s).reg r :: (ssw s).stk (pst k))⟩ := by
  refine State.ext_mk ?_ ?_
  · funext r'; simp [ssw]
  · funext j
    by_cases h : pst j = k
    · have h' : j = pst k := pst_eq_iff.mp h
      simp [ssw, Function.update_apply, h, h']
    · have h' : ¬ (j = pst k) := fun hj => h (pst_eq_iff.mpr hj)
      simp [ssw, Function.update_apply, h, h']

theorem ssw_set (s : State) (r : Reg) (c : Glyph) :
    ssw ⟨Function.update s.reg r c, s.stk⟩ = ⟨Function.update (ssw s).reg r (gsw c), (ssw s).stk⟩ := by
  refine State.ext_mk ?_ ?_
  · funext r'
    by_cases h : r' = r
    · subst h; simp [ssw, Function.update_apply]
    · simp [ssw, Function.update_apply, h]
  · funext j; simp [ssw]

theorem ssw_mov (s : State) (d sc : Reg) :
    ssw ⟨Function.update s.reg d (s.reg sc), s.stk⟩
      = ⟨Function.update (ssw s).reg d ((ssw s).reg sc), (ssw s).stk⟩ := by
  refine State.ext_mk ?_ ?_
  · funext r'
    by_cases h : r' = d
    · subst h; simp [ssw, Function.update_apply]
    · simp [ssw, Function.update_apply, h]
  · funext j; simp [ssw]

/-! ## 5. The command map -/

/-- Relabelling of commands: stacks are moved along `pst`, glyph constants along `gsw`. -/
def cmap : Cmd → Cmd
  | .skip => .skip
  | .pop k r => .pop (pst k) r
  | .peek k r => .peek (pst k) r
  | .push k r => .push (pst k) r
  | .set r c => .set r (gsw c)
  | .mov d sc => .mov d sc
  | .seq a b => .seq (cmap a) (cmap b)
  | .ite r c a b => .ite r (gsw c) (cmap a) (cmap b)
  | .loop r c b => .loop r (gsw c) (cmap b)
  | .self => .self

@[simp] theorem cmap_skip : cmap .skip = .skip := rfl
@[simp] theorem cmap_pop (k : Stk) (r : Reg) : cmap (.pop k r) = .pop (pst k) r := rfl
@[simp] theorem cmap_peek (k : Stk) (r : Reg) : cmap (.peek k r) = .peek (pst k) r := rfl
@[simp] theorem cmap_push (k : Stk) (r : Reg) : cmap (.push k r) = .push (pst k) r := rfl
@[simp] theorem cmap_set (r : Reg) (c : Glyph) : cmap (.set r c) = .set r (gsw c) := rfl
@[simp] theorem cmap_mov (d sc : Reg) : cmap (.mov d sc) = .mov d sc := rfl
@[simp] theorem cmap_seq (a b : Cmd) : cmap (.seq a b) = .seq (cmap a) (cmap b) := rfl
@[simp] theorem cmap_ite (r : Reg) (c : Glyph) (a b : Cmd) :
    cmap (.ite r c a b) = .ite r (gsw c) (cmap a) (cmap b) := rfl
@[simp] theorem cmap_loop (r : Reg) (c : Glyph) (b : Cmd) :
    cmap (.loop r c b) = .loop r (gsw c) (cmap b) := rfl
@[simp] theorem cmap_self : cmap .self = .self := rfl

@[simp] theorem cmap_seqs (l : List Cmd) : cmap (Div.seqs l) = Div.seqs (l.map cmap) := by
  induction l with
  | nil => rfl
  | cons c cs ih => rw [Div.seqs_cons, cmap_seq, List.map_cons, Div.seqs_cons, ih]

theorem cmap_consumeStep (k : Stk) (T : Glyph) (r : Reg) (h : Cmd) :
    cmap (consumeStep k T r h) = consumeStep (pst k) (gsw T) r (cmap h) := by
  simp [consumeStep, gsw_eos, gsw_mk0]

theorem cmap_consumeLoop (k : Stk) (T : Glyph) (r : Reg) (h : Cmd) :
    cmap (consumeLoop k T r h) = consumeLoop (pst k) (gsw T) r (cmap h) := by
  simp [consumeLoop, cmap_consumeStep, gsw_eos]

theorem cmap_consume (k : Stk) (T : Glyph) (r : Reg) (h : Cmd) :
    cmap (consume k T r h) = consume (pst k) (gsw T) r (cmap h) := by
  simp [consume, cmap_consumeLoop, gsw_eos]

theorem cmap_subBitProg (rr rb rc rs : Reg) :
    cmap (subBitProg rr rb rc rs) = subBitProg rr rb rc rs := by
  simp [subBitProg, gsw_bit]

theorem cmap_rippleBody (sb : Stk) : cmap (Div.rippleBody sb) = Div.rippleBody (pst sb) := by
  simp [Div.rippleBody, Div.seqs, cmap_seqs, cmap_subBitProg, gsw_bit, pst_stS, pst_stC, pst_stD]

theorem cmap_rippleProg (sa sb : Stk) (ma mb : Glyph) :
    cmap (Div.rippleProg sa sb ma mb) = Div.rippleProg (pst sa) (pst sb) (gsw ma) (gsw mb) := by
  simp [Div.rippleProg, Div.seqs, cmap_seqs, cmap_consume, cmap_rippleBody, gsw_bit]

/-- A command is `SelfFree` if it contains no recursive call `Cmd.self`. -/
def SelfFree : Cmd → Prop
  | .skip => True
  | .pop _ _ => True
  | .peek _ _ => True
  | .push _ _ => True
  | .set _ _ => True
  | .mov _ _ => True
  | .seq a b => SelfFree a ∧ SelfFree b
  | .ite _ _ a b => SelfFree a ∧ SelfFree b
  | .loop _ _ body => SelfFree body
  | .self => False

@[simp] theorem selfFree_skip : SelfFree .skip := trivial
@[simp] theorem selfFree_pop (k : Stk) (r : Reg) : SelfFree (.pop k r) := trivial
@[simp] theorem selfFree_peek (k : Stk) (r : Reg) : SelfFree (.peek k r) := trivial
@[simp] theorem selfFree_push (k : Stk) (r : Reg) : SelfFree (.push k r) := trivial
@[simp] theorem selfFree_set (r : Reg) (c : Glyph) : SelfFree (.set r c) := trivial
@[simp] theorem selfFree_mov (d sc : Reg) : SelfFree (.mov d sc) := trivial
@[simp] theorem selfFree_seq {a b : Cmd} : SelfFree (.seq a b) ↔ SelfFree a ∧ SelfFree b := Iff.rfl
@[simp] theorem selfFree_ite {r : Reg} {c : Glyph} {a b : Cmd} :
    SelfFree (.ite r c a b) ↔ SelfFree a ∧ SelfFree b := Iff.rfl
@[simp] theorem selfFree_loop {r : Reg} {c : Glyph} {b : Cmd} :
    SelfFree (.loop r c b) ↔ SelfFree b := Iff.rfl
@[simp] theorem not_selfFree_self : ¬ SelfFree .self := not_false

/-! ## 6. Equivariance of `Eval` -/

theorem eval_cmap (main : Cmd) : ∀ (c : Cmd) (s t : State) (n : ℕ),
    Eval main c s t n → SelfFree c → Eval main (cmap c) (ssw s) (ssw t) n := by
  intro c s t n h
  induction h with
  | skip s => intro _; exact Eval.skip (ssw s)
  | pop k r s =>
    intro _
    rw [cmap_pop, ssw_pop]
    exact Eval.pop (main := main) (pst k) r (ssw s)
  | peek k r s =>
    intro _
    rw [cmap_peek, ssw_peek]
    exact Eval.peek (main := main) (pst k) r (ssw s)
  | push k r s =>
    intro _
    rw [cmap_push, ssw_push]
    exact Eval.push (main := main) (pst k) r (ssw s)
  | set r c s =>
    intro _
    rw [cmap_set, ssw_set]
    exact Eval.set (main := main) r (gsw c) (ssw s)
  | mov d sc s =>
    intro _
    rw [cmap_mov, ssw_mov]
    exact Eval.mov (main := main) d sc (ssw s)
  | seq h1 h2 ih1 ih2 =>
    intro hsf
    exact Eval.seq (ih1 hsf.1) (ih2 hsf.2)
  | iteT hr h1 ih1 =>
    intro hsf
    refine Eval.iteT ?_ (ih1 hsf.1)
    rw [ssw_reg, hr]
  | iteF hr h1 ih1 =>
    intro hsf
    refine Eval.iteF ?_ (ih1 hsf.2)
    rw [ssw_reg]
    exact fun hcon => hr (gsw_injective hcon)
  | loopF hr =>
    intro _
    refine Eval.loopF ?_
    rw [ssw_reg]
    exact fun hc => hr (gsw_injective hc)
  | loopT hr h1 h2 ih1 ih2 =>
    intro hsf
    refine Eval.loopT ?_ (ih1 hsf) (ih2 hsf)
    rw [ssw_reg, hr]
  | self h1 ih1 =>
    intro hsf
    exact absurd hsf (by simp)



/-! ## 7. The shape of `ssw (ripSt ...)` -/

theorem ssw_ripSt_stR (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool) (i : ℕ) :
    (ssw (ripSt S blB blR blC blD blS A B i)).stk Div.stR =
      (bitsG A).drop i ++ [gR] ++ blB.map gsw := by
  rw [ssw_stk, pst_stR, ripSt_stB]
  simp [List.map_drop]

theorem ssw_ripSt_stB (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool) (i : ℕ) :
    (ssw (ripSt S blB blR blC blD blS A B i)).stk Div.stB =
      (bitsG B).drop i ++ [gB] ++ blR.map gsw := by
  rw [ssw_stk, pst_stB, ripSt_stR]
  simp [List.map_drop]

theorem ssw_ripSt_stC (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool) (i : ℕ) :
    (ssw (ripSt S blB blR blC blD blS A B i)).stk Div.stC =
      (bitsG (B.take i)).reverse ++ [gC] ++ blC.map gsw := by
  rw [ssw_stk, pst_stC, ripSt_stC]
  simp

theorem ssw_ripSt_stD (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool) (i : ℕ) :
    (ssw (ripSt S blB blR blC blD blS A B i)).stk Div.stD =
      (bitsG (A.take i)).reverse ++ [gD] ++ blD.map gsw := by
  rw [ssw_stk, pst_stD, ripSt_stD]
  simp

theorem ssw_ripSt_stS (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool) (i : ℕ) :
    (ssw (ripSt S blB blR blC blD blS A B i)).stk Div.stS =
      (bitsG ((subRippleBits (A.take i) (B.take i) false).2)).reverse ++ [gS] ++ blS.map gsw := by
  rw [ssw_stk, pst_stS, ripSt_stS]
  simp

theorem ssw_ripSt_reg_rgC (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool) (i : ℕ) :
    (ssw (ripSt S blB blR blC blD blS A B i)).reg Div.rgC =
      Glyph.bit ((subRippleBits (A.take i) (B.take i) false).1) := by
  rw [ssw_reg, ripSt_reg_rgC, gsw_bit]

theorem ssw_ripSt_stk_other (S : State) (blB blR blC blD blS : List Glyph) (A B : List Bool)
    (i : ℕ) (j : Stk) (h1 : j ≠ Div.stB) (h2 : j ≠ Div.stR) (h3 : j ≠ Div.stC)
    (h4 : j ≠ Div.stD) (h5 : j ≠ Div.stS) :
    (ssw (ripSt S blB blR blC blD blS A B i)).stk j = (S.stk j).map gsw := by
  rw [ssw_stk, pst_of_ne h1 h2, ripSt_stk_other S blB blR blC blD blS A B i j h1 h2 h3 h4 h5]

/-! ## 8. `SelfFree` of the programs -/

theorem selfFree_subBitProg (rr rb rc rs : Reg) : SelfFree (subBitProg rr rb rc rs) := by
  simp [subBitProg, SelfFree]

theorem selfFree_rippleBody (sb : Stk) : SelfFree (Div.rippleBody sb) := by
  simp [Div.rippleBody, Div.seqs, SelfFree, subBitProg]

theorem selfFree_consumeLoop_BR :
    SelfFree (consumeLoop Div.stB gB rLoop (Div.rippleBody Div.stR)) := by
  simp [consumeLoop, consumeStep, SelfFree, selfFree_rippleBody]

/-! ## 9. The theorem -/

theorem div_rippleMain (main : HvdH.Cmd) (b0 : HvdH.State) (X Y : List Bool) (L : ℕ)
    (hX : X.length = L) (hY : Y.length = L) (S : HvdH.State)
    (hR : S.stk Work.IntLib.Div.stR = Work.IntLib.bitsG X ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR)
    (hB : S.stk Work.IntLib.Div.stB = Work.IntLib.bitsG Y ++ [Work.IntLib.gB] ++ b0.stk Work.IntLib.Div.stB)
    (hS5 : S.stk Work.IntLib.Div.stS = [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS)
    (hS6 : S.stk Work.IntLib.Div.stC = [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC)
    (hS7 : S.stk Work.IntLib.Div.stD = [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD) :
    ∃ s' n, HvdH.Eval main Work.IntLib.Div.rippleMain S s' n ∧ n ≤ 15 * (L + 2) + 12 ∧
      s'.stk Work.IntLib.Div.stR = b0.stk Work.IntLib.Div.stR ∧
      s'.stk Work.IntLib.Div.stB = b0.stk Work.IntLib.Div.stB ∧
      s'.stk Work.IntLib.Div.stS = Work.IntLib.bitsG (Work.IntLib.subRippleBits X Y false).2.reverse ++ [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS ∧
      s'.stk Work.IntLib.Div.stC = Work.IntLib.bitsG Y.reverse ++ [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC ∧
      s'.stk Work.IntLib.Div.stD = Work.IntLib.bitsG X.reverse ++ [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD ∧
      s'.reg Work.IntLib.Div.rgC = HvdH.Glyph.bit (Work.IntLib.subRippleBits X Y false).1 ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.Div.stR → j ≠ Work.IntLib.Div.stB → j ≠ Work.IntLib.Div.stS →
        j ≠ Work.IntLib.Div.stC → j ≠ Work.IntLib.Div.stD → s'.stk j = S.stk j) := by
  have hXY : X.length = Y.length := by omega
  -- the relabelled base state
  set S₀ : State := ssw S with hS₀
  set blB : List Glyph := (b0.stk Div.stR).map gsw with hblB
  set blR : List Glyph := (b0.stk Div.stB).map gsw with hblR
  set blC : List Glyph := (b0.stk Div.stC).map gsw with hblC
  set blD : List Glyph := (b0.stk Div.stD).map gsw with hblD
  set blS : List Glyph := (b0.stk Div.stS).map gsw with hblS
  have hB₀ : S₀.stk Div.stB = bitsG X ++ [gB] ++ blB := by
    rw [hS₀, ssw_stk, pst_stB, hR, hblB]; simp
  have hR₀ : S₀.stk Div.stR = bitsG Y ++ [gR] ++ blR := by
    rw [hS₀, ssw_stk, pst_stR, hB, hblR]; simp
  have hC₀ : S₀.stk Div.stC = [gC] ++ blC := by
    rw [hS₀, ssw_stk, pst_stC, hS6, hblC]; simp
  have hD₀ : S₀.stk Div.stD = [gD] ++ blD := by
    rw [hS₀, ssw_stk, pst_stD, hS7, hblD]; simp
  have hS₀5 : S₀.stk Div.stS = [gS] ++ blS := by
    rw [hS₀, ssw_stk, pst_stS, hS5, hblS]; simp
  -- the loop of the companion orientation, transported along `ssw`
  obtain ⟨ml, hevl, hml⟩ := ripSt_loop main S₀ blB blR blC blD blS X Y hXY
  have hcm : cmap (consumeLoop Div.stB gB rLoop (Div.rippleBody Div.stR))
      = consumeLoop Div.stR gR rLoop (Div.rippleBody Div.stB) := by
    rw [cmap_consumeLoop, cmap_rippleBody, pst_stB, gsw_gB, pst_stR]
  have hevl' : Eval main (consumeLoop Div.stR gR rLoop (Div.rippleBody Div.stB))
      (ssw (ripSt S₀ blB blR blC blD blS X Y 0))
      (ssw ((ripSt S₀ blB blR blC blD blS X Y X.length).updReg rLoop (Glyph.mk 0))) ml := by
    have h := eval_cmap main (consumeLoop Div.stB gB rLoop (Div.rippleBody Div.stR))
      (ripSt S₀ blB blR blC blD blS X Y 0)
      ((ripSt S₀ blB blR blC blD blS X Y X.length).updReg rLoop (Glyph.mk 0)) ml hevl
      selfFree_consumeLoop_BR
    rwa [hcm] at h
  -- the state after the two preparatory `set`s
  set S₁ : State := (S.updReg Div.rgC (Glyph.bit false)).updReg rLoop Glyph.eos with hS₁
  have hstart : ssw (ripSt S₀ blB blR blC blD blS X Y 0) = S₁ := by
    rw [ripSt_zero S₀ blB blR blC blD blS X Y hB₀ hR₀ hC₀ hD₀ hS₀5, ssw_updReg, ssw_updReg,
      hS₀, ssw_ssw, gsw_bit, gsw_eos, hS₁]
  -- the terminal states
  set E : State := (ripSt S₀ blB blR blC blD blS X Y X.length).updReg rLoop (Glyph.mk 0) with hE
  set T : State := ssw E with hT
  set T2 : State := State.tPop T Div.stR rLoop with hT2
  set T3 : State := State.tPop T2 Div.stB Div.rgB with hT3
  have e1 : Eval main (.set Div.rgC (Glyph.bit false)) S
      (S.updReg Div.rgC (Glyph.bit false)) 1 := Eval.set _ _ _
  have e2 : Eval main (.set rLoop Glyph.eos) (S.updReg Div.rgC (Glyph.bit false)) S₁ 1 := by
    rw [hS₁]; exact Eval.set _ _ _
  have e3 : Eval main (consumeLoop Div.stR gR rLoop (Div.rippleBody Div.stB)) S₁ T ml := by
    rw [← hstart, hT, hE]; exact hevl'
  have e4 : Eval main (.pop Div.stR rLoop) T T2 1 := by rw [hT2]; exact Eval.pop _ _ _
  have e5 : Eval main (.pop Div.stB Div.rgB) T2 T3 1 := by rw [hT3]; exact Eval.pop _ _ _
  have e6 : Eval main .skip T3 T3 1 := Eval.skip T3
  have hwhole : Eval main Div.rippleMain S T3 (1 + ((1 + ml) + (1 + (1 + 1)))) := by
    have h := Eval.seq e1 (Eval.seq (Eval.seq e2 e3) (Eval.seq e4 (Eval.seq e5 e6)))
    simpa [Div.rippleMain, Div.rippleProg, Div.seqs, consume] using h
  -- the shape of `T`
  have hTstR : T.stk Div.stR = gR :: b0.stk Div.stR := by
    rw [hT, hE, ssw_updReg, gsw_mk0, State.updReg_stk, ssw_ripSt_stR, bitsG_drop_length,
      hblB, map_gsw_gsw]
    simp
  have hTstB : T.stk Div.stB = gB :: b0.stk Div.stB := by
    rw [hT, hE, ssw_updReg, gsw_mk0, State.updReg_stk, ssw_ripSt_stB, hXY, bitsG_drop_length,
      hblR, map_gsw_gsw]
    simp
  have hTstS : T.stk Div.stS = bitsG (subRippleBits X Y false).2.reverse ++ [gS] ++ b0.stk Div.stS := by
    rw [hT, hE, ssw_updReg, gsw_mk0, State.updReg_stk, ssw_ripSt_stS, List.take_length, hXY,
      List.take_length, hblS, map_gsw_gsw]
    simp only [List.map_reverse]
  have hTstC : T.stk Div.stC = bitsG Y.reverse ++ [gC] ++ b0.stk Div.stC := by
    rw [hT, hE, ssw_updReg, gsw_mk0, State.updReg_stk, ssw_ripSt_stC, hXY, List.take_length,
      hblC, map_gsw_gsw]
    simp only [List.map_reverse]
  have hTstD : T.stk Div.stD = bitsG X.reverse ++ [gD] ++ b0.stk Div.stD := by
    rw [hT, hE, ssw_updReg, gsw_mk0, State.updReg_stk, ssw_ripSt_stD, List.take_length,
      hblD, map_gsw_gsw]
    simp only [List.map_reverse]
  have hTreg : T.reg Div.rgC = Glyph.bit ((subRippleBits X Y false).1) := by
    have hne : ¬ (Div.rgC = rLoop) := by decide
    rw [hT, hE, ssw_updReg, gsw_mk0, State.updReg_apply, if_neg hne, ssw_ripSt_reg_rgC,
      List.take_length, hXY, List.take_length]
  -- after the first `pop`
  have hT2stR : T2.stk Div.stR = b0.stk Div.stR := by
    rw [hT2, Div.tPop_stk_same, hTstR]
    rfl
  have hT2stB : T2.stk Div.stB = gB :: b0.stk Div.stB := by
    rw [hT2, Div.tPop_stk_ne T Div.stR rLoop Div.stB (by decide), hTstB]
  have hT2stS : T2.stk Div.stS
      = bitsG (subRippleBits X Y false).2.reverse ++ [gS] ++ b0.stk Div.stS := by
    rw [hT2, Div.tPop_stk_ne T Div.stR rLoop Div.stS (by decide), hTstS]
  have hT2stC : T2.stk Div.stC = bitsG Y.reverse ++ [gC] ++ b0.stk Div.stC := by
    rw [hT2, Div.tPop_stk_ne T Div.stR rLoop Div.stC (by decide), hTstC]
  have hT2stD : T2.stk Div.stD = bitsG X.reverse ++ [gD] ++ b0.stk Div.stD := by
    rw [hT2, Div.tPop_stk_ne T Div.stR rLoop Div.stD (by decide), hTstD]
  have hT2reg : T2.reg Div.rgC = Glyph.bit ((subRippleBits X Y false).1) := by
    rw [hT2, Div.tPop_reg_ne T Div.stR rLoop Div.rgC (by decide), hTreg]
  -- after the second `pop`
  have hT3stB : T3.stk Div.stB = b0.stk Div.stB := by
    rw [hT3, Div.tPop_stk_same, hT2stB]
    rfl
  have hT3stR : T3.stk Div.stR = b0.stk Div.stR := by
    rw [hT3, Div.tPop_stk_ne T2 Div.stB Div.rgB Div.stR (by decide), hT2stR]
  have hT3stS : T3.stk Div.stS
      = bitsG (subRippleBits X Y false).2.reverse ++ [gS] ++ b0.stk Div.stS := by
    rw [hT3, Div.tPop_stk_ne T2 Div.stB Div.rgB Div.stS (by decide), hT2stS]
  have hT3stC : T3.stk Div.stC = bitsG Y.reverse ++ [gC] ++ b0.stk Div.stC := by
    rw [hT3, Div.tPop_stk_ne T2 Div.stB Div.rgB Div.stC (by decide), hT2stC]
  have hT3stD : T3.stk Div.stD = bitsG X.reverse ++ [gD] ++ b0.stk Div.stD := by
    rw [hT3, Div.tPop_stk_ne T2 Div.stB Div.rgB Div.stD (by decide), hT2stD]
  have hT3reg : T3.reg Div.rgC = Glyph.bit ((subRippleBits X Y false).1) := by
    rw [hT3, Div.tPop_reg_ne T2 Div.stB Div.rgB Div.rgC (by decide), hT2reg]
  have hframe : ∀ j : Stk, j ≠ Div.stR → j ≠ Div.stB → j ≠ Div.stS → j ≠ Div.stC →
      j ≠ Div.stD → T3.stk j = S.stk j := by
    intro j h1 h2 h3 h4 h5
    rw [hT3, Div.tPop_stk_ne T2 Div.stB Div.rgB j h2, hT2,
      Div.tPop_stk_ne T Div.stR rLoop j h1, hT, hE, ssw_updReg, gsw_mk0, State.updReg_stk,
      hS₀, ssw_ripSt_stk_other (ssw S) blB blR blC blD blS X Y X.length j h2 h1 h4 h5 h3,
      ssw_stk, pst_of_ne h2 h1, map_gsw_gsw]
  refine ⟨T3, 1 + ((1 + ml) + (1 + (1 + 1))), hwhole, ?_, hT3stR, hT3stB, hT3stS, hT3stC,
    hT3stD, hT3reg, hframe⟩
  omega

end Work.IntLib
