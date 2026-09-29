import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.ofBitsAPI

/-!
# `IntLib` / `evCarryAdd`: definitions

The word `EvC.evCarryProg` performs one step of the `evalPoly` streaming window: it reads the digit
`h` (whose value encoding sits, reversed, on `aA`), ripples it into the window `W` (bit region on
`aW`, least significant bit on top), and splits the sum `W + h` at bit `b` using the unary counter
`aCW`:

* the low `b` bits are pushed onto `aO` (on top of the finalised bits), so that after the step
  `ofBits LO' = ofBits LO + 2^{LO.length} · ((ofBits W + h) % 2^b)`,
* the remaining high bits become the new window on `aW`, so that
  `ofBits W' = (ofBits W + h) / 2^b`.

Stack allocation (all markers `Shift.gmk k` are preserved; the regions above them are consumed):

| stack | role |
|---|---|
| `aA = 2`  | input: `(Val.enc (.int h)).reverse` |
| `aB = 4`  | the bits of `h`, least significant on top, `iend`-terminated |
| `aW = 1`  | the window `W` (least significant bit on top) -> new window |
| `aO = 3`  | the finalised low bits `LO` (increasing significance, above `pos`) |
| `a2 = 5`  | the bits of `(W+h)/2^b` in reverse push order |
| `aCW = 7` | the unary counter `b` (counts the bits pushed onto `aO`) |

Registers: `rWa` (window bit), `rHa` (digit bit), `rKa` (carry), `rSa` (sum bit), `rZa`
(constant `bit false`), `rLa` (loop flag), `rTa` (peek scratch), `rGa` (glyph scratch).

The addition is a *single* left-to-right scan of the two bit streams: it runs
`max W.length hbits.length` iterations, each consuming one bit of `W` (as long as there is one),
one bit of `hbits` (as long as there is one) and pushing the sum bit, and finally pushes the
carry.  `accF W hbits false k` is the list of the `k` sum bits pushed by the first `k`
iterations, `carryC W hbits false k` the carry afterwards, and `addAll W hbits` the complete
result — a bit list whose value is `ofBits W + ofBits hbits` (`ofBits_addAll`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib
namespace EvC

open HvdH

/-! ## Registers -/

/-- window-bit register -/
def rWa : Reg := 0
/-- digit-bit register -/
def rHa : Reg := 1
/-- carry register -/
def rKa : Reg := 2
/-- sum-bit register -/
def rSa : Reg := 3
/-- register holding the constant `bit false` -/
def rZa : Reg := 4
/-- loop-flag register -/
def rLa : Reg := 5
/-- scratch register for `peek` -/
def rTa : Reg := 6
/-- scratch register holding a glyph -/
def rGa : Reg := 7

theorem rWa_ne_rLa : rWa ≠ rLa := by decide
theorem rHa_ne_rLa : rHa ≠ rLa := by decide
theorem rKa_ne_rLa : rKa ≠ rLa := by decide
theorem rSa_ne_rKa : rSa ≠ rKa := by decide
theorem rZa_ne_rKa : rZa ≠ rKa := by decide
theorem rTa_ne_rLa : rTa ≠ rLa := by decide
theorem rGa_ne_rLa : rGa ≠ rLa := by decide
theorem rLa_ne_rGa : rLa ≠ rGa := by decide
theorem rSa_ne_rLa : rSa ≠ rLa := by decide
theorem rTa_ne_rKa : rTa ≠ rKa := by decide
theorem rWa_ne_rTa : rWa ≠ rTa := by decide
theorem rHa_ne_rTa : rHa ≠ rTa := by decide

/-! ## The one-bit adder -/

/-- sum bit of `a + b + c` -/
def sumBit (a b c : Bool) : Bool := ((a.toNat + b.toNat + c.toNat) % 2 == 1)
/-- carry of `a + b + c` -/
def carryBit (a b c : Bool) : Bool := decide (2 ≤ a.toNat + b.toNat + c.toNat)

theorem toNat_sumBit (a b c : Bool) :
    (sumBit a b c).toNat = (a.toNat + b.toNat + c.toNat) % 2 := by
  rcases a <;> rcases b <;> rcases c <;> decide

theorem toNat_carryBit (a b c : Bool) :
    (carryBit a b c).toNat = (a.toNat + b.toNat + c.toNat) / 2 := by
  rcases a <;> rcases b <;> rcases c <;> decide

theorem toNat_sumBit_add_carry (a b c : Bool) :
    (sumBit a b c).toNat + 2 * (carryBit a b c).toNat = a.toNat + b.toNat + c.toNat := by
  rcases a <;> rcases b <;> rcases c <;> decide

/-- One ripple-addition step: `sa`, `sb` hold operand bits and `sc` the incoming carry; sets `ss`
to the sum bit and `sc` to the outgoing carry. -/
def stepAdd (sa sb sc ss : Reg) : Cmd :=
  .ite sa (Glyph.bit true)
    (.ite sb (Glyph.bit true)
      (.ite sc (Glyph.bit true)
        (.seq (.set ss (Glyph.bit true)) (.set sc (Glyph.bit true)))
        (.seq (.set ss (Glyph.bit false)) (.set sc (Glyph.bit true))))
      (.ite sc (Glyph.bit true)
        (.seq (.set ss (Glyph.bit false)) (.set sc (Glyph.bit true)))
        (.seq (.set ss (Glyph.bit true)) (.set sc (Glyph.bit false)))))
    (.ite sb (Glyph.bit true)
      (.ite sc (Glyph.bit true)
        (.seq (.set ss (Glyph.bit false)) (.set sc (Glyph.bit true)))
        (.seq (.set ss (Glyph.bit true)) (.set sc (Glyph.bit false))))
      (.ite sc (Glyph.bit true)
        (.seq (.set ss (Glyph.bit true)) (.set sc (Glyph.bit false)))
        (.seq (.set ss (Glyph.bit false)) (.set sc (Glyph.bit false)))))

/-- `stepAdd` computes `sumBit`/`carryBit`; the 8-leaf decision tree costs 5. -/
theorem stepAddEv (main : Cmd) (sa sb sc ss : Reg) (s : State) (a b c : Bool)
    (ha : s.reg sa = Glyph.bit a) (hb : s.reg sb = Glyph.bit b) (hc : s.reg sc = Glyph.bit c) :
    Eval main (stepAdd sa sb sc ss) s
      ((s.updReg ss (Glyph.bit (sumBit a b c))).updReg sc (Glyph.bit (carryBit a b c))) 5 := by
  rcases a <;> rcases b <;> rcases c <;>
  simp only [stepAdd, sumBit, carryBit, Bool.toNat_true, Bool.toNat_false, Nat.reduceAdd,
    Nat.reduceMod, decide_true, decide_false] <;>
  (first | refine Eval.iteT ha ?_ | refine Eval.iteF (by rw [ha]; decide) ?_) <;>
  (first | refine Eval.iteT hb ?_ | refine Eval.iteF (by rw [hb]; decide) ?_) <;>
  (first | refine Eval.iteT hc ?_ | refine Eval.iteF (by rw [hc]; decide) ?_) <;>
  exact Eval.seq (Eval.set ss _ s) (Eval.set sc _ _)

/-! ## The arithmetic of the left-to-right bit addition -/

/-- Carry after `k` steps of the addition of `hbits` into `W`. -/
def carryC (W hbits : List Bool) (c0 : Bool) : ℕ → Bool
  | 0 => c0
  | (k + 1) => carryBit (W.getD k false) (hbits.getD k false) (carryC W hbits c0 k)

/-- The `k` sum bits produced by the first `k` steps. -/
def accF (W hbits : List Bool) (c0 : Bool) : ℕ → List Bool
  | 0 => []
  | (k + 1) => accF W hbits c0 k ++
      [sumBit (W.getD k false) (hbits.getD k false) (carryC W hbits c0 k)]

/-- Number of iterations of the addition loop. -/
def addN (W hbits : List Bool) : ℕ := max W.length hbits.length

/-- The complete bit list of `ofBits W + ofBits hbits` produced by the addition. -/
def addAll (W hbits : List Bool) : List Bool :=
  if carryC W hbits false (addN W hbits) then
    accF W hbits false (addN W hbits) ++ [true]
  else accF W hbits false (addN W hbits)

theorem accF_length (W hbits : List Bool) (c : Bool) (k : ℕ) : (accF W hbits c k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [accF, ih]

theorem accF_zero (W hbits : List Bool) (c : Bool) : accF W hbits c 0 = [] := rfl

theorem carryC_zero (W hbits : List Bool) (c : Bool) : carryC W hbits c 0 = c := rfl

theorem addAll_length_le (W hbits : List Bool) :
    (addAll W hbits).length ≤ addN W hbits + 1 := by
  unfold addAll
  split
  · rw [List.length_append, accF_length]
    simp
  · rw [accF_length]
    omega

/-- The loop-continue flag of the addition loop after `k` steps. -/
def addFlag (W hbits : List Bool) (k : ℕ) : Glyph :=
  if k < addN W hbits then Shift.gGo else Shift.gStop

theorem addFlag_of_lt {W hbits : List Bool} {k : ℕ} (h : k < addN W hbits) :
    addFlag W hbits k = Shift.gGo := by simp [addFlag, h]

theorem addFlag_of_le {W hbits : List Bool} {k : ℕ} (h : addN W hbits ≤ k) :
    addFlag W hbits k = Shift.gStop := by simp [addFlag, Nat.not_lt.mpr h]

/-! ## The state predicate of the addition loop -/

/-- The two bit streams at step `k`: `W` from position `k` on `aW`, `hbits` from position `k` on
`aB` (followed by the `iend` terminator). -/
def strP (W hbits : List Bool) (Ws Bs : List Glyph) (k : ℕ) (s : State) : Prop :=
  s.stk aW = (W.drop k).map Glyph.bit ++ Shift.gmk aW :: Ws ∧
  s.stk aB = (hbits.drop k).map Glyph.bit ++ Glyph.iend :: Shift.gmk aB :: Bs

/-- The accumulators at step `k`: the `min b k` bits already pushed onto `aO`, the rest on `a2`,
and the counter `b - k`. -/
def accP (b : ℕ) (W hbits LO : List Bool) (Os A2s Cs : List Glyph) (k : ℕ) (s : State) : Prop :=
  s.stk aO = ((accF W hbits false k).take b).reverse.map Glyph.bit ++
      LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os ∧
  s.stk a2 = ((accF W hbits false k).drop b).reverse.map Glyph.bit ++ Shift.gmk a2 :: A2s ∧
  s.stk aCW = Unary (b - k) (Shift.gmk aCW :: Cs)

/-- All stacks other than `aW`, `aB`, `aO`, `a2`, `aCW` are untouched. -/
def frP (X : Stk → List Glyph) (s : State) : Prop :=
  ∀ j : Stk, j ≠ aW → j ≠ aB → j ≠ aO → j ≠ a2 → j ≠ aCW → s.stk j = X j

/-- Full invariant of the addition loop after `k` steps. -/
def addP (b : ℕ) (W hbits LO : List Bool) (X : Stk → List Glyph) (Ws Os Cs A2s Bs : List Glyph)
    (k : ℕ) (s : State) : Prop :=
  strP W hbits Ws Bs k s ∧ accP b W hbits LO Os A2s Cs k s ∧ frP X s ∧
    s.reg rKa = Glyph.bit (carryC W hbits false k) ∧ s.reg rLa = addFlag W hbits k

/-! ## The program -/

/-- One iteration, part 1: read the current window bit (if any) and the current digit bit (if any)
and compute the sum bit and the new carry. -/
def stepA : Cmd :=
  Work.Layout.seqs [
    .peek aW rWa,
    .ite rWa (Shift.gmk aW)
      (Work.Layout.seqs [.pop aB rHa, .set rZa (Glyph.bit false), stepAdd rHa rZa rKa rSa])
      (Work.Layout.seqs [.pop aW rWa, .peek aB rHa,
        .ite rHa Glyph.iend
          (Work.Layout.seqs [.set rZa (Glyph.bit false), stepAdd rWa rZa rKa rSa])
          (Work.Layout.seqs [.pop aB rHa, stepAdd rWa rHa rKa rSa])])]

/-- One iteration, part 2: push the sum bit onto `aO` (consuming one counter token) if the
counter is still positive, else onto `a2`. -/
def routeA : Cmd :=
  Work.Layout.seqs [
    .peek aCW rTa,
    .ite rTa Work.IntLib.gTok
      (Work.Layout.seqs [.push aO rSa, .pop aCW rTa])
      (.push a2 rSa)]

/-- One iteration, part 3: recompute the loop flag. -/
def flagA : Cmd :=
  Work.Layout.seqs [
    .peek aW rTa,
    .ite rTa (Shift.gmk aW)
      (Work.Layout.seqs [.peek aB rTa,
        .ite rTa Glyph.iend (.set rLa Shift.gStop) (.set rLa Shift.gGo)])
      (.set rLa Shift.gGo)]

/-- The body of the addition loop. -/
def bodyA : Cmd := Work.Layout.seqs [stepA, routeA, flagA]

/-- The initial flag computation of the addition loop. -/
def initA : Cmd :=
  Work.Layout.seqs [
    .peek aW rTa,
    .ite rTa (Shift.gmk aW)
      (Work.Layout.seqs [.peek aB rTa,
        .ite rTa Glyph.iend (.set rLa Shift.gStop) (.set rLa Shift.gGo)])
      (.set rLa Shift.gGo)]

/-- The final carry of the addition: push it onto `aO` (consuming a counter token) if the counter
is still positive, else onto `a2`. -/
def carryA : Cmd :=
  Work.Layout.seqs [
    .ite rKa (Glyph.bit true)
      (Work.Layout.seqs [
        .peek aCW rTa,
        .ite rTa Work.IntLib.gTok
          (Work.Layout.seqs [.set rZa (Glyph.bit true), .push aO rZa, .pop aCW rTa])
          (.seq (.set rZa (Glyph.bit true)) (.push a2 rZa))])
      .skip]

/-- Initial flag computation of the padding loop. -/
def padInit : Cmd :=
  Work.Layout.seqs [
    .peek aCW rTa,
    .ite rTa Work.IntLib.gTok (.set rLa Shift.gGo) (.set rLa Shift.gStop)]

/-- Body of the padding loop: push a `false` bit onto `aO` and consume one counter token. -/
def padBody : Cmd :=
  Work.Layout.seqs [
    .set rZa (Glyph.bit false), .push aO rZa, .pop aCW rTa,
    .peek aCW rTa,
    .ite rTa Work.IntLib.gTok (.set rLa Shift.gGo) (.set rLa Shift.gStop)]

/-- The padding loop: push `b - |addAll|` zero bits onto `aO`, emptying the counter. -/
def padA : Cmd := Work.Layout.seqs [padInit, .loop rLa Shift.gGo padBody]

/-- The complete `evCarryAdd` word. -/
def evCarryProg : Cmd :=
  Work.Layout.seqs [
    Shift.drain aA aB (Shift.gmk aA) rGa rLa,
    .pop aB rGa,
    .set rKa (Glyph.bit false),
    initA,
    .loop rLa Shift.gGo bodyA,
    carryA,
    .pop aB rGa,
    padA,
    Shift.drain a2 aW (Shift.gmk a2) rGa rLa]

/-- Low `b` bits of a bit string, padded with `false` to length exactly `b`. -/
def lowBits (b : ℕ) (xs : List Bool) : List Bool :=
  xs.take b ++ List.replicate (b - xs.length) false

theorem lowBits_length (b : ℕ) (xs : List Bool) : (lowBits b xs).length = b := by
  rw [lowBits, List.length_append, List.length_take, List.length_replicate]
  by_cases h : xs.length ≤ b
  · rw [Nat.min_eq_right h]; omega
  · rw [Nat.min_eq_left (by omega)]; omega

/-! ## Elementary list identities -/

theorem drop_map_cons (xs : List Bool) {k : ℕ} (h : k < xs.length) :
    (xs.drop k).map Glyph.bit = Glyph.bit (xs.getD k false) :: (xs.drop (k + 1)).map Glyph.bit := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem xs false h, List.map_cons]

/-- `take` of a `++ [x]` when `x` is still inside the prefix. -/
theorem take_append_singleton_of_lt {α : Type} (xs : List α) (x : α) {b : ℕ}
    (h : xs.length < b) : (xs ++ [x]).take b = xs.take b ++ [x] := by
  have hlen : (xs ++ [x]).length ≤ b := by simp; omega
  have hx : xs.length ≤ b := by omega
  rw [List.take_of_length_le hlen, List.take_of_length_le hx]

/-- `take` of a `++ [x]` when `x` is beyond the prefix. -/
theorem take_append_singleton_of_le {α : Type} (xs : List α) (x : α) {b : ℕ}
    (h : b ≤ xs.length) : (xs ++ [x]).take b = xs.take b := by
  rw [List.take_append, Nat.sub_eq_zero_of_le h, List.take_zero, List.append_nil]

/-- `drop` of a `++ [x]` when `x` is beyond the prefix. -/
theorem drop_append_singleton_of_le {α : Type} (xs : List α) (x : α) {b : ℕ}
    (h : b ≤ xs.length) : (xs ++ [x]).drop b = xs.drop b ++ [x] := by
  rw [List.drop_append, Nat.sub_eq_zero_of_le h, List.drop_zero]

/-- `drop` of a `++ [x]` when `x` is still inside the prefix. -/
theorem drop_append_singleton_of_lt {α : Type} (xs : List α) (x : α) {b : ℕ}
    (h : xs.length < b) : (xs ++ [x]).drop b = [] := by
  apply List.drop_eq_nil_of_le
  simp; omega

theorem getD_eq_false_of_le {xs : List Bool} {k : ℕ} (h : xs.length ≤ k) :
    xs.getD k false = false := List.getD_eq_default xs false h

/-! ## `ofBits` identities -/

theorem ofBits_append_singleton (xs : List Bool) (b : Bool) :
    ofBits (xs ++ [b]) = ofBits xs + 2 ^ xs.length * b.toNat := by
  rw [ofBits_append]
  simp [ofBits]

theorem ofBits_replicate_false (n : ℕ) : ofBits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ofBits_cons, ih]

theorem ofBits_take_mod (xs : List Bool) (b : ℕ) : ofBits (xs.take b) = ofBits xs % 2 ^ b := by
  have h := ofBits_take_drop xs b
  have hlt : ofBits (xs.take b) < 2 ^ b := by
    refine lt_of_lt_of_le (ofBits_lt_two_pow _) ?_
    exact Nat.pow_le_pow_right (by norm_num) (by simp)
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem ofBits_drop_div (xs : List Bool) (b : ℕ) : ofBits (xs.drop b) = ofBits xs / 2 ^ b := by
  have h := ofBits_take_drop xs b
  have hpos : 0 < 2 ^ b := pow_pos (by norm_num) b
  have hmod : ofBits (xs.take b) / 2 ^ b = 0 := by
    rw [ofBits_take_mod]
    exact Nat.div_eq_of_lt (Nat.mod_lt _ hpos)
  rw [h, Nat.add_mul_div_left _ _ hpos, hmod, Nat.zero_add]

theorem ofBits_lowBits (b : ℕ) (xs : List Bool) :
    ofBits (lowBits b xs) = ofBits xs % 2 ^ b := by
  rw [lowBits, ofBits_append, ofBits_replicate_false, Nat.mul_zero, Nat.add_zero, ofBits_take_mod]

theorem ofBits_drop_eq (xs : List Bool) (k : ℕ) :
    ofBits (xs.drop k) = (xs.getD k false).toNat + 2 * ofBits (xs.drop (k + 1)) := by
  by_cases hk : k < xs.length
  · rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem xs false hk, ofBits_cons]
  · have h1 : xs.drop k = [] := List.drop_eq_nil_of_le (by omega)
    have h2 : xs.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have h3 : xs.getD k false = false := List.getD_eq_default xs false (by omega)
    rw [h1, h2, h3]
    rfl

theorem ofBits_eq_zero_of_drop_eq_nil {xs : List Bool} {k : ℕ} (h : xs.drop k = []) :
    ofBits (xs.drop k) = 0 := by rw [h]; rfl

end EvC
end Work.IntLib
