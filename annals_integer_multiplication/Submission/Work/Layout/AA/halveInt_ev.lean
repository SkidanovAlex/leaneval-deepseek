import Mathlib
import Submission.Work.Layout.AA.Defs
import Submission.Work.IntLib.encodeNatBridge

/-!
# `halveInt`: `Ev`-level specification

`Work.Layout.halveInt a rs rt` pops the two leading glyphs of the integer value on top of stack
`a` (the sign glyph and the *least significant* bit) and pushes the sign glyph back.  The encoding
of a natural number `k` is the sign `pos`, the bits of `k` least significant first, then `iend`; so
the value `k` becomes the value `k / 2`.

The arithmetical content is `Work.Layout.AA.encodeNat_map_cons`:
`(Computability.encodeNat k).map bit = bit k.bodd :: (Computability.encodeNat (k/2)).map bit`
for `k ≠ 0`, which in turn is the Mathlib fact `Nat.bits n = n.bodd :: (n/2).bits`.

The program is `pop a rs ;; pop a rt ;; push a rs`, so the cost is `3 ≤ 8`.
-/

set_option autoImplicit false

namespace Work.Layout.AA

open HvdH

/-- The bit list of a positive natural number starts with its parity bit. -/
theorem bits_eq_bodd_cons {n : ℕ} (hn : n ≠ 0) : n.bits = n.bodd :: (n / 2).bits := by
  conv_lhs => rw [← Nat.bit_bodd_div2 n]
  rw [Nat.bits_append_bit]
  · rw [Nat.div2_val]
  · intro h
    rw [Nat.div2_val] at h
    have h1 : n = 1 := by omega
    subst h1
    rfl

/-- The bit encoding of `k ≠ 0` splits as its parity bit, followed by the encoding of `k / 2`. -/
theorem encodeNat_map_cons {k : ℕ} (hk : k ≠ 0) :
    (Computability.encodeNat k).map Glyph.bit =
      Glyph.bit k.bodd :: (Computability.encodeNat (k / 2)).map Glyph.bit := by
  rw [Work.IntLib.encodeNat_eq_bits, bits_eq_bodd_cons hk]
  rfl

/-- **Main specification.**  `halveInt a rs rt` replaces the integer value `k` on top of stack `a`
by `k / 2` (for `k ≥ 2`, so that the value has a least significant bit to drop), leaves every other
stack unchanged, and costs at most `8` steps. -/
theorem halveInt_ev (main : HvdH.Cmd) (a : HvdH.Stk) (rs rt : HvdH.Reg) (hrst : rs ≠ rt)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (k : ℕ) (hk : 2 ≤ k)
    (A : List HvdH.Glyph) (ha : X a = (HvdH.Val.int k).enc ++ A) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.halveInt a rs rt) ⟨g, X⟩ s' n ∧ n ≤ 8 ∧
      s'.stk a = (HvdH.Val.int (k / 2)).enc ++ A ∧ (∀ j, j ≠ a → s'.stk j = X j) := by
  have hk0 : k ≠ 0 := by omega
  -- the two encodings, with the sign glyph exposed
  have henc : (HvdH.Val.int k).enc =
      HvdH.Glyph.pos ::
        ((Computability.encodeNat k).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend]) := by
    simp [HvdH.Val.enc]
  have hcast : (k : ℤ) / 2 = ((k / 2 : ℕ) : ℤ) := Int.ofNat_ediv_ofNat
  have henc2 : (HvdH.Val.int ((k / 2 : ℕ) : ℤ)).enc =
      HvdH.Glyph.pos ::
        ((Computability.encodeNat (k / 2)).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend]) := by
    show (if (((k / 2 : ℕ) : ℤ) < 0) then HvdH.Glyph.neg else HvdH.Glyph.pos) ::
      ((Computability.encodeNat (((k / 2 : ℕ) : ℤ)).natAbs).map HvdH.Glyph.bit ++
        [HvdH.Glyph.iend]) =
      HvdH.Glyph.pos ::
        ((Computability.encodeNat (k / 2)).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend])
    rw [if_neg (by omega), Int.natAbs_natCast]
  have hbits := encodeNat_map_cons hk0
  -- everything of the value of `a` except the sign and the least significant bit
  let Z : List HvdH.Glyph :=
    (Computability.encodeNat (k / 2)).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ A
  have hXa : X a = HvdH.Glyph.pos :: HvdH.Glyph.bit k.bodd :: Z := by
    rw [ha, henc, hbits]
    simp only [Z, List.cons_append, List.append_assoc]
  have hXa_head : (X a).headD HvdH.Glyph.eos = HvdH.Glyph.pos := by
    simp only [hXa, Work.Layout.headD_cons]
  have hXa_tail : (X a).tail = HvdH.Glyph.bit k.bodd :: Z := by
    simp only [hXa, Work.Layout.tail_cons]
  -- step 1: pop the sign glyph
  let g1 : HvdH.Reg → HvdH.Glyph := Function.update g rs HvdH.Glyph.pos
  let X1 : HvdH.Stk → List HvdH.Glyph := Function.update X a (X a).tail
  have hpop : Work.Layout.Ev main (.pop a rs) ⟨g, X⟩ ⟨g1, X1⟩ 1 := by
    have h := Work.Layout.ev_pop' main a rs g X
    rw [hXa_head] at h
    exact h
  have hX1a : X1 a = HvdH.Glyph.bit k.bodd :: Z := by
    show Function.update X a (X a).tail a = HvdH.Glyph.bit k.bodd :: Z
    rw [Work.Layout.stkFn_same X a (X a).tail, hXa_tail]
  -- step 2: pop the least significant bit
  let g2 : HvdH.Reg → HvdH.Glyph := Function.update g1 rt (HvdH.Glyph.bit k.bodd)
  let X2 : HvdH.Stk → List HvdH.Glyph := Function.update X1 a Z
  have hpop2 : Work.Layout.Ev main (.pop a rt) ⟨g1, X1⟩ ⟨g2, X2⟩ 1 := by
    have h := Work.Layout.ev_pop' main a rt g1 X1
    rw [hX1a] at h
    exact h
  -- step 3: push the sign glyph back
  have hg2rs : g2 rs = HvdH.Glyph.pos := by
    show Function.update g1 rt (HvdH.Glyph.bit k.bodd) rs = HvdH.Glyph.pos
    rw [Function.update_of_ne hrst]
    show Function.update g rs HvdH.Glyph.pos rs = HvdH.Glyph.pos
    exact Function.update_self rs HvdH.Glyph.pos g
  let X3 : HvdH.Stk → List HvdH.Glyph := Function.update X2 a (HvdH.Glyph.pos :: X2 a)
  have hpush3 : Work.Layout.Ev main (.push a rs) ⟨g2, X2⟩ ⟨g2, X3⟩ 1 := by
    have h := Work.Layout.ev_push' main a rs g2 X2
    rw [hg2rs] at h
    exact h
  have h23 : Work.Layout.Ev main (.seq (.pop a rt) (.push a rs)) ⟨g1, X1⟩ ⟨g2, X3⟩ 2 :=
    Work.Layout.Ev.seq' hpop2 hpush3 (by omega)
  have hEv : Work.Layout.Ev main (Work.Layout.halveInt a rs rt) ⟨g, X⟩ ⟨g2, X3⟩ 3 := by
    show Work.Layout.Ev main
      (.seq (.pop a rs) (.seq (.pop a rt) (.push a rs))) ⟨g, X⟩ ⟨g2, X3⟩ 3
    exact Work.Layout.Ev.seq' hpop h23 (by omega)
  refine ⟨⟨g2, X3⟩, 3, hEv, by omega, ?_, ?_⟩
  · have h3 : X3 a = HvdH.Glyph.pos :: X2 a :=
      Work.Layout.stkFn_same X2 a (HvdH.Glyph.pos :: X2 a)
    have h2a : X2 a = Z := Work.Layout.stkFn_same X1 a Z
    show X3 a = (HvdH.Val.int (k / 2)).enc ++ A
    rw [hcast, henc2, h3, h2a]
    simp only [Z, List.cons_append, List.append_assoc]
  · intro j hj
    calc X3 j = X2 j := Work.Layout.stkFn_ne X2 hj (HvdH.Glyph.pos :: X2 a)
      _ = X1 j := Work.Layout.stkFn_ne X1 hj Z
      _ = X j := Work.Layout.stkFn_ne X hj (X a).tail

end Work.Layout.AA
