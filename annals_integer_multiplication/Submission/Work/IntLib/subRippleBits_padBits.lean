import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.Basic

/-!
# The pure ripple-subtraction identity behind `subBitProg`

`subRippleBits xs ys c` is the list-level function computed by the raw procedure `subBitProg`
(`Submission/Work/IntLib/divRaw.lean`): it ripples through the two (equal length) bit lists
least significant first, returning the final borrow and the result bits.

The main statement of this file is the specification of `subRippleBits` on the `padBits`
expansions of two naturals `x, y < 2^L`:

`subRippleBits (padBits x L) (padBits y L) false = (decide (y > x), padBits ((x + 2^L - y) % 2^L) L)`

i.e. the result bits are the low `L` bits of `x - y` and the final borrow is the underflow
flag.  Everything is proved from the general invariant `SubRipple.subRippleBits_spec`, which
describes `subRippleBits` on *any* pair of equal-length bit lists through `ofBits`:

`ofBits r + ofBits ys + c.toNat = ofBits xs + 2^xs.length * (final borrow).toNat`

(equivalently `xs - ys - c = ofBits r - 2^length * borrow`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

/-! Helper facts for the ripple-subtraction specification, kept in their own namespace so
that they do not collide with the `padBits` API developed elsewhere in `Submission/Work/IntLib`. -/
namespace SubRipple

theorem pair_fst {α β : Type*} (a : α) (b : β) : (a, b).1 = a := rfl
theorem pair_snd {α β : Type*} (a : α) (b : β) : (a, b).2 = b := rfl

/-- The arithmetic content of one ripple step: the bit `subBitVal a b c` and the borrow
`subBorrow a b c` are related to the input bits by `a + 2·borrow = b + c + bit`. -/
theorem borrow_key (a b c : Bool) :
    a.toNat + 2 * (subBorrow a b c).toNat = b.toNat + c.toNat + (subBitVal a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-- The borrow produced by one ripple step is exactly the comparison `B + c' > A`, where the
carry is propagated into the high part. -/
theorem borrow_iff (A B : ℕ) (a b c : Bool) :
    (b.toNat + 2 * B + c.toNat > a.toNat + 2 * A) ↔ (B + (subBorrow a b c).toNat > A) := by
  cases a <;> cases b <;> cases c <;> simp [subBorrow] <;> omega

/-- `ofBits` of `List.ofFn` is `Nat.ofBits`. -/
theorem ofBits_ofFn : ∀ {n : ℕ} (f : Fin n → Bool), ofBits (List.ofFn f) = Nat.ofBits f
  | 0, f => by simp [List.ofFn_zero, ofBits]
  | n + 1, f => by
    have hX : ofBits (List.ofFn fun i => f i.succ) = Nat.ofBits (f ∘ Fin.succ) :=
      ofBits_ofFn (f ∘ Fin.succ)
    rw [List.ofFn_succ, ofBits_cons, Nat.ofBits_succ, hX]
    omega

/-- `padBits n L` is `List.ofFn` of the first `L` bits of `n`. -/
theorem padBits_eq_ofFn (n L : ℕ) :
    padBits n L = List.ofFn (fun i : Fin L => n.testBit i) := by
  simp only [padBits, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map,
    Function.comp_def]

/-- `ofBits` reads back `n % 2^L` from the low `L` bits of `n`. -/
theorem ofBits_padBits (n L : ℕ) : ofBits (padBits n L) = n % 2 ^ L := by
  rw [padBits_eq_ofFn, ofBits_ofFn, Nat.ofBits_testBit]

/-- `ofBits` is injective on bit lists of equal length. -/
theorem ofBits_inj {l m : List Bool} (h : l.length = m.length) (hv : ofBits l = ofBits m) :
    l = m := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => rfl
    | cons b bs =>
      simp only [List.length_nil, List.length_cons] at h
      exact (Nat.succ_ne_zero bs.length h.symm).elim
  | cons b bs ih =>
    cases m with
    | nil =>
      simp only [List.length_nil, List.length_cons] at h
      exact (Nat.succ_ne_zero bs.length h).elim
    | cons b' bs' =>
      have hmod : b.toNat % 2 = b'.toNat % 2 := by
        have h2 := congrArg (fun t => t % 2) hv
        simpa only [ofBits_cons, Nat.add_mul_mod_self_left] using h2
      have hb : b = b' := by
        cases b <;> cases b' <;> simp_all
      have hbs : ofBits bs = ofBits bs' := by
        rw [ofBits_cons, ofBits_cons, hb] at hv
        omega
      have hlen : bs.length = bs'.length := by
        simp only [List.length_cons] at h
        omega
      rw [hb]
      exact congrArg (List.cons b') (ih hlen hbs)

/-- **Specification of the ripple subtraction.**  For equal-length bit lists `xs`, `ys` of
length `k` and an incoming borrow `c`, the ripple subtraction returns the borrow
`decide (ofBits ys + c > ofBits xs)` and a bit list `r` of length `k` with

`ofBits r + ofBits ys + c.toNat = ofBits xs + 2^k · (borrow).toNat`,   i.e. `xs - ys - c` is
`ofBits r` up to the outgoing borrow. -/
theorem subRippleBits_spec (k : ℕ) (xs ys : List Bool) (c : Bool)
    (hx : xs.length = k) (hy : ys.length = k) :
    (subRippleBits xs ys c).1 = decide (ofBits ys + c.toNat > ofBits xs) ∧
    (subRippleBits xs ys c).2.length = k ∧
    ofBits (subRippleBits xs ys c).2 + ofBits ys + c.toNat
      = ofBits xs + 2 ^ k * (subRippleBits xs ys c).1.toNat := by
  induction k generalizing xs ys c with
  | zero =>
    have hxs : xs = [] := List.length_eq_zero_iff.mp hx
    have hys : ys = [] := List.length_eq_zero_iff.mp hy
    rw [hxs, hys, subRippleBits]
    refine ⟨?_, ?_, ?_⟩
    · cases c <;> rfl
    · rfl
    · simp [ofBits]
  | succ k ih =>
    cases xs with
    | nil =>
      simp only [List.length_nil] at hx
      exact (Nat.succ_ne_zero k hx.symm).elim
    | cons a as =>
      cases ys with
      | nil =>
        simp only [List.length_nil] at hy
        exact (Nat.succ_ne_zero k hy.symm).elim
      | cons b bs =>
        have hx' : as.length = k := by
          simp only [List.length_cons] at hx
          omega
        have hy' : bs.length = k := by
          simp only [List.length_cons] at hy
          omega
        obtain ⟨ih1, ih2, ih3⟩ := ih as bs (subBorrow a b c) hx' hy'
        rw [subRippleBits]
        simp only [pair_fst, pair_snd]
        refine ⟨?_, ?_, ?_⟩
        · rw [ih1, ofBits_cons]
          rw [decide_eq_decide]
          exact (borrow_iff (ofBits as) (ofBits bs) a b c).symm
        · simp only [List.length_cons, ih2]
        · simp only [ofBits_cons]
          have hIH2 : 2 * ofBits (subRippleBits as bs (subBorrow a b c)).2
                + 2 * ofBits bs + 2 * (subBorrow a b c).toNat
              = 2 * ofBits as
                + 2 ^ (k + 1) * (subRippleBits as bs (subBorrow a b c)).1.toNat := by
            rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc]
            omega
          rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc] at hIH2
          have hkey := borrow_key a b c
          rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc]
          omega

end SubRipple

theorem subRippleBits_padBits (x y L : ℕ) (hx : x < 2 ^ L) (hy : y < 2 ^ L) :
    Work.IntLib.subRippleBits (Work.IntLib.padBits x L) (Work.IntLib.padBits y L) false =
      (decide (y > x), Work.IntLib.padBits ((x + 2 ^ L - y) % 2 ^ L) L) := by
  have hlenx : (padBits x L).length = L := by simp [padBits]
  have hleny : (padBits y L).length = L := by simp [padBits]
  obtain ⟨h1, h2, h3⟩ :=
    SubRipple.subRippleBits_spec L (padBits x L) (padBits y L) false hlenx hleny
  simp only [SubRipple.ofBits_padBits, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    Bool.toNat_false, add_zero] at h1 h3
  refine Prod.ext ?_ ?_
  · exact h1
  · have hlen : (subRippleBits (padBits x L) (padBits y L) false).2.length
        = (padBits ((x + 2 ^ L - y) % 2 ^ L) L).length := by
      rw [h2]
      simp only [padBits, List.length_map, List.length_range]
    have hval : ofBits (subRippleBits (padBits x L) (padBits y L) false).2
        = ofBits (padBits ((x + 2 ^ L - y) % 2 ^ L) L) := by
      calc ofBits (subRippleBits (padBits x L) (padBits y L) false).2
          = (x + 2 ^ L - y) % 2 ^ L := by
            by_cases hyx : y > x
            · have h1t : (subRippleBits (padBits x L) (padBits y L) false).1 = true := by
                rw [h1]
                exact decide_eq_true hyx
              rw [h1t] at h3
              simp only [Bool.toNat_true, mul_one] at h3
              have hsub : ofBits (subRippleBits (padBits x L) (padBits y L) false).2
                  = x + 2 ^ L - y := by omega
              rw [hsub]
              exact (Nat.mod_eq_of_lt (by omega)).symm
            · have h1f : (subRippleBits (padBits x L) (padBits y L) false).1 = false := by
                rw [h1]
                exact decide_eq_false hyx
              rw [h1f] at h3
              simp only [Bool.toNat_false, mul_zero, add_zero] at h3
              have hsub : ofBits (subRippleBits (padBits x L) (padBits y L) false).2
                  = x - y := by omega
              have hmod : ((x - y) + 2 ^ L) % 2 ^ L = x - y := by
                have hstep : (x - y) + 2 ^ L = (x - y) + 2 ^ L * 1 := by simp only [mul_one]
                rw [hstep, Nat.add_mul_mod_self_left]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hsub, show x + 2 ^ L - y = (x - y) + 2 ^ L by omega]
              exact hmod.symm
        _ = ofBits (padBits ((x + 2 ^ L - y) % 2 ^ L) L) := by
            rw [SubRipple.ofBits_padBits]
            exact (Nat.mod_eq_of_lt (Nat.mod_lt _ (pow_pos (by norm_num) L))).symm
    exact SubRipple.ofBits_inj hlen hval

end Work.IntLib
