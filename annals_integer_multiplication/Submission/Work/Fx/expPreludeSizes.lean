import Mathlib
import Submission.Work.Fx.ExpDefs

/-!
# `Work.Fx.expPreludeSizes`

Size bounds for the values produced by the `expPrelude` word (`Work.Fx.expPrelude`): the inputs
`X, Y`, the scaled inputs `X·2^(d0 p)`, `Y·2^(d0 p)`, the working precision constants
`2^(wprec p)`, `d0 p`, `wprec p`, `wcnt p`, the precision `p` itself, and the list of `wcnt p` ones.

All bounds are `≤ 40·(p+1)`, and all follow from the single hypothesis `|X|, |Y| ≤ 32·2^p`
(obtained from the real square bounds in the statement) together with `p.size ≤ p`.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-! ## Elementary size helpers -/

/-- `isz` bound from a modulus bound: `|z| ≤ 2^k` gives `isz z ≤ k + 3`. -/
theorem expSz_isz_le_of_natAbs_le {z : ℤ} {k : ℕ} (h : z.natAbs ≤ 2 ^ k) : isz z ≤ k + 3 := by
  have h1 : z.natAbs < 2 ^ (k + 1) :=
    lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))
  have h2 : z.natAbs.size ≤ k + 1 := Nat.size_le.mpr h1
  simp only [isz]
  omega

/-- `isz` of a natural number: `isz (n : ℤ) ≤ n + 2`. -/
theorem expSz_isz_natCast_le (n : ℕ) : isz (n : ℤ) ≤ n + 2 := by
  have h : ((n : ℤ).natAbs) = n := Int.natAbs_natCast n
  simp only [isz, h]
  have h2 : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  omega

/-- The modulus bound `|X| ≤ 32·2^p` implied by the real square bound `(X:ℝ)^2 ≤ (32·2^p)^2`. -/
theorem expSz_abs_le_of_sq (p : ℕ) {X : ℤ} (hX : (X : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) :
    |(X : ℝ)| ≤ 32 * 2 ^ p := by
  have h := (sq_le_sq.mp hX)
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 32 * 2 ^ p)] at h

/-- Integer modulus bound: `|X| ≤ 32·2^p` gives `X.natAbs ≤ 32·2^p`. -/
theorem expSz_natAbs_le (p : ℕ) {X : ℤ} (h : |(X : ℝ)| ≤ 32 * 2 ^ p) :
    X.natAbs ≤ 32 * 2 ^ p := by
  have h2 : ((X.natAbs : ℕ) : ℝ) = |(X : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have h3 : ((X.natAbs : ℕ) : ℝ) ≤ ((32 * 2 ^ p : ℕ) : ℝ) := by
    rw [h2]
    push_cast
    exact h
  exact_mod_cast h3

/-- `|X| ≤ 32·2^p` gives `isz X ≤ p + 8`. -/
theorem expSz_isz_X_le (p : ℕ) {X : ℤ} (h : |(X : ℝ)| ≤ 32 * 2 ^ p) : isz X ≤ p + 8 := by
  have h2 : ((X.natAbs : ℕ) : ℝ) = |(X : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have h1 : X.natAbs < 2 ^ (p + 6) := by
    have h3 : ((X.natAbs : ℕ) : ℝ) < ((2 ^ (p + 6) : ℕ) : ℝ) := by
      rw [h2]; push_cast
      have h4 : (32 : ℝ) * 2 ^ p < 2 ^ (p + 6) := by
        rw [pow_add]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p]
      linarith
    exact_mod_cast h3
  have h4 : X.natAbs.size ≤ p + 6 := Nat.size_le.mpr h1
  simp only [isz]
  omega

/-- `|X| ≤ 32·2^p` gives `X.natAbs ≤ 2^(p+5)`. -/
theorem expSz_natAbs_le_pow (p : ℕ) {X : ℤ} (h : |(X : ℝ)| ≤ 32 * 2 ^ p) :
    X.natAbs ≤ 2 ^ (p + 5) := by
  have h1 : X.natAbs ≤ 32 * 2 ^ p := expSz_natAbs_le p h
  have h2 : (32 : ℕ) * 2 ^ p = 2 ^ (p + 5) := by
    rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_add, Nat.add_comm]
  rwa [h2] at h1

/-- `isz` of the shifted input `X·2^(d0 p)`. -/
theorem expSz_isz_shift (p : ℕ) {X : ℤ} (h : |(X : ℝ)| ≤ 32 * 2 ^ p) :
    isz (X * (2 : ℤ) ^ d0 p) ≤ p + 8 + d0 p := by
  have h5 : X.natAbs ≤ 2 ^ (p + 5) := expSz_natAbs_le_pow p h
  have h6 : (X * (2 : ℤ) ^ d0 p).natAbs ≤ 2 ^ (p + 5 + d0 p) := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    have h7 : ((2 : ℤ).natAbs) ^ d0 p = 2 ^ d0 p := by norm_num
    rw [h7]
    calc X.natAbs * 2 ^ d0 p ≤ 2 ^ (p + 5) * 2 ^ d0 p := Nat.mul_le_mul_right _ h5
      _ = 2 ^ (p + 5 + d0 p) := by rw [← pow_add]
  have := expSz_isz_le_of_natAbs_le h6
  omega

/-- `isz` of a power of two. -/
theorem expSz_isz_two_pow (k : ℕ) : isz ((2 : ℤ) ^ k) = k + 3 := by
  have h : ((2 : ℤ) ^ k).natAbs = 2 ^ k := by rw [Int.natAbs_pow]; norm_num
  rw [isz, h, Nat.size_pow]

/-! ## Sizes of `ofList` chains -/

theorem expSz_vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, Nat.add_assoc]

theorem expSz_ofList_cons (x : Val) (t : List Val) : ofList (x :: t) = Val.cons x (ofList t) := rfl

/-- The encoding size of a `cons`-chain of `n` equal values. -/
theorem expSz_vsz_ofList_replicate (n : ℕ) (v : Val) :
    vsz (ofList (List.replicate n v)) = n * (vsz v + 1) + 1 := by
  induction n with
  | zero => simp [ofList, vsz, Val.enc]
  | succ n ih =>
    rw [List.replicate_succ, expSz_ofList_cons, expSz_vsz_cons, ih]
    ring

theorem expSz_vsz_int_one : vsz (Val.int (1 : ℤ)) = 3 := by decide

theorem expSz_vsz_replicate_one (n : ℕ) :
    vsz (ofList (List.replicate n (Val.int (1 : ℤ)))) = 4 * n + 1 := by
  rw [expSz_vsz_ofList_replicate, expSz_vsz_int_one]
  ring

/-! ## The size bounds -/

theorem expPreludeSizes (p : ℕ) (hp : 100 ≤ p) (X Y : ℤ)
    (hX : (X : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) (hY : (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) :
    HvdH.isz X ≤ 40 * (p + 1) ∧ HvdH.isz Y ≤ 40 * (p + 1) ∧
    HvdH.isz (X * (2 : ℤ) ^ Work.Fx.d0 p) ≤ 40 * (p + 1) ∧
    HvdH.isz (Y * (2 : ℤ) ^ Work.Fx.d0 p) ≤ 40 * (p + 1) ∧
    HvdH.isz ((2 : ℤ) ^ Work.Fx.wprec p) ≤ 40 * (p + 1) ∧
    HvdH.isz ((Work.Fx.d0 p : ℕ) : ℤ) ≤ 40 * (p + 1) ∧
    HvdH.isz ((Work.Fx.wprec p : ℕ) : ℤ) ≤ 40 * (p + 1) ∧
    HvdH.isz ((Work.Fx.wcnt p : ℕ) : ℤ) ≤ 40 * (p + 1) ∧
    HvdH.isz ((p : ℕ) : ℤ) ≤ 40 * (p + 1) ∧
    HvdH.vsz (HvdH.ofList (List.replicate (Work.Fx.wcnt p) (HvdH.Val.int 1))) ≤ 40 * (p + 1) := by
  have hpsize : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
  have hX' : |(X : ℝ)| ≤ 32 * 2 ^ p := expSz_abs_le_of_sq p hX
  have hY' : |(Y : ℝ)| ≤ 32 * 2 ^ p := expSz_abs_le_of_sq p hY
  have h1 : isz X ≤ p + 8 := expSz_isz_X_le p hX'
  have h2 : isz Y ≤ p + 8 := expSz_isz_X_le p hY'
  have h3 : isz (X * (2 : ℤ) ^ d0 p) ≤ p + 8 + d0 p := expSz_isz_shift p hX'
  have h4 : isz (Y * (2 : ℤ) ^ d0 p) ≤ p + 8 + d0 p := expSz_isz_shift p hY'
  have h5 : isz ((2 : ℤ) ^ wprec p) = wprec p + 3 := expSz_isz_two_pow (wprec p)
  have h6 : isz ((d0 p : ℕ) : ℤ) ≤ d0 p + 2 := expSz_isz_natCast_le (d0 p)
  have h7 : isz ((wprec p : ℕ) : ℤ) ≤ wprec p + 2 := expSz_isz_natCast_le (wprec p)
  have h8 : isz ((wcnt p : ℕ) : ℤ) ≤ wcnt p + 2 := expSz_isz_natCast_le (wcnt p)
  have h9 : isz ((p : ℕ) : ℤ) ≤ p + 2 := expSz_isz_natCast_le p
  have h10 : vsz (ofList (List.replicate (wcnt p) (Val.int (1 : ℤ)))) = 4 * wcnt p + 1 :=
    expSz_vsz_replicate_one (wcnt p)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [wprec, d0, wcnt] at * <;> omega

end Work.Fx
