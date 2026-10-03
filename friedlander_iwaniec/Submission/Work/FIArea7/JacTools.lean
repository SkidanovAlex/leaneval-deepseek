/-
# `Submission.Work.FIArea7.JacTools` — tools for the Jacobi–Kubota multiplier rule

Elementary facts about the Jacobi symbol `jacobiSym` and the Hilbert symbol at `∞`, used in the
proof of *FI* Lemma 20.1 ((20.3)/(20.4), the Jacobi–Kubota multiplier rule):

* the "indicator of negativity" `negI` and the resulting rewriting of `HilbertInf` (17.7),
  together with the multiplicativity rule (20.8)/(20.9);
* quadratic reciprocity (17.6) for the Jacobi symbol with **integer numerator** and coprime odd
  arguments, in the sharp form `(x/|y|)(y/|x|) = (-1)^{((x-1)/2)((y-1)/2)}(x,y)_∞`;
* the supplementary laws `(-1/·)`, `(2/·)` (20.7) in terms of `Int.negOnePow`;
* "peeling a power of `2`" off the numerator of a Jacobi symbol, via `χ₈`.
-/
import Mathlib
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The indicator of negativity and the Hilbert symbol at `∞` -/

/-- The indicator of `x < 0`, as an integer. -/
def negI (x : ℤ) : ℤ := if x < 0 then 1 else 0

lemma negI_zero : negI 0 = 0 := by unfold negI; simp

lemma negI_sq (x : ℤ) : negI x * negI x = negI x := by
  unfold negI; split <;> ring

lemma negI_nonneg (x : ℤ) : 0 ≤ negI x := by unfold negI; split <;> norm_num

lemma negI_neg {y : ℤ} (hy : y ≠ 0) : negI (-y) = 1 - negI y := by
  unfold negI
  by_cases h : y < 0
  · have h2 : ¬ (-y < 0) := by omega
    rw [if_pos h, if_neg h2]; ring
  · have h2 : -y < 0 := by omega
    rw [if_neg h, if_pos h2]; ring

lemma negI_mul {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    negI (x * y) = negI x + negI y - 2 * negI x * negI y := by
  rcases lt_trichotomy x 0 with hx' | hx' | hx'
  · rcases lt_trichotomy y 0 with hy' | hy' | hy'
    · have h : ¬ (x * y < 0) := by nlinarith
      rw [negI, if_neg h, negI, if_pos hx', negI, if_pos hy']; ring
    · exact absurd hy' hy
    · have h : x * y < 0 := mul_neg_of_neg_of_pos hx' hy'
      have hy'' : ¬ y < 0 := by omega
      rw [negI, if_pos h, negI, if_pos hx', negI, if_neg hy'']; ring
  · exact absurd hx' hx
  · rcases lt_trichotomy y 0 with hy' | hy' | hy'
    · have h : x * y < 0 := mul_neg_of_pos_of_neg hx' hy'
      have hx'' : ¬ x < 0 := by omega
      rw [negI, if_pos h, negI, if_neg hx'', negI, if_pos hy']; ring
    · exact absurd hy' hy
    · have h : ¬ (x * y < 0) := by nlinarith
      have hx'' : ¬ x < 0 := by omega
      have hy'' : ¬ y < 0 := by omega
      rw [negI, if_neg h, negI, if_neg hx'', negI, if_neg hy'']; ring

/-- **(17.7)** the Hilbert symbol at `∞`, in terms of the negativity indicators. -/
lemma hilbertInf_eq_negI (x y : ℤ) : HilbertInf x y = 1 - 2 * negI x * negI y := by
  unfold HilbertInf negI
  by_cases h : x < 0 ∧ y < 0
  · rw [if_pos h, if_pos h.1, if_pos h.2]; ring
  · rw [if_neg h]
    rcases not_and_or.mp h with h | h
    · rw [if_neg h]; ring
    · rw [if_neg h]; ring

lemma key_ring (a b c : ℤ) (ha : a * a = a) :
    1 - 2 * a * (b + c - 2 * b * c) = (1 - 2 * a * b) * (1 - 2 * a * c) := by
  linear_combination (-4 * b * c) * ha

/-- **(20.8)** symmetry. -/
lemma hilbertInf_comm (x y : ℤ) : HilbertInf x y = HilbertInf y x := by
  rw [hilbertInf_eq_negI, hilbertInf_eq_negI]; ring

/-- **(20.9)** multiplicativity in the second argument. -/
lemma hilbertInf_mul_right (x y z : ℤ) (hy : y ≠ 0) (hz : z ≠ 0) :
    HilbertInf x (y * z) = HilbertInf x y * HilbertInf x z := by
  rw [hilbertInf_eq_negI, hilbertInf_eq_negI, hilbertInf_eq_negI, negI_mul hy hz]
  exact key_ring (negI x) (negI y) (negI z) (negI_sq x)

/-- **(20.9)** multiplicativity in the first argument. -/
lemma hilbertInf_mul_left (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    HilbertInf (x * y) z = HilbertInf x z * HilbertInf y z := by
  rw [hilbertInf_comm (x * y) z, hilbertInf_comm x z, hilbertInf_comm y z]
  exact hilbertInf_mul_right z x y hx hy

/-- **(20.10)** `(x,-y)_∞ = (x,y)_∞ \operatorname{sign} x`, with `sign x` written as
`1 - 2·[x<0]`. -/
lemma hilbertInf_neg_right (x y : ℤ) (hy : y ≠ 0) :
    HilbertInf x (-y) = HilbertInf x y * (1 - 2 * negI x) := by
  rw [hilbertInf_eq_negI, hilbertInf_eq_negI, negI_neg hy]
  linear_combination (-4 * negI y) * (negI_sq x)

/-! ## 2. `χ₄`, `χ₈` versus powers of `-1` -/

/-- `χ₄` of an odd integer is `(-1)^{(n-1)/2}`. -/
lemma chi4_int_eq_negOnePow {n : ℤ} (hn : Odd n) :
    ZMod.χ₄ (n : ZMod 4) = ((Int.negOnePow ((n - 1) / 2) : ℤˣ) : ℤ) := by
  have hn2 : n % 2 = 1 := Int.odd_iff.mp hn
  have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  have key : ∀ k : ℤ, ((Int.negOnePow (2 * k) : ℤˣ) : ℤ) = 1 ∧
      ((Int.negOnePow (2 * k + 1) : ℤˣ) : ℤ) = -1 := by
    intro k
    constructor
    · rw [Int.negOnePow_two_mul]; rfl
    · rw [Int.negOnePow_two_mul_add_one]; rfl
  rw [ZMod.χ₄_int_eq_if_mod_four, if_neg (by omega)]
  rcases h4 with h | h
  · rw [if_pos h]
    obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
    have hd : (n - 1) / 2 = 2 * k := by omega
    rw [hd]; exact (key k).1.symm
  · rw [if_neg (by omega : ¬ n % 4 = 1)]
    obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
    have hd : (n - 1) / 2 = 2 * k + 1 := by omega
    rw [hd]; exact (key k).2.symm

/-- `χ₈` of an odd integer is `(-1)^{(n^2-1)/8}` (*FI* (20.7)). -/
lemma chi8_int_eq_negOnePow {n : ℤ} (hn : Odd n) :
    ZMod.χ₈ (n : ZMod 8) = ((Int.negOnePow ((n ^ 2 - 1) / 8) : ℤˣ) : ℤ) := by
  have hn2 : n % 2 = 1 := Int.odd_iff.mp hn
  have h8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  have key : ∀ k : ℤ, ((Int.negOnePow (2 * k) : ℤˣ) : ℤ) = 1 ∧
      ((Int.negOnePow (2 * k + 1) : ℤˣ) : ℤ) = -1 := by
    intro k
    constructor
    · rw [Int.negOnePow_two_mul]; rfl
    · rw [Int.negOnePow_two_mul_add_one]; rfl
  rw [ZMod.χ₈_int_eq_if_mod_eight, if_neg (by omega)]
  rcases h8 with h | h | h | h
  · rw [if_pos (by omega : n % 8 = 1 ∨ n % 8 = 7)]
    obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + 1 := ⟨n / 8, by omega⟩
    have hd : (n ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + k) := by
      have e : n ^ 2 - 1 = 8 * (2 * (4 * k ^ 2 + k)) := by rw [hk]; ring
      rw [e, Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]
    rw [hd]; exact (key _).1.symm
  · rw [if_neg (by omega : ¬ (n % 8 = 1 ∨ n % 8 = 7))]
    obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + 3 := ⟨n / 8, by omega⟩
    have hd : (n ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + 3 * k) + 1 := by
      have e : n ^ 2 - 1 = 8 * (2 * (4 * k ^ 2 + 3 * k) + 1) := by rw [hk]; ring
      rw [e, Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]
    rw [hd]; exact (key _).2.symm
  · rw [if_neg (by omega : ¬ (n % 8 = 1 ∨ n % 8 = 7))]
    obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
    have hd : (n ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + 5 * k + 1) + 1 := by
      have e : n ^ 2 - 1 = 8 * (2 * (4 * k ^ 2 + 5 * k + 1) + 1) := by rw [hk]; ring
      rw [e, Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]
    rw [hd]; exact (key _).2.symm
  · rw [if_pos (by omega : n % 8 = 1 ∨ n % 8 = 7)]
    obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + 7 := ⟨n / 8, by omega⟩
    have hd : (n ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + 7 * k + 3) := by
      have e : n ^ 2 - 1 = 8 * (2 * (4 * k ^ 2 + 7 * k + 3)) := by rw [hk]; ring
      rw [e, Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]
    rw [hd]; exact (key _).1.symm

/-- Peeling a power of `2` out of the numerator of a Jacobi symbol. -/
theorem jacobiSym_two_pow_mul (n : ℕ) (hn : Odd n) (x : ℤ) (k : ℕ) :
    jacobiSym ((2 : ℤ) ^ k * x) n = (ZMod.χ₈ (n : ZMod 8)) ^ k * jacobiSym x n := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have h : (2 : ℤ) ^ (k + 1) * x = (2 : ℤ) ^ k * (2 * x) := by ring
    rw [h, ih (2 * x), jacobiSym.mul_left, jacobiSym.at_two hn, pow_succ]
    ring

/-! ## 3. Quadratic reciprocity with integer numerator -/

private lemma odd_two_mul_add_one (n : ℕ) : Odd (2 * n + 1) := ⟨n, rfl⟩

theorem jacobiSym_recip_int {x y : ℤ} (hx : Odd x) (hy : Odd y) (hxy : IsCoprime x y) :
    jacobiSym x y.natAbs * jacobiSym y x.natAbs
      = ((Int.negOnePow (((x - 1) / 2) * ((y - 1) / 2)) : ℤˣ) : ℤ)
        * HilbertInf x y := by
  obtain ⟨X, hX⟩ : ∃ X : ℕ, x.natAbs = 2 * X + 1 := hx.natAbs
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, y.natAbs = 2 * Y + 1 := hy.natAbs
  have hcop : x.natAbs.gcd y.natAbs = 1 := by
    rw [← Int.gcd_eq_natAbs]; exact Int.isCoprime_iff_gcd_eq_one.mp hxy
  have hgcd : ((2 * (Y : ℤ) + 1)).gcd (2 * X + 1) = 1 := by
    rw [show (2 * (Y : ℤ) + 1) = ((2 * Y + 1 : ℕ) : ℤ) by push_cast; ring,
        show (2 * (X : ℤ) + 1) = ((2 * X + 1 : ℕ) : ℤ) by push_cast; ring,
        Int.gcd_natCast_natCast, Nat.gcd_comm, ← hX, ← hY]
    exact hcop
  have hdivX : (2 * X + 1) / 2 = X := by omega
  have hdivY : (2 * Y + 1) / 2 = Y := by omega
  have hrec : jacobiSym ((2 * X + 1 : ℕ) : ℤ) (2 * Y + 1)
      = (-1 : ℤ) ^ (X * Y) * jacobiSym ((2 * Y + 1 : ℕ) : ℤ) (2 * X + 1) := by
    have h := jacobiSym.quadratic_reciprocity (a := 2 * X + 1) (b := 2 * Y + 1)
      (odd_two_mul_add_one X) (odd_two_mul_add_one Y)
    rw [hdivX, hdivY] at h
    exact h
  have hsq : jacobiSym ((2 * Y + 1 : ℕ) : ℤ) (2 * X + 1)
      * jacobiSym ((2 * Y + 1 : ℕ) : ℤ) (2 * X + 1) = 1 := by
    have h := jacobiSym.sq_one hgcd
    rw [pow_two] at h; exact h
  -- the product of the two "positive" symbols
  have hkey : jacobiSym ((2 * X + 1 : ℕ) : ℤ) (2 * Y + 1)
      * jacobiSym ((2 * Y + 1 : ℕ) : ℤ) (2 * X + 1) = (-1 : ℤ) ^ (X * Y) := by
    rw [hrec, mul_assoc, hsq, mul_one]
  have hchiX : ZMod.χ₄ ((2 * X + 1 : ℕ) : ZMod 4) = (-1 : ℤ) ^ X := by
    rw [ZMod.χ₄_eq_neg_one_pow (n := 2 * X + 1) (by omega), hdivX]
  have hchiY : ZMod.χ₄ ((2 * Y + 1 : ℕ) : ZMod 4) = (-1 : ℤ) ^ Y := by
    rw [ZMod.χ₄_eq_neg_one_pow (n := 2 * Y + 1) (by omega), hdivY]
  have hhalfX : (((2 * X + 1 : ℕ) : ℤ) - 1) / 2 = (X : ℤ) := by
    push_cast
    rw [show (2 * (X : ℤ) + 1 - 1) = 2 * (X : ℤ) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  have hhalfY : (((2 * Y + 1 : ℕ) : ℤ) - 1) / 2 = (Y : ℤ) := by
    push_cast
    rw [show (2 * (Y : ℤ) + 1 - 1) = 2 * (Y : ℤ) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  have hmhalfX : (-(((2 * X + 1 : ℕ) : ℤ)) - 1) / 2 = -((X : ℤ) + 1) := by
    push_cast
    rw [show (-(2 * (X : ℤ) + 1) - 1) = 2 * (-((X : ℤ) + 1)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  have hmhalfY : (-(((2 * Y + 1 : ℕ) : ℤ)) - 1) / 2 = -((Y : ℤ) + 1) := by
    push_cast
    rw [show (-(2 * (Y : ℤ) + 1) - 1) = 2 * (-((Y : ℤ) + 1)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  have hHP : HilbertInf (((2 * X + 1 : ℕ) : ℤ)) (((2 * Y + 1 : ℕ) : ℤ)) = 1 := by
    unfold HilbertInf; rw [if_neg]; omega
  have hHXN : HilbertInf (-(((2 * X + 1 : ℕ) : ℤ))) (((2 * Y + 1 : ℕ) : ℤ)) = 1 := by
    unfold HilbertInf; rw [if_neg]; omega
  have hHYN : HilbertInf (((2 * X + 1 : ℕ) : ℤ)) (-(((2 * Y + 1 : ℕ) : ℤ))) = 1 := by
    unfold HilbertInf; rw [if_neg]; omega
  have hHNN : HilbertInf (-(((2 * X + 1 : ℕ) : ℤ))) (-(((2 * Y + 1 : ℕ) : ℤ))) = -1 := by
    unfold HilbertInf; rw [if_pos]; constructor <;> omega
  have hnegX : jacobiSym (-(((2 * X + 1 : ℕ) : ℤ))) (2 * Y + 1)
      = ZMod.χ₄ ((2 * Y + 1 : ℕ) : ZMod 4) * jacobiSym (((2 * X + 1 : ℕ) : ℤ)) (2 * Y + 1) :=
    jacobiSym.neg _ (odd_two_mul_add_one Y)
  have hnegY : jacobiSym (-(((2 * Y + 1 : ℕ) : ℤ))) (2 * X + 1)
      = ZMod.χ₄ ((2 * X + 1 : ℕ) : ZMod 4) * jacobiSym (((2 * Y + 1 : ℕ) : ℤ)) (2 * X + 1) :=
    jacobiSym.neg _ (odd_two_mul_add_one X)
  have hpow : ∀ a b : ℕ, (-1 : ℤ) ^ a * (-1 : ℤ) ^ b = (-1 : ℤ) ^ (a + b) := by
    intro a b; rw [← pow_add]
  have hsucc : ∀ a : ℕ, (-1 : ℤ) ^ (a + 1) = (-1 : ℤ) ^ a * (-1 : ℤ) := by
    intro a; rw [pow_succ]
  have htwo : ∀ a : ℕ, (-1 : ℤ) ^ (a + 2) = (-1 : ℤ) ^ a := by
    intro a; rw [pow_add]; norm_num
  rcases Int.natAbs_eq x with hx' | hx' <;> rcases Int.natAbs_eq y with hy' | hy'
  · have hx1 : x = ((2 * X + 1 : ℕ) : ℤ) := by rw [hx', hX]
    have hy1 : y = ((2 * Y + 1 : ℕ) : ℤ) := by rw [hy', hY]
    rw [hx1, hy1]
    simp only [Int.natAbs_natCast]
    rw [hhalfX, hhalfY, hHP, mul_one,
      show ((X : ℤ) * (Y : ℤ)) = ((X * Y : ℕ) : ℤ) by simp [Nat.cast_mul],
      Int.coe_negOnePow_natCast]
    exact hkey
  · have hx1 : x = ((2 * X + 1 : ℕ) : ℤ) := by rw [hx', hX]
    have hy1 : y = -((2 * Y + 1 : ℕ) : ℤ) := by rw [hy', hY]
    rw [hx1, hy1]
    simp only [Int.natAbs_natCast, Int.natAbs_neg]
    rw [hhalfX, hmhalfY, hHYN, mul_one,
      show ((X : ℤ) * (-((Y : ℤ) + 1))) = -((((X * (Y + 1) : ℕ)) : ℤ)) by push_cast; ring,
      Int.negOnePow_neg, Int.coe_negOnePow_natCast]
    calc jacobiSym (((2 * X + 1 : ℕ) : ℤ)) (2 * Y + 1)
            * jacobiSym (-(((2 * Y + 1 : ℕ) : ℤ))) (2 * X + 1)
        = jacobiSym (((2 * X + 1 : ℕ) : ℤ)) (2 * Y + 1)
            * (ZMod.χ₄ ((2 * X + 1 : ℕ) : ZMod 4)
              * jacobiSym (((2 * Y + 1 : ℕ) : ℤ)) (2 * X + 1)) := by rw [hnegY]
      _ = (jacobiSym (((2 * X + 1 : ℕ) : ℤ)) (2 * Y + 1)
            * jacobiSym (((2 * Y + 1 : ℕ) : ℤ)) (2 * X + 1))
            * ZMod.χ₄ ((2 * X + 1 : ℕ) : ZMod 4) := by ring
      _ = (-1 : ℤ) ^ (X * Y) * ZMod.χ₄ ((2 * X + 1 : ℕ) : ZMod 4) := by rw [hkey]
      _ = (-1 : ℤ) ^ (X * Y) * (-1 : ℤ) ^ X := by rw [hchiX]
      _ = (-1 : ℤ) ^ (X * (Y + 1)) := by
            rw [hpow, show X * (Y + 1) = X * Y + X by ring]
  · have hx1 : x = -((2 * X + 1 : ℕ) : ℤ) := by rw [hx', hX]
    have hy1 : y = ((2 * Y + 1 : ℕ) : ℤ) := by rw [hy', hY]
    rw [hx1, hy1]
    simp only [Int.natAbs_natCast, Int.natAbs_neg]
    rw [hmhalfX, hhalfY, hHXN, mul_one,
      show ((-((X : ℤ) + 1)) * (Y : ℤ)) = -((((X + 1) * Y : ℕ)) : ℤ) by push_cast; ring,
      Int.negOnePow_neg, Int.coe_negOnePow_natCast]
    calc jacobiSym (-(((2 * X + 1 : ℕ) : ℤ))) (2 * Y + 1)
            * jacobiSym (((2 * Y + 1 : ℕ) : ℤ)) (2 * X + 1)
        = (ZMod.χ₄ ((2 * Y + 1 : ℕ) : ZMod 4)
            * jacobiSym (((2 * X + 1 : ℕ) : ℤ)) (2 * Y + 1))
            * jacobiSym (((2 * Y + 1 : ℕ) : ℤ)) (2 * X + 1) := by rw [hnegX]
      _ = (jacobiSym (((2 * X + 1 : ℕ) : ℤ)) (2 * Y + 1)
            * jacobiSym (((2 * Y + 1 : ℕ) : ℤ)) (2 * X + 1))
            * ZMod.χ₄ ((2 * Y + 1 : ℕ) : ZMod 4) := by ring
      _ = (-1 : ℤ) ^ (X * Y) * ZMod.χ₄ ((2 * Y + 1 : ℕ) : ZMod 4) := by rw [hkey]
      _ = (-1 : ℤ) ^ (X * Y) * (-1 : ℤ) ^ Y := by rw [hchiY]
      _ = (-1 : ℤ) ^ ((X + 1) * Y) := by
            rw [hpow, show (X + 1) * Y = X * Y + Y by ring]
  · have hx1 : x = -((2 * X + 1 : ℕ) : ℤ) := by rw [hx', hX]
    have hy1 : y = -((2 * Y + 1 : ℕ) : ℤ) := by rw [hy', hY]
    rw [hx1, hy1]
    simp only [Int.natAbs_natCast, Int.natAbs_neg]
    rw [hmhalfX, hmhalfY, hHNN,
      show ((-((X : ℤ) + 1)) * (-((Y : ℤ) + 1))) = (((X + 1) * (Y + 1) : ℕ) : ℤ) by push_cast; ring,
      Int.coe_negOnePow_natCast, ← hsucc ((X + 1) * (Y + 1))]
    calc jacobiSym (-(((2 * X + 1 : ℕ) : ℤ))) (2 * Y + 1)
            * jacobiSym (-(((2 * Y + 1 : ℕ) : ℤ))) (2 * X + 1)
        = (ZMod.χ₄ ((2 * Y + 1 : ℕ) : ZMod 4)
            * jacobiSym (((2 * X + 1 : ℕ) : ℤ)) (2 * Y + 1))
            * (ZMod.χ₄ ((2 * X + 1 : ℕ) : ZMod 4)
              * jacobiSym (((2 * Y + 1 : ℕ) : ℤ)) (2 * X + 1)) := by rw [hnegX, hnegY]
      _ = (jacobiSym (((2 * X + 1 : ℕ) : ℤ)) (2 * Y + 1)
            * jacobiSym (((2 * Y + 1 : ℕ) : ℤ)) (2 * X + 1))
            * (ZMod.χ₄ ((2 * Y + 1 : ℕ) : ZMod 4)
              * ZMod.χ₄ ((2 * X + 1 : ℕ) : ZMod 4)) := by ring
      _ = (-1 : ℤ) ^ (X * Y) * ((-1 : ℤ) ^ X * (-1 : ℤ) ^ Y) := by
            rw [hkey, hchiX, hchiY]; ring
      _ = (-1 : ℤ) ^ (X * Y + (X + Y)) := by rw [hpow, hpow]
      _ = (-1 : ℤ) ^ ((X + 1) * (Y + 1) + 1) := by
            rw [show (X + 1) * (Y + 1) + 1 = X * Y + (X + Y) + 2 by ring, htwo]


/-! ## 4. The odd part of an integer -/

/-- The odd part of a nonzero integer, and its `2`-adic valuation. -/
lemma exists_two_pow_mul_odd (x : ℤ) (hx0 : x ≠ 0) :
    ∃ (k : ℕ) (y : ℤ), x = 2 ^ k * y ∧ Odd y := by
  suffices h : ∀ n : ℕ, ∀ x : ℤ, x.natAbs = n → x ≠ 0 → ∃ (k : ℕ) (y : ℤ),
      x = 2 ^ k * y ∧ Odd y by
    exact h x.natAbs x rfl hx0
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x hxn hx0
    by_cases hodd : Odd x
    · exact ⟨0, x, by simp, hodd⟩
    · have hev : Even x := Int.not_odd_iff_even.mp hodd
      obtain ⟨k, hk⟩ := hev
      have hx2 : x = 2 * (x / 2) := by
        have h2 : (2 : ℤ) ∣ x := ⟨k, by rw [hk]; ring⟩
        rw [Int.mul_ediv_cancel' h2]
      have hx2ne : x / 2 ≠ 0 := by
        intro h
        rw [h, mul_zero] at hx2
        exact hx0 hx2
      have hlt : (x / 2).natAbs < n := by
        rw [← hxn, hx2, Int.natAbs_mul, show (2 : ℤ).natAbs = 2 by norm_num]
        have hpos : 0 < (x / 2).natAbs := Int.natAbs_pos.mpr hx2ne
        omega
      obtain ⟨k', y, hky, hyodd⟩ := ih (x / 2).natAbs hlt (x / 2) rfl hx2ne
      refine ⟨k' + 1, y, ?_, hyodd⟩
      rw [hx2, hky, pow_succ]
      ring


/-! ## 5. Chi-values and reciprocity in solved form -/

lemma chi8_neg_one : ZMod.χ₈ (-1 : ZMod 8) = 1 := by decide

lemma chi8_natAbs (m : ℤ) :
    ZMod.χ₈ (m.natAbs : ZMod 8) = ZMod.χ₈ (m : ZMod 8) := by
  have hcast : ∀ n : ℕ, ((n : ZMod 8)) = ((n : ℤ) : ZMod 8) := fun n => by push_cast; ring
  by_cases h : 0 ≤ m
  · rw [hcast, Int.natAbs_of_nonneg h]
  · have h' : m ≤ 0 := by omega
    rw [show m.natAbs = (-m).natAbs by rw [Int.natAbs_neg], hcast,
      Int.natAbs_of_nonneg (by omega)]
    rw [show (((-m : ℤ)) : ZMod 8) = (-1 : ZMod 8) * (m : ZMod 8) by push_cast; ring,
      map_mul, chi8_neg_one, one_mul]

lemma jac_recip {x y : ℤ} (hx : Odd x) (hy : Odd y) (hcop : IsCoprime x y) :
    jacobiSym x y.natAbs
      = ((Int.negOnePow (((x - 1) / 2) * ((y - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf x y
        * jacobiSym y x.natAbs := by
  have hgcd : y.gcd (x.natAbs : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Nat.gcd_comm, ← Int.gcd_eq_natAbs]
    exact Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hsq : jacobiSym y x.natAbs * jacobiSym y x.natAbs = 1 := by
    have h := jacobiSym.sq_one hgcd
    rwa [pow_two] at h
  have h := jacobiSym_recip_int hx hy hcop
  calc jacobiSym x y.natAbs = jacobiSym x y.natAbs * 1 := by ring
    _ = jacobiSym x y.natAbs * (jacobiSym y x.natAbs * jacobiSym y x.natAbs) := by rw [hsq]
    _ = (jacobiSym x y.natAbs * jacobiSym y x.natAbs) * jacobiSym y x.natAbs := by ring
    _ = (((Int.negOnePow (((x - 1) / 2) * ((y - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf x y)
          * jacobiSym y x.natAbs := by rw [h]
    _ = ((Int.negOnePow (((x - 1) / 2) * ((y - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf x y
          * jacobiSym y x.natAbs := by ring

lemma jacobiSym_neg_one_eq (n : ℕ) (hn : Odd n) :
    jacobiSym (-1) n = ((Int.negOnePow (((n : ℤ) - 1) / 2) : ℤˣ) : ℤ) := by
  rw [jacobiSym.at_neg_one (Nat.odd_iff.mpr (Nat.odd_iff.mp hn))]
  exact chi4_int_eq_negOnePow (n := (n : ℤ)) (by exact_mod_cast hn)

end

end Work.FIArea7
