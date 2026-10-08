import Mathlib.Algebra.Order.Star.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Fixed points of a Frobenius power in a finite field of characteristic two

`fixed_card_pow_two`: in the field `GF(2, 2n)` with `2^(2n)` elements (characteristic
two), the number of elements fixed by `x ↦ x^(2^n)` (the fixed field of the
`n`-th Frobenius power, a copy of `GF(2, 2n)`'s unique subfield with `2^n`
elements) is exactly `2 ^ n`.

The proof counts solutions of `x^(2^n) = x`:
* `0` is always a solution;
* a nonzero `x` solves it iff `x^(2^n - 1) = 1`, i.e. iff the corresponding unit
  of the (cyclic) unit group `Kˣ` has order dividing `2^n - 1`;
* in a cyclic group of order `N` the number of elements with `u^d = 1` is
  `gcd d N` (`IsCyclic.card_powMonoidHom_ker`);
* here `N = |Kˣ| = 2^(2n) - 1 = (2^n - 1)(2^n + 1)`, so
  `gcd (2^n - 1) N = 2^n - 1`, giving `1 + (2^n - 1) = 2^n` solutions in total.
-/

open scoped Classical

namespace Commons.FieldTheory.Finite

universe u

namespace fixedPowTwo

/-- `(2^n - 1)(2^n + 1) = 2^(2n) - 1` in `ℕ`. -/
lemma two_pow_sub_one_mul_two_pow_add_one (n : ℕ) :
    (2 ^ n - 1) * (2 ^ n + 1) = 2 ^ (2 * n) - 1 := by
  have h := Nat.pow_two_sub_pow_two (2 ^ n) 1
  have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  rw [h2, one_pow] at h
  calc
    (2 ^ n - 1) * (2 ^ n + 1) = (2 ^ n + 1) * (2 ^ n - 1) := by rw [mul_comm]
    _ = 2 ^ (2 * n) - 1 := h.symm

/-- `gcd (2^(2n) - 1) (2^n - 1) = 2^n - 1`. -/
lemma gcd_two_pow_sub (n : ℕ) : Nat.gcd (2 ^ (2 * n) - 1) (2 ^ n - 1) = 2 ^ n - 1 := by
  rw [Nat.gcd_comm]
  apply Nat.gcd_eq_left
  refine ⟨2 ^ n + 1, ?_⟩
  exact (two_pow_sub_one_mul_two_pow_add_one n).symm

/-- A nonzero element `x` of a field fixed by the `2^n`-power map has
`x^(2^n - 1) = 1`; conversely. -/
lemma pow_sub_one_eq_one_of_pow_eq_self {K : Type u} [Field K] {x : K} (n : ℕ)
    (hx : x ≠ 0) (h : x ^ (2 ^ n) = x) : x ^ (2 ^ n - 1) = 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) n)
  have hpow : x ^ (2 ^ n) = x * x ^ (2 ^ n - 1) := by
    calc
      x ^ (2 ^ n) = x ^ ((2 ^ n - 1) + 1) := by rw [Nat.sub_add_cancel h1]
      _ = x ^ (2 ^ n - 1) * x := by rw [pow_add, pow_one]
      _ = x * x ^ (2 ^ n - 1) := by rw [mul_comm]
  exact mul_left_cancel₀ hx (by simpa using hpow.symm.trans h)

lemma pow_eq_self_of_pow_sub_one_eq_one {K : Type u} [Field K] {x : K} (n : ℕ)
    (h : x ^ (2 ^ n - 1) = 1) : x ^ (2 ^ n) = x := by
  have h1 : 1 ≤ 2 ^ n := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) n)
  calc
    x ^ (2 ^ n) = x ^ ((2 ^ n - 1) + 1) := by rw [Nat.sub_add_cancel h1]
    _ = x ^ (2 ^ n - 1) * x := by rw [pow_add, pow_one]
    _ = 1 * x := by rw [h]
    _ = x := by rw [one_mul]

/-- Nonzero solutions of `x^(2^n) = x` correspond exactly to units `u` with
`u^(2^n - 1) = 1`. -/
noncomputable def nonzeroFixed_equiv_unitsPow {K : Type u} [Field K] (n : ℕ) :
    {x : K // x ≠ 0 ∧ x ^ (2 ^ n) = x} ≃ {u : Kˣ // u ^ (2 ^ n - 1) = 1} := by
  refine Equiv.ofBijective (fun x => ?_) ?_
  · refine ⟨Units.mk0 x.1 x.2.1, ?_⟩
    apply Units.ext
    have hx : x.1 ^ (2 ^ n - 1) = 1 :=
      pow_sub_one_eq_one_of_pow_eq_self (K := K) n x.2.1 x.2.2
    simpa using hx
  · constructor
    · intro a b h
      apply Subtype.ext
      have hv := congrArg (fun u : {u : Kˣ // u ^ (2 ^ n - 1) = 1} => (u.1 : K)) h
      simpa using hv
    · intro u
      refine ⟨⟨(u.1 : K), ?_⟩, ?_⟩
      · constructor
        · exact Units.ne_zero u.1
        · apply pow_eq_self_of_pow_sub_one_eq_one (K := K) n
          simpa using congrArg (fun v : Kˣ => (v : K)) u.2
      · apply Subtype.ext
        simp

/-- In a finite field, the number of units with `u^d = 1` is `gcd d |Kˣ|`. -/
lemma card_units_pow_eq_one_gcd {K : Type u} [Field K] [Finite K] (d : ℕ) :
    Nat.card {u : Kˣ // u ^ d = 1} = Nat.gcd (Nat.card Kˣ) d := by
  let φ : Kˣ →* Kˣ := powMonoidHom d
  calc
    Nat.card {u : Kˣ // u ^ d = 1} = Nat.card φ.ker := Nat.card_congr
      (Equiv.subtypeEquivRight (fun u => by
        simp [φ]))
    _ = Nat.gcd (Nat.card Kˣ) d := by
        simpa [φ] using (IsCyclic.card_powMonoidHom_ker (G := Kˣ) (d := d))

/-- In a finite field with `2^(2n)` elements (any characteristic), exactly
`2^n` elements satisfy `x^(2^n) = x`. -/
lemma card_fixed_pow_two_of_card {K : Type u} [Field K] [Finite K]
    (n : ℕ) (hcard : Nat.card K = 2 ^ (2 * n)) :
    Nat.card {x : K // x ^ (2 ^ n) = x} = 2 ^ n := by
  classical
  change ({x : K | x ^ (2 ^ n) = x} : Set K).ncard = 2 ^ n
  let p : K → Prop := fun x => x ^ (2 ^ n) = x
  have hp0 : p 0 := by
    dsimp [p]
    exact zero_pow (Nat.ne_of_gt (pow_pos (by decide : 0 < (2 : ℕ)) n))
  let Z : Set K := {x : K | x = 0}
  let B : Set K := {x : K | x ≠ 0 ∧ p x}
  have hAB : ({x : K | x ^ (2 ^ n) = x} : Set K) = Z ∪ B := by
    ext x
    constructor
    · intro hxA
      by_cases hx0 : x = 0
      · exact Or.inl (by simpa [Z] using hx0)
      · exact Or.inr ⟨hx0, by simpa [p] using hxA⟩
    · intro hx
      rcases hx with hxZ | hxB
      · have hx0 : x = 0 := by simpa [Z] using hxZ
        subst x
        exact hp0
      · exact hxB.2
  have hdisj : Disjoint Z B := by
    rw [Set.disjoint_left]
    intro x hxZ hxB
    exact hxB.1 (by simpa [Z] using hxZ)
  have hZsing : Z = ({0} : Set K) := by
    ext x
    simp [Z]
  have hZ : Z.ncard = 1 := by
    rw [hZsing]
    exact Set.ncard_singleton 0
  have hBtype : {x : K // x ∈ B} ≃ {x : K // x ≠ 0 ∧ p x} :=
    Equiv.subtypeEquivRight (fun x => by simp [B])
  have hB : B.ncard = Nat.card {x : K // x ≠ 0 ∧ p x} := by
    calc
      B.ncard = Nat.card {x : K // x ∈ B} := (Nat.card_coe_set_eq B).symm
      _ = Nat.card {x : K // x ≠ 0 ∧ p x} := Nat.card_congr hBtype
  have hBcard : Nat.card {x : K // x ≠ 0 ∧ p x} = 2 ^ n - 1 := by
    calc
      Nat.card {x : K // x ≠ 0 ∧ p x}
          = Nat.card {u : Kˣ // u ^ (2 ^ n - 1) = 1} := by
              simpa [p] using Nat.card_congr (nonzeroFixed_equiv_unitsPow (K := K) n)
      _ = Nat.gcd (Nat.card Kˣ) (2 ^ n - 1) := card_units_pow_eq_one_gcd (K := K) (d := 2 ^ n - 1)
      _ = 2 ^ n - 1 := by
          rw [Nat.card_units, hcard]
          exact gcd_two_pow_sub n
  calc
    ({x : K | x ^ (2 ^ n) = x} : Set K).ncard
        = (Z ∪ B).ncard := by rw [hAB]
    _ = Z.ncard + B.ncard := by rw [Set.ncard_union_eq hdisj]
    _ = 1 + (2 ^ n - 1) := by rw [hZ, hB, hBcard]
    _ = 2 ^ n := by
        rw [Nat.add_comm, Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) n))]

end fixedPowTwo

/-- In the field `GF(2, 2n)` of characteristic two, exactly `2^n` elements
satisfy `x^(2^n) = x` (the fixed field of the `n`-th Frobenius power has
`2^n` elements). -/
theorem fixed_card_pow_two (n : ℕ) (hn : 0 < n) :
    Nat.card {x : GaloisField 2 (2 * n) // x ^ (2 ^ n) = x} = 2 ^ n := by
  have h2n : 2 * n ≠ 0 := mul_ne_zero (by decide : (2 : ℕ) ≠ 0) (ne_of_gt hn)
  have hcard : Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) := by
    exact GaloisField.card 2 (2 * n) h2n
  exact fixedPowTwo.card_fixed_pow_two_of_card (K := GaloisField 2 (2 * n)) n hcard

end Commons.FieldTheory.Finite