import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.Basic

namespace Work.IntLib

set_option autoImplicit false

/-!
# API for `padBits`: the `L` low-order bits of `n`, least significant first

`padBits n L = (List.range L).map (fun i => n.testBit i)`.  This file collects the
elementary facts about it (length, its `ofBits`-value, bit access, injectivity on
values `< 2^L`, the shift recursion, and the matching injectivity of `ofBits` on
equal-length lists) that `padBitsAPI` is assembled from.
-/

/-- `padBits n L` has exactly `L` entries. -/
theorem padBits_length (n L : ℕ) : (padBits n L).length = L := by
  simp [padBits]

/-- The `i`-th entry of `padBits n L` (`i < L`) is the `i`-th bit of `n`. -/
theorem padBits_getD (n L i : ℕ) (h : i < L) : (padBits n L).getD i false = n.testBit i := by
  rw [padBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-- Low-bit extraction: `n % 2^(k+1)` is bit `0` of `n` followed by the low `k` bits of `n/2`. -/
theorem mod_two_pow_succ (n k : ℕ) :
    n % 2 ^ (k + 1) = 2 * (n / 2 % 2 ^ k) + n % 2 := by
  have h1 : n % 2 ^ (k + 1) / 2 = n / 2 % 2 ^ k := by
    rw [pow_succ']
    exact Nat.mod_mul_right_div_self n 2 (2 ^ k)
  have h2 : n % 2 ^ (k + 1) % 2 = n % 2 := by
    rw [pow_succ']
    exact Nat.mod_mul_right_mod n 2 (2 ^ k)
  have h3 := Nat.div_add_mod (n % 2 ^ (k + 1)) 2
  rw [h1, h2] at h3
  exact h3.symm

/-- Shift recursion for `padBits`: appending the bit `d` at the low end shifts the window. -/
theorem padBits_bit (d : Bool) (L r : ℕ) (hL : 1 ≤ L) :
    padBits (2 * r + d.toNat) L = d :: padBits r (L - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  have hbit : 2 * r + d.toNat = Nat.bit d r := by
    cases d <;> simp [Nat.bit]
  rw [hbit, padBits, List.range_succ_eq_map, List.map_cons]
  have key : List.map (fun i => (Nat.bit d r).testBit i) (List.map Nat.succ (List.range k))
      = padBits r k := by
    rw [List.map_map, padBits]
    apply List.map_congr_left
    intro i _
    exact Nat.testBit_bit_succ i d r
  rw [key, Nat.testBit_bit_zero, Nat.add_sub_cancel]

/-- `padBits` is a left inverse of `ofBits` at the list's own length. -/
theorem padBits_ofBits (l : List Bool) : padBits (ofBits l) l.length = l := by
  induction l with
  | nil => simp [padBits]
  | cons b xs ih =>
    have hb : ofBits (b :: xs) = 2 * ofBits xs + b.toNat := by
      rw [ofBits_cons]; ring
    rw [hb, List.length_cons]
    rw [padBits_bit b (xs.length + 1) (ofBits xs) (by omega)]
    rw [Nat.add_sub_cancel, ih]

/-- `ofBits` reads back exactly `n % 2^L` from the `L` low-order bits of `n`. -/
theorem ofBits_padBits (n L : ℕ) : ofBits (padBits n L) = n % 2 ^ L := by
  induction L generalizing n with
  | zero => simp [padBits, ofBits, Nat.mod_one]
  | succ k ih =>
    have hbit : Nat.bit (n.testBit 0) (n / 2) = 2 * (n / 2) + (n.testBit 0).toNat := by
      cases h : n.testBit 0 <;> simp [Nat.bit]
    have hn' : Nat.bit (n.testBit 0) (n / 2) = n := Nat.bit_bodd_div2 n
    have hn : 2 * (n / 2) + (n.testBit 0).toNat = n := by
      rw [← hbit]; exact hn'
    have hpb : padBits n (k + 1) = (n.testBit 0) :: padBits (n / 2) k := by
      conv_lhs => rw [← hn]
      rw [padBits_bit (n.testBit 0) (k + 1) (n / 2) (by omega), Nat.add_sub_cancel]
    rw [hpb, ofBits_cons, ih (n / 2), mod_two_pow_succ]
    have h2 : n % 2 = (n.testBit 0).toNat := by
      rw [Nat.mod_two_of_bodd]; rfl
    rw [h2]; ring

/-- `ofBits` is injective on bit lists of a fixed length. -/
theorem ofBits_inj_of_length_eq (l₁ l₂ : List Bool) (h : l₁.length = l₂.length)
    (h2 : ofBits l₁ = ofBits l₂) : l₁ = l₂ := by
  calc l₁ = padBits (ofBits l₁) l₁.length := (padBits_ofBits l₁).symm
    _ = padBits (ofBits l₂) l₁.length := by rw [h2]
    _ = padBits (ofBits l₂) l₂.length := by rw [h]
    _ = l₂ := padBits_ofBits l₂

theorem padBitsAPI :
    (∀ n L : ℕ, (Work.IntLib.padBits n L).length = L) ∧
    (∀ n L : ℕ, Work.IntLib.ofBits (Work.IntLib.padBits n L) = n % 2 ^ L) ∧
    (∀ (n L i : ℕ), i < L → (Work.IntLib.padBits n L).getD i false = n.testBit i) ∧
    (∀ (x y L : ℕ), x < 2 ^ L → y < 2 ^ L → Work.IntLib.padBits x L = Work.IntLib.padBits y L →
      x = y) ∧
    (∀ (d : Bool) (L r : ℕ), 1 ≤ L →
      Work.IntLib.padBits (2 * r + d.toNat) L = d :: Work.IntLib.padBits r (L - 1)) ∧
    (∀ (l₁ l₂ : List Bool), l₁.length = l₂.length → Work.IntLib.ofBits l₁ = Work.IntLib.ofBits l₂ →
      l₁ = l₂) ∧
    (∀ (n L : ℕ), Work.IntLib.ofBits (Work.IntLib.padBits n L) ≤ n) := by
  refine ⟨padBits_length, ofBits_padBits, padBits_getD, ?_, padBits_bit,
    ofBits_inj_of_length_eq, ?_⟩
  · intro x y L hx hy hxy
    have hx' : x % 2 ^ L = x := Nat.mod_eq_of_lt hx
    have hy' : y % 2 ^ L = y := Nat.mod_eq_of_lt hy
    calc x = x % 2 ^ L := hx'.symm
      _ = ofBits (padBits x L) := (ofBits_padBits x L).symm
      _ = ofBits (padBits y L) := by rw [hxy]
      _ = y % 2 ^ L := ofBits_padBits y L
      _ = y := hy'
  · intro n L
    rw [ofBits_padBits]
    exact Nat.mod_le n (2 ^ L)

end Work.IntLib
