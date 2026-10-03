/-
# `Submission.Work.FIArea7.KronTwo` — the Kronecker symbol `(2|·)`

`χ₂(a) = (2|a) = (−1)^{(a²−1)/8} = ±1` for odd `a` (and `0` for even `a`) is the character of
`(ℤ/8ℤ)^*` with `χ₂(±1) = 1`, `χ₂(±3) = −1`.  It is *not* Mathlib's `jacobiSym 2 a`
(which is `1` for odd `a`, because `legendreSym 2 a` is trivial — and that is exactly what makes
Mathlib's `jacobiSym a b` agree with the paper's convention (8.15), i.e. the symbol of the *odd
part* of `b`).

It is needed to write *FI* Lemma 17.1 in the form the frozen area-7 sums consume it: with Mathlib's
`jacobiSym` the identity

  `(Re(z̄₁z₂) | |Δ|)·(|z₁|² | |Δ|) = (s₁/|r₁|)(s₂/|r₂|)`

requires the source's `z₁ ≡ z₂ (mod 8)` (which the source gets from (5.7), a *fixed residue class
mod 8* for `β`), whereas with the *Kronecker* symbol

  `Kron(a|b) = jacobiSym a b · χ₂(a)^{ν₂(b)}`

it needs only `z₁ ≡ z₂ (mod 4)` — and `z₁ ≡ z₂ (mod 4)` is exactly what the frozen sums force,
through the factor `4d ∣ |Δ|` (for primary `z₁, z₂` one has `Δ ≡ r₂ − r₁ (mod 4)`).  The two
conventions differ by `χ₂(Re(z̄₁z₂))^{ν₂(|Δ|)}·χ₂(|z₁|²)^{ν₂(|Δ|)}`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea7

/-- The Kronecker symbol `(2|a) = (−1)^{(a²−1)/8}` for odd `a`, extended by `0` to even `a`. -/
def kronTwo (a : ℤ) : ℤ := if Even a then 0 else if a % 8 = 1 ∨ a % 8 = 7 then 1 else -1

/-- `χ₂` is odd-supported. -/
lemma kronTwo_eq_zero_of_even {a : ℤ} (ha : Even a) : kronTwo a = 0 := by
  rw [kronTwo, if_pos ha]

/-- `χ₂` takes the values `±1` on odd integers. -/
lemma kronTwo_eq_one_or_neg_one_of_odd {a : ℤ} (ha : Odd a) :
    kronTwo a = 1 ∨ kronTwo a = -1 := by
  have hne : ¬ Even a := by
    rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := ha
    omega
  rw [kronTwo, if_neg hne]
  split_ifs <;> simp

/-- `χ₂` does not vanish on odd integers. -/
lemma kronTwo_ne_zero_of_odd {a : ℤ} (ha : Odd a) : kronTwo a ≠ 0 := by
  rcases kronTwo_eq_one_or_neg_one_of_odd ha with h | h <;> rw [h] <;> norm_num

end Work.FIArea7
