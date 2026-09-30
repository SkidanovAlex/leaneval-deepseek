import Mathlib
import Submission.Work.BMF.recursion.LinnikDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reduction map for the Linnik lifting step

`linnikRed p ℓ k` is the map `(Fin k → Fin (p^(ℓ+1))) → (Fin k → Fin (p^ℓ))` which reduces
every coordinate modulo `p^ℓ`.  It is the projection used in the digit-by-digit lifting
step `Work.BMF.recursion.linnik_step`.
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open Finset

/-- Reduce every coordinate of a `k`-tuple of residues modulo `p^(ℓ+1)` modulo `p^ℓ`. -/
def linnikRed (p ℓ k : ℕ) (b : Fin k → Fin (p ^ (ℓ + 1))) : (Fin k → Fin (p ^ ℓ)) :=
  fun i => ⟨(b i).val % p ^ ℓ, by
    by_cases h : p ^ ℓ = 0
    · have hp0 : p ^ (ℓ + 1) = 0 := by rw [pow_succ, h, zero_mul]
      have : (b i).val < 0 := by rw [← hp0]; exact (b i).isLt
      omega
    · exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩

@[simp] theorem linnikRed_apply (p ℓ k : ℕ) (b : Fin k → Fin (p ^ (ℓ + 1))) (i : Fin k) :
    (linnikRed p ℓ k b i).val = (b i).val % p ^ ℓ := rfl

/-- `p` divides `x - (x mod p)`. -/
theorem dvd_sub_mod (p x : ℕ) : (p : ℤ) ∣ (x : ℤ) - ((x % p : ℕ) : ℤ) := by
  refine ⟨((x / p : ℕ) : ℤ), ?_⟩
  have h := Nat.mod_add_div x p
  have h' : (x : ℤ) = ((x % p : ℕ) : ℤ) + (p : ℤ) * ((x / p : ℕ) : ℤ) := by
    exact_mod_cast h.symm
  rw [h']; ring

/-- Congruent tuples have congruent power sums: if `q ∣ b i - x i` for all `i` then
`q ∣ ∑ b i^j - ∑ x i^j`. -/
theorem pow_sum_congr (q : ℤ) (k j : ℕ) (x b : Fin k → ℕ)
    (h : ∀ i, q ∣ (b i : ℤ) - (x i : ℤ)) :
    q ∣ (∑ i, (b i : ℤ) ^ j) - (∑ i, (x i : ℤ) ^ j) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  exact dvd_trans (h i) (sub_dvd_pow_sub_pow _ _ j)

end Work.BMF.recursion
