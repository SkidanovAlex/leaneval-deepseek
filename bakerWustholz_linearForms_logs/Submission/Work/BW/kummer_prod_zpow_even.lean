import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.kummer_zpow_parity_square

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Under the Kummer condition, an element `∏ i, β i ^ (d i)` with arbitrary integral exponents is a square only if all exponents are even. -/
theorem kummer_prod_zpow_even {K : Type*} [Field K] {n : ℕ} (β : Fin n → K)
    (hβnz : ∀ i, β i ≠ 0) (hβ : KummerCond β) (d : Fin n → ℤ)
    (hsq : IsSquare (∏ i, β i ^ d i)) : ∀ i, (2 : ℤ) ∣ d i := by
  -- Reduce every exponent modulo `2`: a square instance only depends on the parity.
  have hsq2 : IsSquare (∏ i, β i ^ (d i % 2)) := kummer_zpow_parity_square β hβnz d hsq
  -- Encode the remainders as a `Fin 2`-valued exponent vector.
  have hpar : ∀ i : Fin n, ∃ a : Fin 2, ((a : ℕ) : ℤ) = d i % 2 := by
    intro i
    rcases Int.emod_two_eq_zero_or_one (d i) with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose e he using hpar
  -- Rewrite the parity product as a product over `Fin 2` exponents.
  have hprod : (∏ i, β i ^ (d i % 2)) = ∏ i, β i ^ (e i : ℕ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← zpow_natCast (β i) (e i : ℕ), he i]
  rw [hprod] at hsq2
  -- `KummerCond` forces the exponent vector to vanish.
  have he0 : e = 0 := by
    by_contra hne
    exact (hβ e hne) hsq2
  intro i
  rw [Int.dvd_iff_emod_eq_zero]
  have hi : (e i : ℕ) = 0 := by rw [he0]; rfl
  rw [← he i, hi]
  norm_num

end Work.BW
