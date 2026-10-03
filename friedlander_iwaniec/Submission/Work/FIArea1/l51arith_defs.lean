import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sqKernel_sq_dvd

set_option autoImplicit false
namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `sP d = ∏_{p ∣ d} p ^ ⌊v_p(d)/2⌋`, the square root of the largest square divisor of `d`
(so `sP d ^ 2 ∣ d`). -/
def sP (d : ℕ) : ℕ := ∏ p ∈ d.primeFactors, p ^ (d.factorization p / 2)

/-- `sP d ^ 2` divides `d`. -/
theorem sP_sq_dvd (d : ℕ) : (sP d) ^ 2 ∣ d := by
  rcases eq_or_ne d 0 with h | h
  · subst h
    simp [sP]
  · conv_rhs => rw [Nat.prod_primeFactors_pow_factorization h]
    have hsq : (sP d) ^ 2 = ∏ p ∈ d.primeFactors, (p ^ (d.factorization p / 2)) ^ 2 := by
      rw [sP, Finset.prod_pow]
    rw [hsq]
    refine Finset.prod_dvd_prod_of_dvd _ _ (fun p _ => ?_)
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)

/-- `d = sP d ^ 2 * (d / sP d ^ 2)`. -/
theorem sP_sq_mul_div (d : ℕ) : sP d ^ 2 * (d / sP d ^ 2) = d :=
  Nat.mul_div_cancel' (sP_sq_dvd d)

/-- `sP d` divides `d`. -/
theorem sP_dvd (d : ℕ) : sP d ∣ d := by
  have h1 : sP d ∣ sP d ^ 2 := ⟨sP d, by ring⟩
  have h2 : sP d ^ 2 ∣ d := ⟨d / sP d ^ 2, (sP_sq_mul_div d).symm⟩
  exact h1.trans h2

theorem sP_pos (d : ℕ) : 0 < sP d := by
  rw [sP]
  exact Finset.prod_pos (fun p hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _)

theorem sP_le (d : ℕ) (hd : d ≠ 0) : sP d ≤ d :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (sP_dvd d)

end

end Work.FIArea1
