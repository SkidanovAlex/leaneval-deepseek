import Mathlib
import Submission.Work.BW.ap_factorial_dvd
import Submission.Work.BW.auxpolydefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial Finset

/-- Evaluation form of `deltaRat`: `Δ(x;k) = (x+1)(x+2)⋯(x+k)/k!`. -/
lemma deltaRat_eq_inv_mul_prod (x : ℤ) (k : ℕ) :
    deltaRat x k
      = ((k.factorial : ℚ))⁻¹ * ∏ i ∈ Finset.range k, ((x : ℚ) + (i : ℚ) + 1) := by
  rw [deltaRat, deltaPoly, Polynomial.smul_eq_C_mul, map_mul, Polynomial.aeval_C]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C]
  push_cast
  ring

/-- `deltaRat x k = Δ(x;k) = (x+1)⋯(x+k)/k! = C(x+k,k)` is an integer for every integer `x`
and `k : ℕ`.  Proof: `ap_factorial_dvd k 1 (x+k)` gives `k! ∣ ∏_{i<k}(x+i+1)`, and
`deltaRat x k` is `(k!)⁻¹ · ∏_{i<k}(x+i+1)`. -/
theorem deltaRat_int (x : ℤ) (k : ℕ) : ∃ N : ℤ, deltaRat x k = (N : ℚ) := by
  obtain ⟨N, hN⟩ := Nat.factorial_coe_dvd_prod k (x + 1)
  refine ⟨N, ?_⟩
  rw [deltaRat_eq_inv_mul_prod]
  have hcast : (∏ i ∈ Finset.range k, ((x : ℚ) + (i : ℚ) + 1))
      = (k.factorial : ℚ) * (N : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hN
    simp only [Int.cast_prod, Int.cast_add, Int.cast_natCast] at h
    push_cast at h
    have hp1 : (∏ i ∈ Finset.range k, ((x : ℚ) + (i : ℚ) + 1))
        = ∏ i ∈ Finset.range k, ((x : ℚ) + 1 + (i : ℚ)) :=
      Finset.prod_congr rfl fun i _ => by ring
    rw [hp1, h]
  rw [hcast, inv_mul_cancel_left₀]
  exact_mod_cast Nat.factorial_ne_zero k

end Work.BW
