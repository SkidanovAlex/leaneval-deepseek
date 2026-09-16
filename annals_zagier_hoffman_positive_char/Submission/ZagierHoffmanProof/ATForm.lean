import Submission.ZagierHoffmanProof.ATClaim

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# The special-index Anderson–Thakur formula: the `R`-normalisation

Writing `R_k = P_k / L_k` with `P_k = ∏_{j ≤ k}(θ - t^(q^j))` and `L_k = ∏_{j ≤ k}(θ - θ^(q^j))`, the
value of the Anderson–Thakur coefficient sequence at the special index `q^n - 1 - ∑_i N_i q^i` is
predicted (and numerically verified, `q = 2,3,5`) to be

  `atCoeff F (atIndex F n N) = atForm F n N = ∏_{i ≤ n-2} R_{n-1-i} ^ (N_i * q^i)`

(`atForm`), subject to `∑_{i<n} N_i ≤ q - 1`.  Chen's key claim (`ATClaim.lean`) takes the clean form

  `1 - ∑_{i=1}^{M-1} atE i * R_{M-1-i}^(q^i) = R_{M-1}`   (`atClaimR`),

and the increment step is `atForm_add_one`:
`atForm F n (N + e_k) = R_{n-1-k}^(q^k) * atForm F n N`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- `R_k = P_k / L_k` where `P_k = ∏_{j ≤ k}(θ - t^(q^j))` and `L_k = ∏_{j ≤ k}(θ - θ^(q^j))`. -/
noncomputable def atR (k : ℕ) : atQ F := atPk F k * (atL F k)⁻¹

/-- The predicted value of `atCoeff` at the special index `q^n - 1 - ∑_i N_i q^i`. -/
noncomputable def atForm (n : ℕ) (N : ℕ → ℕ) : atQ F :=
  ∏ i ∈ Finset.range (n - 1), (atR F (n - 1 - i)) ^ (N i * Nat.card F ^ i)

/-- The special index. -/
noncomputable def atIndex (n : ℕ) (N : ℕ → ℕ) : ℕ :=
  Nat.card F ^ n - 1 - ∑ i ∈ Finset.range n, N i * Nat.card F ^ i

/-- Chen's claim in terms of `R`. -/
theorem atClaimR (M : ℕ) :
    1 - ∑ i ∈ Finset.Icc 1 (M - 1), atE F i * (atR F (M - 1 - i)) ^ (Nat.card F ^ i)
      = atR F (M - 1) := by
  rw [atR]
  rw [← atClaim F M]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [atE, atR, mul_pow, inv_pow]
  ring

/-- The ratio of the predicted values when one entry of the shape is increased by `1`. -/
lemma atForm_add_one (n : ℕ) (N : ℕ → ℕ) (k : ℕ) (hk : k + 2 ≤ n) :
    atForm F n (fun i => N i + if i = k then 1 else 0)
      = (atR F (n - 1 - k)) ^ (Nat.card F ^ k) * atForm F n N := by
  rw [atForm, atForm]
  have hmem : k ∈ Finset.range (n - 1) := Finset.mem_range.mpr (by omega)
  have hk' : k ≤ n - 2 := by omega
  have hsplit : (∏ i ∈ Finset.range (n - 1),
        (atR F (n - 1 - i)) ^ ((N i + if i = k then 1 else 0) * Nat.card F ^ i))
      = (∏ i ∈ Finset.range (n - 1), (atR F (n - 1 - i)) ^ (N i * Nat.card F ^ i)) *
        (∏ i ∈ Finset.range (n - 1),
          (atR F (n - 1 - i)) ^ ((if i = k then 1 else 0) * Nat.card F ^ i)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [← pow_add, Nat.add_mul]
  rw [hsplit]
  have hone : (∏ i ∈ Finset.range (n - 1),
        (atR F (n - 1 - i)) ^ ((if i = k then 1 else 0) * Nat.card F ^ i))
      = (atR F (n - 1 - k)) ^ (Nat.card F ^ k) := by
    rw [Finset.prod_eq_single k]
    · rw [if_pos rfl, one_mul]
    · intro i hi hik; rw [if_neg hik, zero_mul, pow_zero]
    · intro h; exact absurd hmem h
  rw [hone, mul_comm]

end ZagierHoffmanPositiveChar

