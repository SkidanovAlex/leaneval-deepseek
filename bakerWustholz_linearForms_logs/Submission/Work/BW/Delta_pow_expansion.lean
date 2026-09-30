import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.Delta_sum_shift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-! ### The binomial/`Delta` basis of the polynomials of degree `≤ k`

Recall `deltaPoly j = (j!)⁻¹ • ∏_{i<j} (X + (i+1))`, so that evaluating at `z` gives
`Delta z j = Δ(z;j) = binom(z+j, j)`.  The `Delta (·;j)` for `j = 0, …, k` form a
triangular (hence spanning) basis of the polynomials of degree `≤ k`.

The key structural identity is
  `(X + (j+1)) • deltaPoly j = (j+1) • deltaPoly (j+1)`,
equivalently `z · Delta z j = (j+1) · (Delta z (j+1) - Delta z j)`,
which is exactly the recurrence that lets one reduce `z^{k+1}` to `z^k · z`. -/

/-- `(X + (j+1)) * deltaPoly j = (j+1) • deltaPoly (j+1)`; the product form of the recurrence
`(z+j+1)·Δ(z;j) = (j+1)·Δ(z;j+1)`. -/
lemma deltaPoly_succ_mul (j : ℕ) :
    (Polynomial.X + Polynomial.C ((j+1 : ℕ) : ℚ)) * deltaPoly j
      = ((j+1 : ℕ) : ℚ) • deltaPoly (j+1) := by
  rw [deltaPoly, deltaPoly, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
  rw [mul_smul_comm, smul_smul]
  rw [show (((j+1:ℕ):ℚ) * ((((j+1:ℕ):ℚ) * (j.factorial:ℚ)))⁻¹) = ((j.factorial:ℚ))⁻¹ from by
        field_simp]
  rw [mul_comm (X + C (((j+1:ℕ):ℚ))) (∏ x ∈ Finset.range j, (X + C (((x:ℕ):ℚ) + 1)))]
  simp

/-- Evaluated form of `deltaPoly_succ_mul`: `(z + (j+1))·Δ(z;j) = (j+1)·Δ(z;j+1)`. -/
lemma Delta_rel (z : ℂ) (j : ℕ) :
    (z + ((j+1:ℕ):ℂ)) * Delta z j = ((j+1:ℕ):ℂ) * Delta z (j+1) := by
  have h : (Polynomial.X + Polynomial.C ((j+1:ℕ):ℚ)) * deltaPoly j
      = Polynomial.C ((j+1:ℕ):ℚ) * deltaPoly (j+1) := by
    rw [← Polynomial.smul_eq_C_mul]; exact deltaPoly_succ_mul j
  have h2 := congrArg (Polynomial.aeval z) h
  simp only [Polynomial.aeval_mul, Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  simpa [Delta] using h2

/-- The recurrence driving the expansion: `z · Δ(z;j) = (j+1)·(Δ(z;j+1) - Δ(z;j))`. -/
lemma Delta_mul_self (z : ℂ) (j : ℕ) :
    z * Delta z j = ((j+1:ℕ):ℂ) * (Delta z (j+1) - Delta z j) := by
  have h := Delta_rel z j
  linear_combination h

/-- For every `k`, `z^k` is a finite ℂ-linear combination of the polynomials `Δ(z;j) = deltaPoly j`
evaluated at `z`, for `j ≤ k`.  (The `Delta z j` form the "binomial basis" `binom(z+j,j)` of the
polynomials of degree `≤ k`.) -/
theorem Delta_pow_expansion (k : ℕ) :
    ∃ b : ℕ → ℂ, (∀ j, k < j → b j = 0) ∧
      ∀ z : ℂ, z ^ k = ∑ j ∈ Finset.range (k + 1), b j * Delta z j := by
  induction k with
  | zero =>
    refine ⟨fun j => if j = 0 then 1 else 0, ?_, ?_⟩
    · intro j hj; simp only []; exact ite_eq_right (Nat.ne_of_gt hj)
    · intro z; simp [Delta, deltaPoly]
  | succ k ih =>
    obtain ⟨b, hbsupp, hbval⟩ := ih
    refine ⟨fun m => (m : ℂ) * b (m - 1) - (((m+1 : ℕ)) : ℂ) * b m, ?_, ?_⟩
    · intro m hm
      have hm1 : k < m := by omega
      have hm2 : k < m - 1 := by omega
      simp only []
      rw [hbsupp m hm1, hbsupp (m-1) hm2]
      ring
    · intro z
      rw [pow_succ', hbval z, Finset.mul_sum]
      rw [show (∑ j ∈ Finset.range (k+1), z * (b j * Delta z j))
            = ∑ j ∈ Finset.range (k+1),
                b j * ((((j+1 : ℕ)) : ℂ) * (Delta z (j+1) - Delta z j)) from ?_]
      · exact Delta_sum_shift b k (hbsupp (k+1) (by omega)) (fun m => Delta z m)
      · apply Finset.sum_congr rfl
        intro j hj
        calc z * (b j * Delta z j) = b j * (z * Delta z j) := by ring
          _ = b j * ((((j+1:ℕ)) : ℂ) * (Delta z (j+1) - Delta z j)) := by rw [Delta_mul_self]

end Work.BW
