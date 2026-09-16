import Submission.ZagierHoffmanProof.GenEntire
import Submission.ZagierHoffmanProof.EvalEntire

/-!
# Regression tests for the generic `ε`-chapter

Over a `ℤᵐ⁰`-valued field, the generic notions of `GenEntire.lean` (`GEntire`, `GSuperEntire γ`)
coincide with the `ℤᵐ⁰`-specific ones of `Entire.lean`/`SuperEntire.lean` when
`γ = WithZero.exp (-1)`: this shows that the generic chapter specialises to the existing one
(and hence that the existing analytic chapter can be *transported* to the generic setting).
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- A nonzero element of `ℤᵐ⁰` is an `exp`. -/
lemma exists_exp_eq_of_ne_zero' {x : ℤᵐ⁰} (hx : x ≠ 0) : ∃ k : ℤ, x = WithZero.exp k :=
  WithZero.expRecOn x (motive := fun x => x ≠ 0 → ∃ k : ℤ, x = WithZero.exp k)
    (fun h => absurd rfl h) (fun a _ => ⟨a, rfl⟩) hx

/-- `(exp (-1)) ^ (M * n) = exp (-(M * n))`. -/
lemma exp_neg_one_pow (M n : ℕ) :
    (WithZero.exp (-1) : ℤᵐ⁰) ^ (M * n) = WithZero.exp (-((M : ℤ) * (n : ℤ))) := by
  rw [expmul]
  congr 1
  push_cast
  ring

/-- The generic entire condition is the `ℤᵐ⁰`-specific one. -/
lemma gEntire_iff_entire (f : PowerSeries K) : GEntire f ↔ Entire f := by
  constructor
  · intro hf N
    exact hf (WithZero.exp (-N)) (WithZero.exp_ne_zero)
  · intro hf u hu
    obtain ⟨k, rfl⟩ := exists_exp_eq_of_ne_zero' hu
    filter_upwards [hf (-k)] with n hn
    simpa using hn

/-- `exp a * (exp (-1)) ^ (M * n) = exp (a - M * n)`. -/
lemma exp_mul_exp_neg_one_pow (a : ℤ) (M n : ℕ) :
    WithZero.exp a * (WithZero.exp (-1) : ℤᵐ⁰) ^ (M * n)
      = WithZero.exp (a - (M : ℤ) * (n : ℤ)) := by
  rw [expmul, ← WithZero.exp_add]
  congr 1
  push_cast
  ring

/-- The generic super-entire condition is the `ℤᵐ⁰`-specific one. -/
lemma gSuperEntire_iff_superEntire (f : PowerSeries K) :
    GSuperEntire (WithZero.exp (-1)) f ↔ SuperEntire f := by
  constructor
  · intro hf M
    obtain ⟨A, hA⟩ := hf M
    rcases eq_or_ne A 0 with h0 | h0
    · refine ⟨0, fun n => ?_⟩
      have h : Valued.v (PowerSeries.coeff n f) ≤ (0 : ℤᵐ⁰) := by
        have h' := hA n
        rwa [h0, zero_mul] at h'
      refine le_trans h ?_
      exact (zero_le : (0 : ℤᵐ⁰) ≤ WithZero.exp ((0 : ℤ) - (M : ℤ) * (n : ℤ)))
    · obtain ⟨a, rfl⟩ := exists_exp_eq_of_ne_zero' h0
      exact ⟨a, fun n => le_of_le_of_eq (hA n) (exp_mul_exp_neg_one_pow a M n)⟩
  · intro hf M
    obtain ⟨a, ha⟩ := hf M
    exact ⟨WithZero.exp a, fun n => le_of_le_of_eq (ha n) (exp_mul_exp_neg_one_pow a M n).symm⟩

end ZagierHoffmanPositiveChar
