import Mathlib
import Submission.Work.Holonomy3.cleared_defs

/-!
# Multiplying a convergent power series by a polynomial

If the coefficient series of `σ : PowerSeries ℂ` converges at `z` to `A`, i.e.
`∑ₙ (coeff n σ) zⁿ = A`, then the coefficient series of `(R : PowerSeries ℂ) * σ` converges at `z`
to `R.eval z * A`.  Multiplication by a polynomial is a finite linear combination of coefficient
shifts, so no hypothesis beyond the convergence of `σ` at `z` is needed.
-/

namespace Work.Holonomy3

open scoped BigOperators

/-- **Reindexing by a shift.**  Multiplying a power series by `X ^ k` shifts its coefficients up by
`k` places (`coeff n (X ^ k * σ) = coeff (n - k) σ` for `n ≥ k`, and `0` otherwise), which
multiplies the value of the associated coefficient series by `z ^ k`. -/
private lemma hasSum_shift_X_pow {σ : PowerSeries ℂ} {A z : ℂ} (k : ℕ)
    (h : HasSum (fun n : ℕ => PowerSeries.coeff n σ * z ^ n) A) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.X ^ k * σ) * z ^ n) (z ^ k * A) := by
  -- multiply the given series by `z ^ k` and rewrite `(coeff m σ * z ^ m) * z ^ k`
  -- as the `(m + k)`-th summand of the shifted series
  have h1 : HasSum (fun m : ℕ => (PowerSeries.coeff m σ * z ^ m) * z ^ k) (A * z ^ k) :=
    h.mul_right (z ^ k)
  have h2 : HasSum (fun m : ℕ =>
      PowerSeries.coeff (m + k) (PowerSeries.X ^ k * σ) * z ^ (m + k)) (A * z ^ k) :=
    h1.congr_fun fun m => by
      rw [PowerSeries.coeff_X_pow_mul', if_pos (Nat.le_add_left k m), Nat.add_sub_cancel]
      ring
  -- the `k` terms below the shift vanish, so the shift can be undone
  have hzero : ∑ i ∈ Finset.range k, PowerSeries.coeff i (PowerSeries.X ^ k * σ) * z ^ i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [PowerSeries.coeff_X_pow_mul', if_neg (Nat.not_le.mpr (Finset.mem_range.mp hi))]
    ring
  have h3 : HasSum (fun n : ℕ =>
      (fun i => PowerSeries.coeff i (PowerSeries.X ^ k * σ) * z ^ i) (n + k))
      ((A * z ^ k) - ∑ i ∈ Finset.range k, PowerSeries.coeff i (PowerSeries.X ^ k * σ) * z ^ i) := by
    rw [hzero, sub_zero]; exact h2
  have h4 := (hasSum_nat_add_iff'
    (f := fun i => PowerSeries.coeff i (PowerSeries.X ^ k * σ) * z ^ i) k).mp h3
  have h5 : A * z ^ k = z ^ k * A := mul_comm _ _
  rwa [h5] at h4

theorem hasSum_polynomial_mul {σ : PowerSeries ℂ} {A z : ℂ} (R : Polynomial ℂ)
    (h : HasSum (fun n : ℕ => PowerSeries.coeff n σ * z ^ n) A) :
    HasSum (fun n : ℕ => PowerSeries.coeff n ((R : PowerSeries ℂ) * σ) * z ^ n)
      (R.eval z * A) := by
  -- the statement is additive in `R`, so it suffices to check the monomials
  have key : ∀ (P : Polynomial ℂ),
      HasSum (fun n : ℕ => PowerSeries.coeff n ((P : PowerSeries ℂ) * σ) * z ^ n)
        (P.eval z * A) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q ihp ihq =>
      have hs := ihp.add ihq
      rw [Polynomial.eval_add, add_mul]
      refine hs.congr_fun fun n => ?_
      rw [Polynomial.coe_add, add_mul, map_add, add_mul]
    | monomial n a =>
      have hmono : ((Polynomial.monomial n a : Polynomial ℂ) : PowerSeries ℂ)
          = PowerSeries.C a * PowerSeries.X ^ n := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial (a := a) (n := n)]
        simp
      rw [hmono, Polynomial.eval_monomial, mul_assoc, mul_assoc]
      refine ((hasSum_shift_X_pow (z := z) (σ := σ) (A := A) n h).mul_left a).congr_fun
        fun k => ?_
      simp only [PowerSeries.coeff_C_mul]
      ring
  exact key R

end Work.Holonomy3
