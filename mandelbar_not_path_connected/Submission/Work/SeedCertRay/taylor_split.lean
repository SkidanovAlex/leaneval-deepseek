import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Finset

namespace Work.SeedCertRay

/-- Splitting a sum over `range (2*n)` into its even-indexed and odd-indexed parts. -/
lemma sum_range_two_mul_odd_even {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    (∑ k ∈ Finset.range (2*n), f k)
      = (∑ k ∈ Finset.range n, f (2*k)) + ∑ k ∈ Finset.range n, f (2*k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, Finset.sum_range_succ]
    ac_rfl

theorem taylor_split (t : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (2*N), (Complex.I * (t:ℂ))^k / ((k.factorial : ℕ) : ℂ))
      = (((∑ k ∈ Finset.range N, (-(t^2))^k / (((2*k).factorial : ℕ) : ℝ)) : ℝ) : ℂ)
        + (((t * (∑ k ∈ Finset.range N, (-(t^2))^k / (((2*k+1).factorial : ℕ) : ℝ))) : ℝ) : ℂ) * Complex.I := by
  have h2 : (Complex.I * (t:ℂ))^2 = ((-(t^2) : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Complex.ofReal_neg]; ring
  have h_even_pow : ∀ k, (Complex.I * (t:ℂ))^(2*k) = (((-(t^2))^k : ℝ) : ℂ) := by
    intro k
    rw [pow_mul, h2, ← Complex.ofReal_pow]
  have h_even : ∀ k, (Complex.I * (t:ℂ))^(2*k) / (((2*k).factorial : ℕ) : ℂ)
      = (((-(t^2))^k / (((2*k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro k
    rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, ← h2, ← pow_mul]
  have h_odd : ∀ k, (Complex.I * (t:ℂ))^(2*k+1) / (((2*k+1).factorial : ℕ) : ℂ)
      = Complex.I * (((t * (-(t^2))^k) / (((2*k+1).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro k
    have hnum : (Complex.I * (t:ℂ))^(2*k+1) = Complex.I * (((t * (-(t^2))^k) : ℝ) : ℂ) := by
      rw [pow_succ, h_even_pow k, Complex.ofReal_mul]; ring
    rw [hnum, Complex.ofReal_div, Complex.ofReal_natCast, mul_div_assoc]
  have hEsum : (∑ k ∈ Finset.range N, (Complex.I * (t:ℂ))^(2*k) / (((2*k).factorial : ℕ) : ℂ))
      = (((∑ k ∈ Finset.range N, (-(t^2))^k / (((2*k).factorial : ℕ) : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun k _ => h_even k)
  have hOsum : (∑ k ∈ Finset.range N, (Complex.I * (t:ℂ))^(2*k+1) / (((2*k+1).factorial : ℕ) : ℂ))
      = Complex.I * (((t * (∑ k ∈ Finset.range N, (-(t^2))^k / (((2*k+1).factorial : ℕ) : ℝ))) : ℝ) : ℂ) := by
    have key : ((t * (∑ k ∈ Finset.range N, (-(t^2))^k / (((2*k+1).factorial : ℕ) : ℝ))) : ℝ)
        = (∑ k ∈ Finset.range N, t * ((-(t^2))^k / (((2*k+1).factorial : ℕ) : ℝ))) := by
      rw [Finset.mul_sum]
    rw [key, Complex.ofReal_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [h_odd k, mul_div_assoc])
  rw [sum_range_two_mul_odd_even _ N, hEsum, hOsum, mul_comm Complex.I]

end Work.SeedCertRay
