import Mathlib
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Submission.Work.LinnikAreas.Density4.ShiftedDefs
import Submission.Work.LinnikAreas.Density4.Phi_sub_Psi_le
import Submission.Work.LinnikAreas.Density4.sig_mul_of_coprime
import Submission.Work.LinnikAreas.Density4.sHalf_facts

namespace Work.LinnikAreas.Density4

noncomputable section

open Finset
open scoped BigOperators

/-- The (coprime-)multiplicative arithmetic function
`f d = μ(d)² · σ_{-1/2}(d) / d` used in the alternative proof. -/
private def muSqSig (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ)^2 / (d:ℝ) * sigR d

private lemma muSqSig_one : muSqSig 1 = 1 := by
  unfold muSqSig sigR
  rw [ArithmeticFunction.moebius_apply_one, Nat.divisors_one, Finset.sum_singleton]
  norm_num

private lemma muSqSig_mul {a b : ℕ} (hab : a.Coprime b) :
    muSqSig (a*b) = muSqSig a * muSqSig b := by
  unfold muSqSig
  have hmu : (ArithmeticFunction.moebius (a*b) : ℝ)
      = (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab]
    push_cast
    ring
  rw [hmu, sig_mul_of_coprime hab, Nat.cast_mul]
  ring_nf

private lemma muSqSig_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) :
    muSqSig (p^k) = 0 := by
  unfold muSqSig
  have h : ArithmeticFunction.moebius (p^k) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show k ≠ 1 by omega]
  rw [h]
  simp

/-- `σ_{-1/2}(p) = 1 + 1/√p` for a prime `p`. -/
private lemma sigR_prime (p : ℕ) (hp : p.Prime) : sigR p = 1 + 1/Real.sqrt (p:ℝ) := by
  unfold sigR
  rw [Nat.Prime.divisors hp]
  rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hp.ne_one h.symm)]
  simp [Real.sqrt_one]

private lemma muSqSig_prime (p : ℕ) (hp : p.Prime) :
    muSqSig p = (1 + 1/Real.sqrt (p:ℝ)) / (p:ℝ) := by
  unfold muSqSig
  rw [sigR_prime p hp, ArithmeticFunction.moebius_apply_prime hp]
  ring_nf

/-- `1 + f(p) = (1 + 1/√p) · f(p)` where `f(p) = 1/p + g(p)` is the local Euler
factor of `ShiftedDefs`. -/
private lemma one_add_muSqSig_prime (p : ℕ) (hp : p.Prime) :
    1 + muSqSig p = (1 + 1/Real.sqrt (p:ℝ)) * fR p := by
  rw [muSqSig_prime p hp]
  unfold fR gR
  field_simp
  ring

private lemma mul_gR_one (p : ℕ) : (1 + 1/Real.sqrt (p:ℝ)) * gR p = 1 := by
  unfold gR
  rw [mul_inv_cancel₀]
  positivity

/-- Alternative proof of the diagonal weighted divisor sum estimate
`Σ_{d | r, d ≥ 2} μ(d)² σ_{-1/2}(d)/d ≤ (9/10) σ_{-1/2}(r)`, where
`σ_{-1/2}(m) = Σ_{e | m} 1/√e`.
(This is the same estimate as `Work.LinnikAreas.Density4.diagonalWeightedSum_le`; a second,
independent proof is wanted.  It is needed as the input to
`Work.LinnikAreas.Density4.selTheta_asymptotic`.)

Suggested route, using only material already in this workspace:

Write `f(d) = μ(d)²·σ_{-1/2}(d)/d` (so `f p = (1 + 1/√p)/p` for `p` prime).  One has
`f 1 = 1`, `f` is multiplicative on coprime arguments (`σ_{-1/2}` is multiplicative:
`sig_mul_of_coprime`; `μ²` is multiplicative by `ArithmeticFunction.isMultiplicative_moebius`;
`1/(ab) = 1/a·1/b`), and `f (p^k) = 0` for `k ≥ 2` since `μ (p^k) = 0`
(`ArithmeticFunction.moebius_apply_prime_pow`).  Hence, for `r ≠ 0`,
`Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors f r hr0`
(import `Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors`)
gives `∏ p ∈ r.primeFactors, (1 + f p) = ∑ d ∈ r.divisors, f d`.

Now `1 + f p = (1 + 1/√p) · fR p`, where `fR p = 1/p + gR p` and
`gR p = (1 + 1/√p)⁻¹` are the local Euler factors of
`Submission.Work.LinnikAreas.Density4.ShiftedDefs`, and `(1 + 1/√p) · gR p = 1`
(both identities are `field_simp; ring`).  Therefore, putting
`B := ∏ p ∈ r.primeFactors, (1 + 1/√p)`, one gets

  `∑ d ∈ r.divisors, f d = B · Φ r.primeFactors`  and  `1 = B · Ψ r.primeFactors`,

where `Φ s = ∏ p ∈ s, fR p`, `Ψ s = ∏ p ∈ s, gR p` (products over the `Finset r.primeFactors`).
Also `r.divisors.filter (fun d => 2 ≤ d) = r.divisors.erase 1` (all divisors are `≥ 1`), so
`∑ d ∈ r.divisors.filter (fun d => 2 ≤ d), f d = B·Φ - 1 = B·Φ - B·Ψ = B·(Φ - Ψ) ≤ (9/10)·B`
by `Phi_sub_Psi_le r.primeFactors (fun p hp => (Nat.mem_primeFactors.mp hp).1)` and `B ≥ 0`.
Finally `B ≤ σ_{-1/2}(r)` is the first conjunct of
`Work.LinnikAreas.Density4.sHalf_facts r hr`. -/
theorem diag_weighted_sum_le_alt {r : ℕ} (hr : 1 ≤ r) :
    (∑ d ∈ r.divisors.filter (fun d : ℕ => 2 ≤ d),
        ((ArithmeticFunction.moebius d : ℝ))^2 / (d : ℝ) *
          (∑ e ∈ d.divisors, (1 : ℝ) / Real.sqrt (e : ℝ)))
      ≤ (9/10) * (∑ e ∈ r.divisors, (1 : ℝ) / Real.sqrt (e : ℝ)) := by
  classical
  change (∑ d ∈ r.divisors.filter (fun d : ℕ => 2 ≤ d), muSqSig d) ≤ (9/10) * sigR r
  have hr0 : r ≠ 0 := by omega
  -- `r.divisors.filter (· ≥ 2) = r.divisors.erase 1`
  have hfilter : r.divisors.filter (fun d : ℕ => 2 ≤ d) = r.divisors.erase 1 := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hd, h2⟩; exact ⟨by omega, hd⟩
    · rintro ⟨hne, hd⟩
      exact ⟨hd, by have := Nat.pos_of_mem_divisors hd; omega⟩
  -- Euler-product identity for the multiplicative function `f`
  have hkey := Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
      muSqSig r hr0 muSqSig_one (fun a b hab => muSqSig_mul hab)
      (fun p k hp hk => muSqSig_prime_pow p k hp hk)
  set B : ℝ := ∏ p ∈ r.primeFactors, (1 + 1/Real.sqrt (p:ℝ)) with hB
  have hS : (∑ d ∈ r.divisors, muSqSig d) = B * PhiSh r.primeFactors := by
    rw [← hkey]
    rw [Finset.prod_congr rfl
      (fun p hp => one_add_muSqSig_prime p (Nat.prime_of_mem_primeFactors hp))]
    rw [Finset.prod_mul_distrib]
    unfold PhiSh
    rw [hB]
  have hOne : (1:ℝ) = B * Psi r.primeFactors := by
    calc (1:ℝ) = ∏ p ∈ r.primeFactors, (1:ℝ) := by simp
      _ = ∏ p ∈ r.primeFactors, (1 + 1/Real.sqrt (p:ℝ)) * gR p :=
            Finset.prod_congr rfl (fun p _ => (mul_gR_one p).symm)
      _ = (∏ p ∈ r.primeFactors, (1 + 1/Real.sqrt (p:ℝ))) * (∏ p ∈ r.primeFactors, gR p) :=
            Finset.prod_mul_distrib
      _ = B * Psi r.primeFactors := by unfold Psi; rw [hB]
  have heq : (∑ d ∈ r.divisors.filter (fun d : ℕ => 2 ≤ d), muSqSig d)
      = (∑ d ∈ r.divisors, muSqSig d) - 1 := by
    rw [hfilter]
    have h1mem : 1 ∈ r.divisors := Nat.one_mem_divisors.mpr hr0
    have hsum := Finset.sum_erase_add r.divisors muSqSig h1mem
    rw [muSqSig_one] at hsum
    linarith
  have hmaineq : (∑ d ∈ r.divisors.filter (fun d : ℕ => 2 ≤ d), muSqSig d)
      = B * (PhiSh r.primeFactors - Psi r.primeFactors) := by
    rw [heq, hS, hOne]; ring
  rw [hmaineq]
  have hBnonneg : 0 ≤ B := by
    rw [hB]
    exact Finset.prod_nonneg (fun p _ => by positivity)
  have hBle : B ≤ sigR r := by
    rw [hB]; unfold sigR
    exact (sHalf_facts r hr).1
  have hle : PhiSh r.primeFactors - Psi r.primeFactors ≤ 9/10 :=
    Phi_sub_Psi_le _ (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  calc B * (PhiSh r.primeFactors - Psi r.primeFactors)
      ≤ B * (9/10) := mul_le_mul_of_nonneg_left hle hBnonneg
    _ = (9/10) * B := by ring
    _ ≤ (9/10) * sigR r := by
        apply mul_le_mul_of_nonneg_left hBle; norm_num

end

end Work.LinnikAreas.Density4
