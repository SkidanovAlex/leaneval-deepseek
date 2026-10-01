import Mathlib
import Submission.Work.LinnikAreas.Density4.dtb_prime_local_bound
import Submission.Work.LinnikAreas.Density4.dtb_euler_H
import Submission.Work.LinnikAreas.Density4.dtb_prod_inv_sqrt_le_sigma
import Submission.Work.LinnikAreas.Density4.dtb_prod_B_le

namespace Work.LinnikAreas.Density4

open Finset

/-- The square of the Möbius function is at most one. -/
lemma moebius_sq_le_one (d : ℕ) : ((ArithmeticFunction.moebius d : ℝ))^2 ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> rw [h] <;> norm_num

/-- Core multiplicative comparison: `Σ_{d|r} μ(d)²·√d/φ(d) ≤ 1000·σ_{-1/2}(r)`.

Expanding both sides as Euler products, `Σ_{d|r} μ(d)²√d/φ(d) = ∏_{p|r}(1+√p/(p-1))`
(`dtb_euler_H`), while `σ_{-1/2}(r) ≥ ∏_{p|r}(1+1/√p)` (`dtb_prod_inv_sqrt_le_sigma`).
By the local inequality `dtb_prime_local_bound` the first product is at most
`(∏_{p|r}(1+1/√p))·(∏_{p|r}(1+1/(p-1)^{3/2}))`, and the last factor is at most `1000`
(`dtb_prod_B_le`). -/
theorem divisorTail_core (r : ℕ) (hr : 1 ≤ r) :
    (∑ d ∈ r.divisors,
        ((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d : ℝ) / (Nat.totient d : ℝ))
      ≤ 1000 * ∑ d ∈ r.divisors, (1 : ℝ)/Real.sqrt (d : ℝ) := by
  have hEuler := dtb_euler_H r hr
  have hprod : (∏ p ∈ r.primeFactors, (1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1)))
      ≤ ∏ p ∈ r.primeFactors,
          (1 + 1 / Real.sqrt (p : ℝ)) * (1 + 1 / ((p : ℝ) - 1) ^ (3 / 2 : ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have h1 : 0 ≤ Real.sqrt (p:ℝ) / ((p:ℝ) - 1) :=
        div_nonneg (Real.sqrt_nonneg _) (by linarith)
      linarith
    · intro p hp
      exact dtb_prime_local_bound p (Nat.prime_of_mem_primeFactors hp)
  rw [Finset.prod_mul_distrib] at hprod
  have h4 := dtb_prod_inv_sqrt_le_sigma r hr
  have h5 := dtb_prod_B_le r hr
  have hsig : 0 ≤ ∑ d ∈ r.divisors, (1 : ℝ)/Real.sqrt (d : ℝ) := by
    apply Finset.sum_nonneg; intro d hd
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hB : 0 ≤ ∏ p ∈ r.primeFactors, (1 + 1 / ((p : ℝ) - 1) ^ (3 / 2 : ℝ)) := by
    apply Finset.prod_nonneg; intro p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hbase : 0 ≤ ((p:ℝ) - 1) ^ (3/2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hle : 0 ≤ 1 / ((p:ℝ) - 1) ^ (3/2 : ℝ) := div_nonneg zero_le_one hbase
    linarith
  rw [hEuler]
  calc ∏ p ∈ r.primeFactors, (1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1))
      ≤ (∏ p ∈ r.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (∏ p ∈ r.primeFactors, (1 + 1 / ((p : ℝ) - 1) ^ (3 / 2 : ℝ))) := hprod
    _ ≤ (∑ d ∈ r.divisors, (1 : ℝ)/Real.sqrt (d : ℝ)) * 1000 :=
        mul_le_mul h4 h5 hB hsig
    _ = 1000 * ∑ d ∈ r.divisors, (1 : ℝ)/Real.sqrt (d : ℝ) := by ring

/-- Large-divisor harmonic sums over the divisors of `r`, with the sharp `σ_{-1/2}`-weight:
for every `X > 0` and `r ≥ 1`,
`Σ_{d | r, d > X} μ(d)²/d ≤ σ_{-1/2}(r)/√X` and
`Σ_{d | r, d > X} μ(d)²/φ(d) ≤ 1000·σ_{-1/2}(r)/√X`,
where `σ_{-1/2}(r) = Σ_{d | r} 1/√d`.  (Proof: `1/d ≤ 1/(√X·√d)` for `d > X`, and
`d/φ(d) = Π_{p | d} p/(p-1) ≤ C·Π_{p | d}(1 + p^{-1/2})` for an absolute constant `C`; a crude
`C = 1000` is enough.) -/
theorem divisorTail_bounds (r : ℕ) (hr : 1 ≤ r) (X : ℝ) (hX : 0 < X) :
    (∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
        ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ))
      ≤ (∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) / Real.sqrt X ∧
    (∑ d ∈ r.divisors.filter (fun d : ℕ => X < (d:ℝ)),
        ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
      ≤ 1000 * ((∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) / Real.sqrt X) := by
  have hsqrtXpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  constructor
  · -- first conjunct
    set F := r.divisors.filter (fun d : ℕ => X < (d:ℝ)) with hF
    have hFsub : F ⊆ r.divisors := by rw [hF]; exact Finset.filter_subset _ _
    have hA : (∑ d ∈ F, ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ))
        ≤ ∑ d ∈ F, (1/Real.sqrt X) * (1/Real.sqrt (d:ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [hF, Finset.mem_filter] at hd
      obtain ⟨hddiv, hdX⟩ := hd
      have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hddiv
      have hsdp : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdpos
      have hstep1 : ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) ≤ 1/(d:ℝ) := by
        rw [div_le_div_iff_of_pos_right hdpos]; simpa using moebius_sq_le_one d
      have hsd : Real.sqrt X ≤ Real.sqrt (d:ℝ) := Real.sqrt_le_sqrt (le_of_lt hdX)
      have hinv : (1:ℝ)/Real.sqrt (d:ℝ) ≤ 1/Real.sqrt X :=
        one_div_le_one_div_of_le hsqrtXpos hsd
      have h2 : (1:ℝ)/(d:ℝ) = (1/Real.sqrt (d:ℝ)) * (1/Real.sqrt (d:ℝ)) := by
        rw [one_div_mul_one_div, Real.mul_self_sqrt (le_of_lt hdpos)]
      have hstep2 : (1:ℝ)/(d:ℝ) ≤ (1/Real.sqrt X) * (1/Real.sqrt (d:ℝ)) := by
        rw [h2]
        exact mul_le_mul_of_nonneg_right hinv (div_nonneg zero_le_one (Real.sqrt_nonneg _))
      linarith
    have hB : (∑ d ∈ F, (1/Real.sqrt X) * (1/Real.sqrt (d:ℝ)))
        = (1/Real.sqrt X) * ∑ d ∈ F, (1/Real.sqrt (d:ℝ)) := by
      rw [Finset.mul_sum]
    have hC : (∑ d ∈ F, (1/Real.sqrt (d:ℝ))) ≤ ∑ d ∈ r.divisors, (1/Real.sqrt (d:ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hFsub
      intro i hi hiF
      exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
    calc (∑ d ∈ F, ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ))
        ≤ ∑ d ∈ F, (1/Real.sqrt X) * (1/Real.sqrt (d:ℝ)) := hA
      _ = (1/Real.sqrt X) * ∑ d ∈ F, (1/Real.sqrt (d:ℝ)) := hB
      _ ≤ (1/Real.sqrt X) * ∑ d ∈ r.divisors, (1/Real.sqrt (d:ℝ)) :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ = (∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) / Real.sqrt X := by
          rw [one_div_mul_eq_div]
  · -- second conjunct
    set F := r.divisors.filter (fun d : ℕ => X < (d:ℝ)) with hF
    have hFsub : F ⊆ r.divisors := by rw [hF]; exact Finset.filter_subset _ _
    have hcore := divisorTail_core r hr
    have hA : (∑ d ∈ F, ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
        ≤ ∑ d ∈ F, (1/Real.sqrt X) *
            (((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [hF, Finset.mem_filter] at hd
      obtain ⟨hddiv, hdX⟩ := hd
      have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hddiv
      have hphi : (0:ℝ) < (Nat.totient d : ℝ) := by
        have : 0 < Nat.totient d := Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hddiv)
        exact_mod_cast this
      have hsd : Real.sqrt X ≤ Real.sqrt (d:ℝ) := Real.sqrt_le_sqrt (le_of_lt hdX)
      have hmnn : (0:ℝ) ≤ ((ArithmeticFunction.moebius d : ℝ))^2 := sq_nonneg _
      have hb : (1:ℝ)/(Nat.totient d : ℝ)
          ≤ Real.sqrt (d:ℝ) / ((Nat.totient d : ℝ) * Real.sqrt X) := by
        have heq : (1:ℝ)/(Nat.totient d : ℝ)
            = Real.sqrt X / ((Nat.totient d : ℝ) * Real.sqrt X) := by
          field_simp
        rw [heq]
        apply div_le_div_of_nonneg_right hsd
        positivity
      have hthis := mul_le_mul_of_nonneg_left hb hmnn
      have hrw : ((ArithmeticFunction.moebius d : ℝ))^2 *
            (Real.sqrt (d:ℝ) / ((Nat.totient d : ℝ) * Real.sqrt X))
          = (1/Real.sqrt X) *
            (((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ)) := by
        field_simp
      rw [← hrw]
      simpa [div_eq_mul_inv] using hthis
    have hB : (∑ d ∈ F, (1/Real.sqrt X) *
          (((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ)))
        = (1/Real.sqrt X) * ∑ d ∈ F,
          (((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ)) := by
      rw [Finset.mul_sum]
    have hnonneg : ∀ d ∈ r.divisors,
        0 ≤ ((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ) := by
      intro d hd
      apply div_nonneg
      · exact mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
      · have : 0 < Nat.totient d := Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hd)
        exact_mod_cast this.le
    have hC : (∑ d ∈ F,
          (((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ)))
        ≤ ∑ d ∈ r.divisors,
          (((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hFsub (fun i hi _ => hnonneg i hi)
    calc (∑ d ∈ F, ((ArithmeticFunction.moebius d : ℝ))^2 / (Nat.totient d : ℝ))
        ≤ ∑ d ∈ F, (1/Real.sqrt X) *
            (((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ)) := hA
      _ = (1/Real.sqrt X) * ∑ d ∈ F,
            (((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ)) := hB
      _ ≤ (1/Real.sqrt X) * ∑ d ∈ r.divisors,
            (((ArithmeticFunction.moebius d : ℝ))^2 * Real.sqrt (d:ℝ) / (Nat.totient d : ℝ)) :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ ≤ (1/Real.sqrt X) * (1000 * ∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 1000 * ((∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ)) / Real.sqrt X) := by
          field_simp

end Work.LinnikAreas.Density4
