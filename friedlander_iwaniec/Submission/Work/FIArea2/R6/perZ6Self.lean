import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.R6.pairFibre6Aux
import Submission.Work.FIArea7.coprime_gnorm_of_dvd_absDelta

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- **The coprimality restriction of the round-6 pair bracket is free.**  If `A` and `M` are
coprime, then every pair `(d₁, d₂)` with `d₁ ∣ A` and `d₂ ∣ M` automatically satisfies
`gcd(d₁,d₂) = 1`; hence the restricted double divisor sum dominates the product of the two single
divisor sums. -/
private lemma prod_sum_le_pair_sum (A M K1 K2 : ℕ) (hAM : Nat.Coprime A M) :
    (∑ d1 ∈ Finset.Icc 1 K1, (if d1 ∣ A then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))
      * (∑ d2 ∈ Finset.Icc 1 K2, (if d2 ∣ M then (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))
    ≤ ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
        (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ A ∧ d2 ∣ M
          then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
            * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun d1 _ => Finset.sum_le_sum fun d2 _ => ?_
  by_cases h1 : d1 ∣ A
  · by_cases h2 : d2 ∣ M
    · have hg : Nat.gcd d1 d2 = 1 := (hAM.coprime_dvd_left h1).coprime_dvd_right h2
      simp [h1, h2, hg]
    · simp [h1, h2]
  · simp [h1]

/-- The arithmetic core: for coprime `A, M` with `A ≤ K₁⁴`, `M ≤ K₂⁴`, the product `τ(A)²τ₃(M)`
is bounded by `2¹⁶·2¹⁶` times the restricted double divisor sum. -/
private lemma core (A M K1 K2 : ℕ) (hK1 : 1 ≤ K1) (hK2 : 1 ≤ K2)
    (hA : (A : ℝ) ≤ (K1 : ℝ) ^ (4 : ℕ)) (hM : (M : ℝ) ≤ (K2 : ℝ) ^ (4 : ℕ))
    (hAM : Nat.Coprime A M) :
    (((A.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ) * ((tau3 M : ℕ) : ℝ)
      ≤ 65536 * (65536 * ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ A ∧ d2 ∣ M
            then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0)) := by
  have hTA := tau_sq_le_sum_Icc_four A K1 hK1 hA
  have hTM := tau3_le_sum_Icc_four M K2 hK2 hM
  have hS := prod_sum_le_pair_sum A M K1 K2 hAM
  have htau3nn : (0 : ℝ) ≤ ((tau3 M : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul hTA hTM htau3nn (by positivity :
    (0 : ℝ) ≤ 65536 * ∑ d1 ∈ Finset.Icc 1 K1,
      (if d1 ∣ A then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))
  have hstep : (65536 * ∑ d1 ∈ Finset.Icc 1 K1,
        (if d1 ∣ A then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))
      * (65536 * ∑ d2 ∈ Finset.Icc 1 K2,
        (if d2 ∣ M then (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0))
      ≤ 65536 * (65536 * ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ A ∧ d2 ∣ M
            then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0)) := by
    nlinarith [hS]
  linarith [hmul, hstep]

/-- **The per-point bound of the round-6 pair bracket.**  For `z₁, z₂` primary with squarefree
norms and `|z₂|² > N ≥ 1`, and any `K₁, K₂ ≥ 1` with `|z₂|² ≤ K₁⁴`, `|Δ(z₁,z₂)| ≤ K₂⁴`,

  `[z₁ ⊥ z₂]·τ(|z₂|²)²·τ₃(|Δ(z₁,z₂)|) ≤ 2¹⁶·2¹⁶·∑_{d₁ ≤ K₁}∑_{d₂ ≤ K₂} [gcd(d₁,d₂)=1]·[d₁ | |z₂|²]·[d₂ | |Δ|]·τ(d₁)^16 τ(d₂)^16`,

where the two factors `τ(|z₂|²)²`, `τ₃(|Δ|)` are handled by `Work.FIArea2.R6.tau_sq_le_sum_Icc_four`
(at `K₁`) and `Work.FIArea2.R6.tau3_le_sum_Icc_four` (at `K₂`).  The coprimality restriction is
free: if `z₁ ⊥ z₂` in `ℤ[i]`, the two squarefreeness hypotheses make
`Work.FIArea7.coprime_gnorm_of_dvd_absDelta` applicable, so `d₁ | |z₂|²` together with `d₂ | |Δ|`
forces `gcd(d₁,d₂) = 1`; and `Δ = 0` is impossible in that case (applying it with `q = |z₂|²`
gives `Nat.Coprime |z₂|² |z₂|²`, whence `|z₂|² = 1`, against `|z₂|² > N ≥ 1`). -/
theorem perZ6Self (N : ℝ) (z1 z2 : GaussianInt) (K1 K2 : ℕ)
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hN1 : (1 : ℝ) ≤ N) (hgz2 : N < (Work.FIPlan.gnorm z2 : ℝ))
    (hK1 : 1 ≤ K1) (hK2 : 1 ≤ K2)
    (hgn : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (K1 : ℝ) ^ (4 : ℕ))
    (hΔ : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ (K2 : ℝ) ^ (4 : ℕ)) :
    Work.FIArea2.R6.copInd z1 z2 * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
        * ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ)
      ≤ 65536 * (65536 * ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
          (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
            then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
              * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0)) := by
  have hApos : 0 < Work.FIPlan.gnorm z2 := by
    have : (0 : ℝ) < (Work.FIPlan.gnorm z2 : ℝ) := by linarith
    exact_mod_cast this
  have hAge2 : 2 ≤ Work.FIPlan.gnorm z2 := by
    have hge1 : (1 : ℝ) < (Work.FIPlan.gnorm z2 : ℝ) := lt_of_le_of_lt hN1 hgz2
    have : 1 < Work.FIPlan.gnorm z2 := by exact_mod_cast hge1
    omega
  by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
  · -- `z₁ ⊥ z₂`: the coprimality restriction on the divisor pair is automatic.
    have hci : copInd z1 z2 = 1 := by simp [copInd, hcop]
    rw [hci, one_mul]
    have hAM : Nat.Coprime (Work.FIPlan.gnorm z2) (Work.FIPlan.absDelta z1 z2) := by
      rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with hM0 | hMpos
      · -- `|Δ| = 0` is impossible: `q = |z₂|²` would give `|z₂|² ⊥ |z₂|²`.
        exfalso
        have hq : Work.FIPlan.gnorm z2 ∣ Work.FIPlan.absDelta z1 z2 := by
          rw [hM0]; exact dvd_zero _
        have hcc := Work.FIArea7.coprime_gnorm_of_dvd_absDelta
          (q := Work.FIPlan.gnorm z2) hApos hP1 hP2 hs1 hs2 hcop hq
        have hA1 : Work.FIPlan.gnorm z2 = 1 := (Nat.coprime_self _).mp hcc
        omega
      · exact Work.FIArea7.coprime_gnorm_of_dvd_absDelta
          (q := Work.FIPlan.absDelta z1 z2) hMpos hP1 hP2 hs1 hs2 hcop (dvd_refl _)
    exact core (Work.FIPlan.gnorm z2) (Work.FIPlan.absDelta z1 z2) K1 K2 hK1 hK2 hgn hΔ hAM
  · -- `z₁, z₂` not coprime: the indicator vanishes.
    have hci : copInd z1 z2 = 0 := by simp [copInd, hcop]
    rw [hci, zero_mul, zero_mul]
    have hSnn : (0 : ℝ) ≤ ∑ d1 ∈ Finset.Icc 1 K1, ∑ d2 ∈ Finset.Icc 1 K2,
        (if Nat.gcd d1 d2 = 1 ∧ d1 ∣ Work.FIPlan.gnorm z2 ∧ d2 ∣ Work.FIPlan.absDelta z1 z2
          then (((d1.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)
            * (((d2.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ) else 0) :=
      Finset.sum_nonneg fun d1 _ => Finset.sum_nonneg fun d2 _ => by split_ifs <;> positivity
    nlinarith [hSnn]

end Work.FIArea2.R6
