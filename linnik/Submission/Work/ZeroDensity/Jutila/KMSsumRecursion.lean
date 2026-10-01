import Mathlib
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.LinnikAreas.Density4.coprime_indicator_moebius
import Submission.Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- **The summand `μ(n)/κ(n)` is multiplicative on coprime factors.**  For any `d`, `m`,
`μ (d*m)/κ (d*m)` equals `(μ d/κ d)·(μ m/κ m)` when `d` and `m` are coprime, and `0` otherwise.
(Squarefreeness of `d` is not needed: if `d` and `m` are coprime the multiplicativity of `μ` and
`κ` applies, while if they share a prime `p` then `p ^ 2 ∣ d*m` and both sides vanish.) -/
lemma mu_div_kappa_mul (d m : ℕ) :
    (ArithmeticFunction.moebius (d * m) : ℝ) / kappa (d * m) =
      (if Nat.Coprime d m then ((ArithmeticFunction.moebius d : ℝ) / kappa d)
        * ((ArithmeticFunction.moebius m : ℝ) / kappa m) else 0) := by
  by_cases h : Nat.Coprime d m
  · have hmu : (ArithmeticFunction.moebius (d * m) : ℝ) =
        (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius m : ℝ) := by
      rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius h]
      push_cast
      ring
    rw [if_pos h, hmu, kappa_mul_of_coprime h, div_mul_div_comm]
  · have hsq : ¬ Squarefree (d * m) := by
      intro hsf
      obtain ⟨p, hp, hpd, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp (mul_dvd_mul hpd hpm)
    rw [if_neg h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- **Recursion for the `κ`-weighted coprime Möbius sum.**  For squarefree `t`,

    `Ssum x t = ∑_{e ∣ t} κ(e)⁻¹ · Ssum (⌊x/e⌋) e`,

where `Ssum x t = ∑_{r ≤ x, (r,t)=1} μ(r)/κ(r)`.  The coprimality indicator is expanded by
Möbius inversion (`[m ⊥ t] = ∑_{d ∣ t, d ∣ m} μ(d)`), the two sums are interchanged, and the
inner sum over the multiples of `d` is reindexed as `m = d·k`; on the coprime terms the summand
splits as `μ(d·k)/κ(d·k) = (μ d/κ d)·(μ k/κ k)`, and the remaining sum over `k` coprime to `d` is
`Ssum (⌊x/d⌋) d`.  Since `t` is squarefree all its divisors `d` are squarefree, so `μ(d)² = 1`
and the factor `μ(d)² /κ(d)` is `κ(d)⁻¹`. -/
theorem KMSsumRecursion (x t : ℕ) (ht : Squarefree t) :
    Ssum x t = ∑ e ∈ t.divisors, (kappa e)⁻¹ * Ssum (x / e) e := by
  have ht0 : t ≠ 0 := ht.ne_zero
  have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
  -- Step 1: expand the coprimality indicator and interchange the two sums.
  have hstep : Ssum x t = ∑ d ∈ t.divisors, ∑ m ∈ Finset.Icc 1 x,
      (if d ∣ m then (ArithmeticFunction.moebius d : ℝ) *
        ((ArithmeticFunction.moebius m : ℝ) / kappa m) else 0) := by
    rw [Ssum_eq_sum_if]
    calc ∑ m ∈ Finset.Icc 1 x,
            (if Nat.Coprime m t then (ArithmeticFunction.moebius m : ℝ) / kappa m else 0)
        = ∑ m ∈ Finset.Icc 1 x, ∑ d ∈ t.divisors,
            (if d ∣ m then (ArithmeticFunction.moebius d : ℝ) *
              ((ArithmeticFunction.moebius m : ℝ) / kappa m) else 0) :=
          Finset.sum_congr rfl (fun m _ =>
            Work.LinnikAreas.Density4.coprime_indicator_moebius m t ht1 _)
      _ = ∑ d ∈ t.divisors, ∑ m ∈ Finset.Icc 1 x,
            (if d ∣ m then (ArithmeticFunction.moebius d : ℝ) *
              ((ArithmeticFunction.moebius m : ℝ) / kappa m) else 0) := Finset.sum_comm
  rw [hstep]
  -- Step 2: evaluate the inner sum for each divisor `d` of `t`.
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ t := Nat.dvd_of_mem_divisors hd
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hdsf : Squarefree d := Squarefree.squarefree_of_dvd hdvd ht
  calc ∑ m ∈ Finset.Icc 1 x, (if d ∣ m then (ArithmeticFunction.moebius d : ℝ) *
          ((ArithmeticFunction.moebius m : ℝ) / kappa m) else 0)
      = (ArithmeticFunction.moebius d : ℝ) * ∑ m ∈ (Finset.Icc 1 x).filter (fun m => d ∣ m),
          ((ArithmeticFunction.moebius m : ℝ) / kappa m) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases h : d ∣ m <;> simp [h, mul_comm]
    _ = (ArithmeticFunction.moebius d : ℝ) * ∑ k ∈ Finset.Icc 1 (x / d),
          ((ArithmeticFunction.moebius (d * k) : ℝ) / kappa (d * k)) := by
        rw [Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex x d hd1
          (fun m => (ArithmeticFunction.moebius m : ℝ) / kappa m)]
    _ = (ArithmeticFunction.moebius d : ℝ) *
          (((ArithmeticFunction.moebius d : ℝ) / kappa d) * Ssum (x / d) d) := by
        congr 1
        have hS : Ssum (x / d) d = ∑ k ∈ Finset.Icc 1 (x / d),
            (if Nat.Coprime d k then (ArithmeticFunction.moebius k : ℝ) / kappa k else 0) := by
          rw [Ssum_eq_sum_if]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          by_cases h : Nat.Coprime d k
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (fun hc => h hc.symm)]
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [mu_div_kappa_mul d k]
        by_cases h : Nat.Coprime d k <;> simp [h]
    _ = (kappa d)⁻¹ * Ssum (x / d) d := by
        have hmusq : (ArithmeticFunction.moebius d : ℝ) ^ 2 = 1 := by
          have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsf
          have h' : (((ArithmeticFunction.moebius d) ^ 2 : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by rw [h]
          push_cast at h'
          simpa using h'
        have hkey : (ArithmeticFunction.moebius d : ℝ) *
            ((ArithmeticFunction.moebius d : ℝ) / kappa d) = (kappa d)⁻¹ := by
          field_simp
          rw [hmusq]
        rw [← mul_assoc, hkey]

end

end Work.ZeroDensity.Jutila
