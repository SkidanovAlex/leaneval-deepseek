import Mathlib
import Submission.Commons.NumberTheory.Sieve.vaughan_decomposition_real

namespace Commons.NumberTheory.ArithmeticFunction

open Finset

/-- `log m` splits into the truncated divisor sums below and above `z`. -/
private lemma log_eq_sum_ite (m : ℕ) (z : ℝ) :
    Real.log (((m : ℕ) : ℝ))
      = (∑ c ∈ m.divisors, (if ((c : ℕ) : ℝ) ≤ z then ArithmeticFunction.vonMangoldt c else 0))
        + (∑ c ∈ m.divisors, (if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0)) := by
  rw [← ArithmeticFunction.vonMangoldt_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : ((c : ℕ) : ℝ) ≤ z
  · simp [hc, not_lt.mpr hc]
  · simp [hc, lt_of_not_ge hc]

/-- The `z < c ≤ sz` and `sz < c` truncated sums add up to the `z < c` one. -/
private lemma sum_ite_split (m : ℕ) {z sz : ℝ} (hz : z ≤ sz) :
    (∑ c ∈ m.divisors,
        (if z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz then ArithmeticFunction.vonMangoldt c else 0))
      + (∑ c ∈ m.divisors, (if sz < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0))
    = ∑ c ∈ m.divisors, (if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : z < ((c : ℕ) : ℝ)
  · by_cases hcs : ((c : ℕ) : ℝ) ≤ sz
    · simp [hc, hcs, not_lt.mpr hcs]
    · simp [hc, hcs, lt_of_not_ge hcs]
  · have hcz : ((c : ℕ) : ℝ) ≤ z := le_of_not_gt hc
    have hszc : ¬ sz < ((c : ℕ) : ℝ) := not_lt.mpr (le_trans hcz hz)
    simp [hc, hszc]

/-- Combination of five sums over the same finset into a single sum. -/
private lemma combine5 {s : Finset ℕ} (f1 f2 f3 f4 f5 : ℕ → ℝ) :
    (∑ x ∈ s, f1 x) - (∑ x ∈ s, f2 x) + (∑ x ∈ s, f3 x)
      + (∑ x ∈ s, f4 x) + (∑ x ∈ s, f5 x)
      = ∑ x ∈ s, (f1 x - f2 x + f3 x + f4 x + f5 x) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]

/-- Per-`b` reduction of the five terms. -/
private lemma per_b (n b : ℕ) {y z sy sz : ℝ} (hy : y ≤ sy) (hz : z ≤ sz) :
    (if ((b : ℕ) : ℝ) ≤ y then
        (ArithmeticFunction.moebius b : ℝ) * Real.log (((n / b : ℕ) : ℝ)) else 0)
      - (if ((b : ℕ) : ℝ) ≤ y then
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (n / b).divisors, (if ((c : ℕ) : ℝ) ≤ z then ArithmeticFunction.vonMangoldt c else 0)
          else 0)
      + (if y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy then
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (n / b).divisors, (if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0)
          else 0)
      + (if sy < ((b : ℕ) : ℝ) then
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (n / b).divisors,
              (if z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz then ArithmeticFunction.vonMangoldt c else 0)
          else 0)
      + (if sy < ((b : ℕ) : ℝ) then
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ c ∈ (n / b).divisors, (if sz < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0)
          else 0)
    = (ArithmeticFunction.moebius b : ℝ) *
        ∑ c ∈ (n / b).divisors, (if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0) := by
  have hAB := log_eq_sum_ite (n / b) z
  have hB12 := sum_ite_split (n / b) (sz := sz) hz
  by_cases hb : ((b : ℕ) : ℝ) ≤ y
  · rw [if_pos hb, if_pos hb,
      if_neg (fun h => not_lt.mpr hb h.1),
      if_neg (not_lt.mpr (le_trans hb hy)),
      if_neg (not_lt.mpr (le_trans hb hy)),
      hAB]
    ring
  · have hb' : y < ((b : ℕ) : ℝ) := lt_of_not_ge hb
    by_cases hbsy : ((b : ℕ) : ℝ) ≤ sy
    · rw [if_neg hb, if_neg hb, if_pos ⟨hb', hbsy⟩, if_neg (not_lt.mpr hbsy),
        if_neg (not_lt.mpr hbsy)]
      ring
    · have hsyb : sy < ((b : ℕ) : ℝ) := lt_of_not_ge hbsy
      rw [if_neg hb, if_neg hb, if_neg (fun h => hbsy h.2), if_pos hsyb, if_pos hsyb]
      ring_nf
      rw [← mul_add, hB12]

theorem vonMangoldt_gt_vaughan_decomp (n : ℕ) (hn : 1 ≤ n) {y z sy sz : ℝ}
    (hy_sy : y ≤ sy) (hz_sz : z ≤ sz) :
    (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0)
      = (∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
            (ArithmeticFunction.moebius b : ℝ) * Real.log (((n / b : ℕ) : ℝ)))
        - (∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
            (ArithmeticFunction.moebius b : ℝ)
              * ∑ c ∈ (n / b).divisors.filter (fun c => ((c : ℕ) : ℝ) ≤ z),
                  ArithmeticFunction.vonMangoldt c)
        + (∑ b ∈ n.divisors.filter (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy),
            (ArithmeticFunction.moebius b : ℝ)
              * ∑ c ∈ (n / b).divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
                  ArithmeticFunction.vonMangoldt c)
        + (∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)
              * ∑ c ∈ (n / b).divisors.filter
                  (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
                  ArithmeticFunction.vonMangoldt c)
        + (∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)
              * ∑ c ∈ (n / b).divisors.filter (fun c => sz < ((c : ℕ) : ℝ)),
                  ArithmeticFunction.vonMangoldt c) := by
  have hn0 : 0 < n := by omega
  have hcombined :
      (∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
            (ArithmeticFunction.moebius b : ℝ) * Real.log (((n / b : ℕ) : ℝ)))
        - (∑ b ∈ n.divisors.filter (fun b => ((b : ℕ) : ℝ) ≤ y),
            (ArithmeticFunction.moebius b : ℝ)
              * ∑ c ∈ (n / b).divisors.filter (fun c => ((c : ℕ) : ℝ) ≤ z),
                  ArithmeticFunction.vonMangoldt c)
        + (∑ b ∈ n.divisors.filter (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy),
            (ArithmeticFunction.moebius b : ℝ)
              * ∑ c ∈ (n / b).divisors.filter (fun c => z < ((c : ℕ) : ℝ)),
                  ArithmeticFunction.vonMangoldt c)
        + (∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)
              * ∑ c ∈ (n / b).divisors.filter
                  (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
                  ArithmeticFunction.vonMangoldt c)
        + (∑ b ∈ n.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)
              * ∑ c ∈ (n / b).divisors.filter (fun c => sz < ((c : ℕ) : ℝ)),
                  ArithmeticFunction.vonMangoldt c)
      = ∑ b ∈ n.divisors, (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (n / b).divisors,
            (if z < ((c : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt c else 0)) := by
    simp only [Finset.sum_filter]
    rw [combine5]
    apply Finset.sum_congr rfl
    intro b _
    exact per_b n b hy_sy hz_sz
  rw [hcombined]
  simp_rw [Finset.mul_sum]
  exact (Commons.NumberTheory.Sieve.sum_mu_divisors_mul_truncated_real
    (f := ArithmeticFunction.vonMangoldt) hn0 z).symm

end Commons.NumberTheory.ArithmeticFunction
