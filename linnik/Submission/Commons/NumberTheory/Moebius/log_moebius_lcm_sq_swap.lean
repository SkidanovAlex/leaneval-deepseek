import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Commons.NumberTheory.Moebius.sum_sq_truncated_eq_lcm_sum

namespace Commons.NumberTheory.Moebius

open scoped BigOperators

/-- General form of the "swap square of truncated divisor sums into a double sum
over the LCM" identity: for an arbitrary real weight `f`,

`∑_{k ≤ x} (∑_{d | k, d ≤ V} f d)^2 = ∑_{d ≤ V} ∑_{e ≤ V} f d · f e · ⌊x / lcm d e⌋`,

where the double sum on the right is read with real values and `⌊x / lcm d e⌋`
counts the integers `k ≤ x` divisible by both `d` and `e`. -/
theorem sum_sq_truncated_eq_lcm_sum_general (x V : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 x, (∑ d ∈ k.divisors.filter (fun d => d ≤ V), f d) ^ 2)
      = ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          f d * f e * ((x / Nat.lcm d e : ℕ) : ℝ) := by
  classical
  -- rewrite the truncated divisor sum as an unrestricted sum over `Icc 1 V`
  -- weighted by the divisibility indicator
  have hdiv : ∀ k ∈ Finset.Icc 1 x,
      k.divisors.filter (fun d => d ≤ V) = (Finset.Icc 1 V).filter (fun d => d ∣ k) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdvd, _⟩, hle⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), hle⟩, hdvd⟩
    · rintro ⟨⟨hd1, hle⟩, hdvd⟩
      exact ⟨⟨hdvd, by omega⟩, hle⟩
  -- the term-wise expansion of the square
  have key : ∀ k ∈ Finset.Icc 1 x,
      (∑ d ∈ k.divisors.filter (fun d => d ≤ V), f d) ^ 2
      = ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          (f d * (if d ∣ k then (1:ℝ) else 0))
          * (f e * (if e ∣ k then (1:ℝ) else 0)) := by
    intro k hk
    have hsk : (∑ d ∈ k.divisors.filter (fun d => d ≤ V), f d)
        = ∑ d ∈ Finset.Icc 1 V, f d * (if d ∣ k then (1:ℝ) else 0) := by
      rw [hdiv k hk, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases h : d ∣ k <;> simp [h]
    rw [hsk, pow_two, Finset.sum_mul_sum]
  -- step 1: expand each squared inner sum
  have step1 : (∑ k ∈ Finset.Icc 1 x,
        (∑ d ∈ k.divisors.filter (fun d => d ≤ V), f d) ^ 2)
      = ∑ k ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          (f d * (if d ∣ k then (1:ℝ) else 0))
          * (f e * (if e ∣ k then (1:ℝ) else 0)) :=
    Finset.sum_congr rfl key
  -- step 2: interchange the sums
  have step2 : (∑ k ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          (f d * (if d ∣ k then (1:ℝ) else 0))
          * (f e * (if e ∣ k then (1:ℝ) else 0)))
      = ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, ∑ k ∈ Finset.Icc 1 x,
          (f d * (if d ∣ k then (1:ℝ) else 0))
          * (f e * (if e ∣ k then (1:ℝ) else 0)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm]
  rw [step1, step2]
  -- step 3: evaluate the inner sum over `k`
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mem_Icc] at hd he
  have hd0 : 0 < d := by omega
  have he0 : 0 < e := by omega
  have hF : ∀ k, (f d * (if d ∣ k then (1:ℝ) else 0))
        * (f e * (if e ∣ k then (1:ℝ) else 0))
      = f d * f e * (if d ∣ k ∧ e ∣ k then (1:ℝ) else 0) := by
    intro k
    by_cases h1 : d ∣ k <;> by_cases h2 : e ∣ k <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun k _ => hF k), ← Finset.mul_sum, Finset.sum_boole,
    card_filter_Icc_dvd_and_dvd x d e hd0 he0]

theorem log_moebius_lcm_sq_swap (W N : ℕ) (hW : 1 ≤ W) :
    (Finset.Icc 1 N).sum (fun n : ℕ =>
        ((n.divisors.filter (fun d => d ≤ W)).sum
          (fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log ((W : ℝ) / (d : ℝ)))) ^ 2)
      = (Finset.Icc 1 W).sum (fun d : ℕ => (Finset.Icc 1 W).sum (fun e : ℕ =>
          ((ArithmeticFunction.moebius d : ℝ) * Real.log ((W : ℝ) / (d : ℝ)))
            * ((ArithmeticFunction.moebius e : ℝ) * Real.log ((W : ℝ) / (e : ℝ)))
            * (((N / Nat.lcm d e : ℕ) : ℝ)))) := by
  exact sum_sq_truncated_eq_lcm_sum_general N W
    (fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log ((W : ℝ) / (d : ℝ)))

end Commons.NumberTheory.Moebius