import Mathlib
import Submission.Commons.NumberTheory.Moebius.sum_sq_truncated_eq_lcm_sum

namespace Work.ZeroDensity.Jutila

open scoped BigOperators

/-- Bilinear lcm reindexing: `Σ_{n≤N}(Σ_{d|n,d≤W}A d)(Σ_{e|n,e≤E}B e) = Σ_{d≤W,e≤E}A d·B e·⌊N/lcm(d,e)⌋`.
Route: rewrite each truncated divisor sum over all `d ≤ W` (resp. `e ≤ E`) with a divisibility indicator, expand the product, swap the two outer sums with the sum over `n`, and evaluate `#{n ≤ N : d|n ∧ e|n} = N / lcm(d,e)` via `Commons.NumberTheory.Moebius.card_filter_Icc_dvd_and_dvd` (import `Submission.Commons.NumberTheory.Moebius.sum_sq_truncated_eq_lcm_sum`). -/
theorem grahamBilinearReindex (W E : ℕ) (A B : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (∑ d ∈ n.divisors.filter (fun d => d ≤ W), A d) *
        (∑ e ∈ n.divisors.filter (fun e => e ≤ E), B e))
      = ∑ d ∈ Finset.Icc 1 W, ∑ e ∈ Finset.Icc 1 E,
          A d * B e * ((N / Nat.lcm d e : ℕ) : ℝ) := by
  classical
  -- rewrite the truncated divisor sums as unrestricted sums over `Icc 1 W` (resp. `Icc 1 E`)
  -- weighted by the divisibility indicator
  have hdivW : ∀ k ∈ Finset.Icc 1 N,
      k.divisors.filter (fun d => d ≤ W) = (Finset.Icc 1 W).filter (fun d => d ∣ k) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdvd, _⟩, hle⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), hle⟩, hdvd⟩
    · rintro ⟨⟨hd1, hle⟩, hdvd⟩
      exact ⟨⟨hdvd, by omega⟩, hle⟩
  have hdivE : ∀ k ∈ Finset.Icc 1 N,
      k.divisors.filter (fun e => e ≤ E) = (Finset.Icc 1 E).filter (fun e => e ∣ k) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hedvd, _⟩, hle⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hedvd (by omega), hle⟩, hedvd⟩
    · rintro ⟨⟨he1, hle⟩, hedvd⟩
      exact ⟨⟨hedvd, by omega⟩, hle⟩
  -- rewrite each inner sum with the divisibility indicator
  have hskW : ∀ k ∈ Finset.Icc 1 N,
      (∑ d ∈ k.divisors.filter (fun d => d ≤ W), A d)
        = ∑ d ∈ Finset.Icc 1 W, A d * (if d ∣ k then (1:ℝ) else 0) := by
    intro k hk
    rw [hdivW k hk, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : d ∣ k <;> simp [h]
  have hskE : ∀ k ∈ Finset.Icc 1 N,
      (∑ e ∈ k.divisors.filter (fun e => e ≤ E), B e)
        = ∑ e ∈ Finset.Icc 1 E, B e * (if e ∣ k then (1:ℝ) else 0) := by
    intro k hk
    rw [hdivE k hk, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : e ∣ k <;> simp [h]
  -- step 1: expand each product of inner sums
  have step1 : (∑ k ∈ Finset.Icc 1 N,
        (∑ d ∈ k.divisors.filter (fun d => d ≤ W), A d) *
        (∑ e ∈ k.divisors.filter (fun e => e ≤ E), B e))
      = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 W, ∑ e ∈ Finset.Icc 1 E,
          (A d * (if d ∣ k then (1:ℝ) else 0)) *
          (B e * (if e ∣ k then (1:ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hskW k hk, hskE k hk, Finset.sum_mul_sum]
  -- step 2: interchange the sums
  have step2 : (∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 W, ∑ e ∈ Finset.Icc 1 E,
          (A d * (if d ∣ k then (1:ℝ) else 0)) *
          (B e * (if e ∣ k then (1:ℝ) else 0)))
      = ∑ d ∈ Finset.Icc 1 W, ∑ e ∈ Finset.Icc 1 E, ∑ k ∈ Finset.Icc 1 N,
          (A d * (if d ∣ k then (1:ℝ) else 0)) *
          (B e * (if e ∣ k then (1:ℝ) else 0)) := by
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
  have hF : ∀ k, (A d * (if d ∣ k then (1:ℝ) else 0)) *
        (B e * (if e ∣ k then (1:ℝ) else 0))
      = A d * B e * (if d ∣ k ∧ e ∣ k then (1:ℝ) else 0) := by
    intro k
    by_cases h1 : d ∣ k <;> by_cases h2 : e ∣ k <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun k _ => hF k), ← Finset.mul_sum, Finset.sum_boole,
    Commons.NumberTheory.Moebius.card_filter_Icc_dvd_and_dvd N d e hd0 he0]

end Work.ZeroDensity.Jutila
