import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.NumberTheory.Moebius.sum_pairwise_divisors_moebius_totient_lcm_cpow

namespace Commons.NumberTheory.Moebius

open scoped BigOperators

/-- The number of integers `k` with `1 ≤ k ≤ x` divisible by both `d` and `e`
equals `⌊x / lcm d e⌋`, for `d, e > 0`. -/
theorem card_filter_Icc_dvd_and_dvd (x d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    ((Finset.Icc 1 x).filter (fun k => d ∣ k ∧ e ∣ k)).card = x / Nat.lcm d e := by
  classical
  set m : ℕ := Nat.lcm d e with hm
  have hmpos : 0 < m := by rw [hm]; exact Nat.lcm_pos hd he
  have hm1 : 1 ≤ m := hmpos
  have hset : (Finset.Icc 1 x).filter (fun k => d ∣ k ∧ e ∣ k)
      = (Finset.Icc 1 (x / m)).image (fun j => j * m) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha1, hax⟩, hdvd, hedvd⟩
      have hmvd : m ∣ a := by rw [hm]; exact Nat.lcm_dvd_iff.mpr ⟨hdvd, hedvd⟩
      obtain ⟨j, hj⟩ := hmvd
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; simp at hj; omega
        · exact h
      refine ⟨j, ⟨hj1, ?_⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le hmpos, mul_comm]
        omega
      · rw [hj, mul_comm]
    · rintro ⟨j, ⟨hj1, hjx⟩, rfl⟩
      have hjx' : j * m ≤ x := (Nat.le_div_iff_mul_le hmpos).mp hjx
      refine ⟨⟨?_, hjx'⟩, ?_, ?_⟩
      · have : 1 * 1 ≤ j * m := Nat.mul_le_mul hj1 hm1
        simpa using this
      · rw [hm]; exact (Nat.dvd_lcm_left d e).trans (dvd_mul_left m j)
      · rw [hm]; exact (Nat.dvd_lcm_right d e).trans (dvd_mul_left m j)
  rw [hset, Finset.card_image_of_injective _ (fun a b h => Nat.mul_right_cancel hmpos h)]
  rw [Nat.card_Icc]
  simp

theorem sum_sq_truncated_eq_lcm_sum (x V : ℕ) :
    (∑ k ∈ Finset.Icc 1 x,
        (∑ d ∈ k.divisors.filter (fun d => d ≤ V), (ArithmeticFunction.moebius d : ℝ)) ^ 2)
      = ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ)
            * ((x / Nat.lcm d e : ℕ) : ℝ) := by
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
      (∑ d ∈ k.divisors.filter (fun d => d ≤ V), (ArithmeticFunction.moebius d : ℝ)) ^ 2
      = ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          ((ArithmeticFunction.moebius d : ℝ) * (if d ∣ k then (1:ℝ) else 0))
          * ((ArithmeticFunction.moebius e : ℝ) * (if e ∣ k then (1:ℝ) else 0)) := by
    intro k hk
    have hsk : (∑ d ∈ k.divisors.filter (fun d => d ≤ V), (ArithmeticFunction.moebius d : ℝ))
        = ∑ d ∈ Finset.Icc 1 V,
            (ArithmeticFunction.moebius d : ℝ) * (if d ∣ k then (1:ℝ) else 0) := by
      rw [hdiv k hk, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases h : d ∣ k <;> simp [h]
    rw [hsk, pow_two, Finset.sum_mul_sum]
  -- step 1: expand each squared inner sum
  have step1 : (∑ k ∈ Finset.Icc 1 x,
        (∑ d ∈ k.divisors.filter (fun d => d ≤ V), (ArithmeticFunction.moebius d : ℝ)) ^ 2)
      = ∑ k ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          ((ArithmeticFunction.moebius d : ℝ) * (if d ∣ k then (1:ℝ) else 0))
          * ((ArithmeticFunction.moebius e : ℝ) * (if e ∣ k then (1:ℝ) else 0)) :=
    Finset.sum_congr rfl key
  -- step 2: interchange the sums
  have step2 : (∑ k ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
          ((ArithmeticFunction.moebius d : ℝ) * (if d ∣ k then (1:ℝ) else 0))
          * ((ArithmeticFunction.moebius e : ℝ) * (if e ∣ k then (1:ℝ) else 0)))
      = ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V, ∑ k ∈ Finset.Icc 1 x,
          ((ArithmeticFunction.moebius d : ℝ) * (if d ∣ k then (1:ℝ) else 0))
          * ((ArithmeticFunction.moebius e : ℝ) * (if e ∣ k then (1:ℝ) else 0)) := by
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
  have hF : ∀ k, ((ArithmeticFunction.moebius d : ℝ) * (if d ∣ k then (1:ℝ) else 0))
        * ((ArithmeticFunction.moebius e : ℝ) * (if e ∣ k then (1:ℝ) else 0))
      = (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ)
          * (if d ∣ k ∧ e ∣ k then (1:ℝ) else 0) := by
    intro k
    by_cases h1 : d ∣ k <;> by_cases h2 : e ∣ k <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun k _ => hF k), ← Finset.mul_sum, Finset.sum_boole,
    card_filter_Icc_dvd_and_dvd x d e hd0 he0]

end Commons.NumberTheory.Moebius