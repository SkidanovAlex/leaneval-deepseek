import Mathlib
import Submission.Work.FIArea6.tau_small_divisor_localization
import Submission.Work.FIArea3.lemma_2_2

set_option maxHeartbeats 2000000

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators

/-- For a finite set of nonnegative reals, `∑ aᵢ² ≤ (∑ aᵢ)²` (all the cross terms in the
expansion of the square are nonnegative). -/
lemma sum_sq_le_sq_sum (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    s.sum (fun i => a i ^ 2) ≤ (s.sum a) ^ 2 := by
  have h1 : ∀ i ∈ s, a i ^ 2 ≤ a i * s.sum a := by
    intro i hi
    have hle : a i ≤ s.sum a := Finset.single_le_sum (fun j hj => ha j hj) hi
    calc a i ^ 2 = a i * a i := pow_two (a i)
      _ ≤ a i * s.sum a := mul_le_mul_of_nonneg_left hle (ha i hi)
  calc s.sum (fun i => a i ^ 2) ≤ s.sum (fun i => a i * s.sum a) := Finset.sum_le_sum h1
    _ = (s.sum a) * (s.sum a) := (Finset.sum_mul s a (s.sum a)).symm
    _ = (s.sum a) ^ 2 := (pow_two (s.sum a)).symm

/-- **The pointwise `τ`-localization.**  For squarefree `n ≥ 1`,
`τ(n) ≤ 4 ∑_{d ∣ n, d³ ≤ n} τ(d)³`.

From `Work.FIArea6.tau_small_divisor_localization` (`4^{ω(n)} ≤ 16 ∑_{d ∣ n, d³ ≤ n} τ(d)⁶`),
`τ(n) = 2^{ω(n)}` for squarefree `n`, taking square roots (`τ(n)² = 4^{ω(n)} ≤ 16 ∑ τ(d)⁶`),
and `√(∑ aᵢ²) ≤ ∑ aᵢ` for `aᵢ = τ(d)³ ≥ 0`. -/
theorem tau_divisors_cube_le (n : ℕ) (hn : 1 ≤ n) (hsf : Squarefree n) :
    ((n.divisors.card : ℕ) : ℝ)
      ≤ 4 * ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ≤ n),
          (((d.divisors.card : ℕ) : ℝ)) ^ 3 := by
  have hn0 : n ≠ 0 := by omega
  set k := n.primeFactors.card with hk
  set s := n.divisors.filter (fun d => d ^ 3 ≤ n) with hs
  set T : ℝ := ∑ d ∈ s, (((d.divisors.card : ℕ) : ℝ)) ^ 6 with hT
  set S : ℝ := ∑ d ∈ s, (((d.divisors.card : ℕ) : ℝ)) ^ 3 with hS
  have hnn : ∀ i : ℕ, (0 : ℝ) ≤ (((i.divisors.card : ℕ) : ℝ)) ^ 3 :=
    fun i => pow_nonneg (Nat.cast_nonneg i.divisors.card) 3
  -- `τ(n) = 2^{ω(n)}` for squarefree `n`, hence `τ(n)² = 4^{ω(n)}`.
  have hτ : (((n.divisors.card : ℕ) : ℝ)) = (2 : ℝ) ^ k := by
    rw [Work.FIArea3.tau_card_of_squarefree hsf, ← hk, Nat.cast_pow]
    norm_num
  have hτ2 : (((n.divisors.card : ℕ) : ℝ)) ^ 2 = (4 : ℝ) ^ k := by
    rw [hτ, ← pow_mul, show k * 2 = 2 * k by ring, pow_mul]
    norm_num
  -- The localized divisor given by the crux lemma.
  obtain ⟨d, _hdpos, hddvd, hd3, hineq⟩ := Work.FIArea6.tau_key_divisor n hn hsf
  have hmem : d ∈ s := by
    rw [hs, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hddvd, hn0⟩, hd3⟩
  -- `τ(d)⁶ = (τ(d)³)²` and the single term is bounded by the sum `T`.
  have hsingle : (((d.divisors.card : ℕ) : ℝ)) ^ 6 ≤ T := by
    have h2 : ((((d.divisors.card : ℕ) : ℝ)) ^ 3) ^ 2
        ≤ ∑ i ∈ s, ((((i.divisors.card : ℕ) : ℝ)) ^ 3) ^ 2 :=
      Finset.single_le_sum (fun i _ => pow_nonneg (hnn i) 2) hmem
    calc (((d.divisors.card : ℕ) : ℝ)) ^ 6
        = ((((d.divisors.card : ℕ) : ℝ)) ^ 3) ^ 2 := by ring
      _ ≤ ∑ i ∈ s, ((((i.divisors.card : ℕ) : ℝ)) ^ 3) ^ 2 := h2
      _ = ∑ i ∈ s, (((i.divisors.card : ℕ) : ℝ)) ^ 6 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = T := hT.symm
  -- `4^{ω(n)} ≤ 16 T`.
  have hineqT : (4 : ℝ) ^ k ≤ 16 * T := by
    have h1 : (4 : ℝ) ^ k ≤ 16 * (((d.divisors.card : ℕ) : ℝ)) ^ 6 := by
      rw [hk]; exact hineq
    linarith
  -- `T ≤ S²`, since `T = ∑ (τ(d)³)²` and the `τ(d)³` are nonnegative.
  have hTS : T ≤ S ^ 2 := by
    have h := sum_sq_le_sq_sum s (fun i => (((i.divisors.card : ℕ) : ℝ)) ^ 3) (fun i _ => hnn i)
    rw [hS]
    calc T = ∑ i ∈ s, (((i.divisors.card : ℕ) : ℝ)) ^ 6 := hT
      _ = ∑ i ∈ s, ((((i.divisors.card : ℕ) : ℝ)) ^ 3) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ ≤ (∑ i ∈ s, (((i.divisors.card : ℕ) : ℝ)) ^ 3) ^ 2 := h
  -- Hence `τ(n)² = 4^{ω(n)} ≤ 16 S² = (4S)²` and, taking square roots, `τ(n) ≤ 4S`.
  have hSnn : 0 ≤ 4 * S := by
    have h0 : (0 : ℝ) ≤ ∑ i ∈ s, (((i.divisors.card : ℕ) : ℝ)) ^ 3 :=
      Finset.sum_nonneg (fun i _ => hnn i)
    rw [hS]
    linarith
  have hx2 : (((n.divisors.card : ℕ) : ℝ)) ^ 2 ≤ (4 * S) ^ 2 := by
    rw [hτ2]
    calc (4 : ℝ) ^ k ≤ 16 * T := hineqT
      _ ≤ 16 * S ^ 2 := by linarith
      _ = (4 * S) ^ 2 := by ring
  have hfin : (((n.divisors.card : ℕ) : ℝ)) ≤ 4 * S := by
    have h2 := sq_le_sq.mp hx2
    rw [abs_of_nonneg (Nat.cast_nonneg n.divisors.card), abs_of_nonneg hSnn] at h2
    exact h2
  rw [hS, hs] at hfin
  exact hfin

end Work.FIRed6Axis
