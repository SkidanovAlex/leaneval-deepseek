import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.subSieve_SharpNorm

/-!
# The auxiliary modulus `Qb u₀ = ∏_{p < ⌈u₀⌉₊, p prime} p`

`Qb u₀` dominates the `Q`-trick modulus `Qmod A u₀ = ∏_{p ∣ P, p < u₀} p`, and is small enough
that `log Qb = O(u₀²)`: this is what makes the shift `σ - σ'' ≤ log(2Q)/log z` of the `σ > 2`
case small once `z ≥ exp(10^6 (u₀+2)^2)`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.JR2

noncomputable section

/-- `Qb u₀ = ∏_{p < ⌈u₀⌉₊, p prime} p`: the product of all primes below `⌈u₀⌉₊`. -/
def Qb (u₀ : ℝ) : ℕ := ∏ p ∈ (Finset.range ⌈u₀⌉₊).filter (fun p : ℕ => p.Prime), p

theorem one_le_Qb (u₀ : ℝ) : 1 ≤ Qb u₀ := by
  rw [Qb]
  exact Finset.one_le_prod₀ (fun p hp => (Finset.mem_filter.mp hp).2.one_le)

theorem Qb_ne_zero (u₀ : ℝ) : Qb u₀ ≠ 0 := by
  have := one_le_Qb u₀; omega

/-- The `Q`-trick modulus is dominated by `Qb`: the primes of `P` below `u₀` are primes below
`⌈u₀⌉₊`. -/
theorem Qmod_le_Qb (A : BoundingSieve) (u₀ : ℝ) : Qmod A u₀ ≤ Qb u₀ := by
  rw [Qmod, Qb]
  refine Finset.prod_le_prod_of_subset_of_one_le₀ ?_ (fun p _ => by positivity) ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_range.mpr (by exact_mod_cast lt_of_lt_of_le hp.2 (Nat.le_ceil u₀)),
      Nat.prime_of_mem_primeFactors hp.1⟩
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_le

/-- `Qb u₀ ≤ ⌈u₀⌉₊ ^ ⌈u₀⌉₊`. -/
theorem Qb_le_pow (u₀ : ℝ) : Qb u₀ ≤ ⌈u₀⌉₊ ^ ⌈u₀⌉₊ := by
  rcases Nat.eq_zero_or_pos ⌈u₀⌉₊ with hn | hn
  · rw [Qb, hn]; simp
  · rw [Qb]
    have hcard : ((Finset.range ⌈u₀⌉₊).filter (fun p : ℕ => p.Prime)).card ≤ ⌈u₀⌉₊ := by
      have := Finset.card_le_card (Finset.filter_subset (fun p : ℕ => p.Prime)
        (Finset.range ⌈u₀⌉₊))
      simpa using this
    calc ∏ p ∈ (Finset.range ⌈u₀⌉₊).filter (fun p : ℕ => p.Prime), p
        ≤ ⌈u₀⌉₊ ^ ((Finset.range ⌈u₀⌉₊).filter (fun p : ℕ => p.Prime)).card :=
          Finset.prod_le_pow_card _ _ _
            (fun p hp => le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hp).1))
      _ ≤ ⌈u₀⌉₊ ^ ⌈u₀⌉₊ := Nat.pow_le_pow_right hn hcard

/-- `log (2 · Qb u₀) ≤ 2 (u₀+2)²` for `u₀ ≥ 2`. -/
theorem log_two_mul_Qb_le {u₀ : ℝ} (hu₀ : 2 ≤ u₀) :
    Real.log (2 * (Qb u₀ : ℝ)) ≤ 2 * (u₀ + 2) ^ 2 := by
  have hu₀0 : (0 : ℝ) < u₀ := by linarith
  set n : ℕ := ⌈u₀⌉₊ with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.one_le_ceil_iff.mpr hu₀0
  have hnpos : (0 : ℕ) < n := hn1
  have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnle : (n : ℝ) ≤ u₀ + 1 := by
    have := Nat.ceil_lt_add_one hu₀0.le
    rw [← hn] at this
    linarith
  have hQb1 : (1 : ℝ) ≤ (Qb u₀ : ℝ) := by exact_mod_cast one_le_Qb u₀
  have hQbpow : (Qb u₀ : ℝ) ≤ (n : ℝ) ^ n := by
    have := Qb_le_pow u₀
    rw [← hn] at this
    exact_mod_cast this
  have hlogn : Real.log (n : ℝ) ≤ u₀ := by
    have h1 : Real.log (n : ℝ) ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hnposR
    linarith
  have hlogQb : Real.log (Qb u₀ : ℝ) ≤ (n : ℝ) * u₀ := by
    have h2 : Real.log (Qb u₀ : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
      Real.log_le_log (by linarith) hQbpow
    rw [Real.log_pow] at h2
    calc Real.log (Qb u₀ : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := h2
      _ ≤ (n : ℝ) * u₀ := mul_le_mul_of_nonneg_left hlogn hnposR.le
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hQbne : (Qb u₀ : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (by norm_num) hQbne]
  calc Real.log 2 + Real.log (Qb u₀ : ℝ)
      ≤ 1 + (n : ℝ) * u₀ := add_le_add hlog2 hlogQb
    _ ≤ 1 + (u₀ + 1) * u₀ := by
        have : (n : ℝ) * u₀ ≤ (u₀ + 1) * u₀ := mul_le_mul_of_nonneg_right hnle hu₀0.le
        linarith
    _ ≤ 2 * (u₀ + 2) ^ 2 := by nlinarith

/-- **The `σ`-shift of the `Q`-trick.**  With `D'' = ⌊D/Q⌋` and `z ≥ exp(10^6 (u₀+2)²)`, if
`D ≥ 2 Qb u₀ + 2` then `log D/log z - log D''/log z ≤ 1/500000`. -/
theorem sigma_shift_le {A : BoundingSieve} {u₀ z D : ℝ} (hu₀ : 2 ≤ u₀)
    (hz : Real.exp (10 ^ 6 * (u₀ + 2) ^ 2) ≤ z) (hD : 2 * (Qb u₀ : ℝ) + 2 ≤ D) :
    Real.log D / Real.log z - Real.log ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z
      ≤ 1 / 500000 := by
  have hu₀0 : (0 : ℝ) < u₀ := by linarith
  have hz1 : (1 : ℝ) < z := by
    have h1 : (1 : ℝ) < Real.exp (10 ^ 6 * (u₀ + 2) ^ 2) := by
      rw [← Real.log_lt_iff_lt_exp (by norm_num)]
      have : (0 : ℝ) < 10 ^ 6 * (u₀ + 2) ^ 2 := by positivity
      have h2 : Real.log 1 = 0 := Real.log_one
      rw [h2]; exact this
    linarith
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz1
  have hlogzbig : 10 ^ 6 * (u₀ + 2) ^ 2 ≤ Real.log z := by
    have := Real.log_le_log (Real.exp_pos _) hz
    rwa [Real.log_exp] at this
  have hQle : Qmod A u₀ ≤ Qb u₀ := Qmod_le_Qb A u₀
  have hQ1 : 1 ≤ Qmod A u₀ := Nat.one_le_iff_ne_zero.mpr (Qmod_ne_zero A u₀)
  have hQpos : (0 : ℝ) < (Qmod A u₀ : ℝ) := by exact_mod_cast hQ1
  have hQleR : (Qmod A u₀ : ℝ) ≤ (Qb u₀ : ℝ) := by exact_mod_cast hQle
  have hDpos : (0 : ℝ) < D := by
    have h1 : (0 : ℝ) < 2 * (Qb u₀ : ℝ) + 2 := by
      have := one_le_Qb u₀
      have : (1 : ℝ) ≤ (Qb u₀ : ℝ) := by exact_mod_cast this
      linarith
    linarith
  set Q : ℕ := Qmod A u₀ with hQdef
  set D'' : ℕ := ⌊D / (Q : ℝ)⌋₊ with hD''def
  have hQpos' : (0 : ℝ) < (Q : ℝ) := by rw [hQdef]; exact hQpos
  have hQ1' : (1 : ℝ) ≤ (Q : ℝ) := by rw [hQdef]; exact_mod_cast hQ1
  have h2Q : 2 * (Q : ℝ) ≤ D := by
    have : (Q : ℝ) ≤ (Qb u₀ : ℝ) := by rw [hQdef]; exact hQleR
    linarith
  have hDQ_nn : 0 ≤ D / (Q : ℝ) := div_nonneg hDpos.le hQpos'.le
  have hD''le : (D'' : ℝ) ≤ D / (Q : ℝ) := by
    rw [hD''def]; exact Nat.floor_le hDQ_nn
  have hD''gt : D / (Q : ℝ) < (D'' : ℝ) + 1 := by
    rw [hD''def]; exact Nat.lt_floor_add_one _
  -- `Q * D'' ≥ D - Q`, hence `2 * Q * D'' ≥ D`
  have hQD'' : D - (Q : ℝ) ≤ (Q : ℝ) * (D'' : ℝ) := by
    have h1 : D / (Q : ℝ) - 1 < (D'' : ℝ) := by linarith [hD''gt]
    have h2 := mul_lt_mul_of_pos_left h1 hQpos'
    have h3 : (Q : ℝ) * (D / (Q : ℝ) - 1) = D - (Q : ℝ) := by
      field_simp
    rw [h3] at h2
    linarith
  have hDle2 : D ≤ 2 * (Q : ℝ) * (D'' : ℝ) := by linarith
  have hD''pos : (0 : ℝ) < (D'' : ℝ) := by
    have : D - (Q : ℝ) ≤ (Q : ℝ) * (D'' : ℝ) := hQD''
    nlinarith [hDpos, hQpos', this, h2Q]
  have hlog_le : Real.log D - Real.log (D'' : ℝ) ≤ Real.log (2 * (Q : ℝ)) := by
    have h2QD''pos : (0 : ℝ) < 2 * (Q : ℝ) * (D'' : ℝ) := by positivity
    have h1 : Real.log D ≤ Real.log (2 * (Q : ℝ) * (D'' : ℝ)) := Real.log_le_log hDpos hDle2
    rw [Real.log_mul (by positivity) (ne_of_gt hD''pos)] at h1
    linarith
  have hlog2Q_le : Real.log (2 * (Q : ℝ)) ≤ 2 * (u₀ + 2) ^ 2 := by
    refine le_trans (Real.log_le_log (by positivity) ?_) (log_two_mul_Qb_le hu₀)
    have : (2 : ℝ) * (Q : ℝ) ≤ 2 * (Qb u₀ : ℝ) := by
      have : (Q : ℝ) ≤ (Qb u₀ : ℝ) := by rw [hQdef]; exact hQleR
      linarith
    exact this
  have hmain : Real.log D - Real.log (D'' : ℝ) ≤ 2 * (u₀ + 2) ^ 2 := le_trans hlog_le hlog2Q_le
  have h3 : Real.log D / Real.log z - Real.log (D'' : ℝ) / Real.log z
      = (Real.log D - Real.log (D'' : ℝ)) / Real.log z := by ring
  rw [h3, div_le_iff₀ hlogz]
  have hkey : 2 * (u₀ + 2) ^ 2 ≤ (1 / 500000 : ℝ) * Real.log z := by
    have h1 := mul_le_mul_of_nonneg_left hlogzbig (by norm_num : (0:ℝ) ≤ 1/500000)
    have h2 : (1/500000 : ℝ) * (10^6 * (u₀+2)^2) = 2 * (u₀+2)^2 := by ring
    linarith [h1, h2.le, h2.ge]
  linarith [hmain, hkey]

end
end Work.ChenPlan.LinearSieve.JR2
