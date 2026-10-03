import Mathlib
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le

open Finset
open scoped BigOperators

namespace Work.FIArea2.R6

/-- `4 · (3 log 3 / log 2) ≤ 20`, since `3 ^ 12 < 2 ^ 20`. -/
lemma four_mul_three_log_div_log_two_le_twenty :
    4 * (3 * Real.log 3 / Real.log 2) ≤ (20 : ℝ) := by
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 12 * Real.log 3 < 20 * Real.log 2 := by
    have h1 : Real.log ((3 : ℝ) ^ 12) = 12 * Real.log 3 := by
      rw [Real.log_pow]; norm_num
    have h2 : Real.log ((2 : ℝ) ^ 20) = 20 * Real.log 2 := by
      rw [Real.log_pow]; norm_num
    rw [← h1, ← h2]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  rw [show (4 : ℝ) * (3 * Real.log 3 / Real.log 2) = 12 * Real.log 3 / Real.log 2 by ring]
  rw [div_le_iff₀ h2pos]
  linarith

/-- Real-arithmetic core: if `0 ≤ a`, `1 ≤ c` and `a ≤ (2c)^{3 log 3/log 2}` then
`a⁴ ≤ 2²⁰ · c²⁰`. -/
lemma tau4_pow_le_of_le_cuberoot_rpow {a c : ℝ} (ha : 0 ≤ a) (hc : 1 ≤ c)
    (h : a ≤ (2 * c) ^ ((3 : ℝ) * Real.log 3 / Real.log 2)) :
    a ^ 4 ≤ (2 : ℝ) ^ (20 : ℕ) * c ^ 20 := by
  have h2c1 : (1 : ℝ) ≤ 2 * c := by linarith
  have hKle : ((3 : ℝ) * Real.log 3 / Real.log 2) * ((4 : ℕ) : ℝ) ≤ ((20 : ℕ) : ℝ) := by
    have h4 := four_mul_three_log_div_log_two_le_twenty
    push_cast
    linarith
  calc a ^ 4 ≤ (((2 * c) ^ ((3 : ℝ) * Real.log 3 / Real.log 2)) ^ (4 : ℕ)) :=
        pow_le_pow_left₀ ha h 4
    _ = (2 * c) ^ (((3 : ℝ) * Real.log 3 / Real.log 2) * ((4 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast ((2 * c) ^ ((3 : ℝ) * Real.log 3 / Real.log 2)) 4,
            ← Real.rpow_mul (show (0 : ℝ) ≤ 2 * c by positivity)]
    _ ≤ (2 * c) ^ (((20 : ℕ)) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h2c1 hKle
    _ = (2 : ℝ) ^ (20 : ℕ) * c ^ 20 := by
        rw [Real.rpow_natCast (2 * c) 20, mul_pow]

/-- **Landreau's Lemma 2.2 at the cube root.**  For `m ≥ 1` there is a divisor `d ∣ m` with `d³ ≤ m` and `τ(m) ≤ (2τ(d))^{3 log 3/log 2}`, hence (raising to the 4th power, using `τ(d) ≥ 1` and `4·3·log 3/log 2 < 20`)

  `τ(m)^4 ≤ 2^20 · Σ_{d ∣ m, d³ ≤ m} τ(d)^20`.

This is the `k = 3` analogue of `tau4_le_sum_small_divisors'` in `R6/uboxSum_le_dsum.lean` (the `k = 2` case with exponent `8`), and it is what allows the small-divisor cutoff of the box estimate to be pushed from `d² ≤ |N|` to `d³ ≤ |N|`.

Proof: `Commons.NumberTheory.Divisors.small_divisor_tau_le` (in `Submission/Commons/NumberTheory/Divisors/small_divisor_tau_le.lean`) with `k := 3` gives `d ∣ m`, `d^3 ≤ m`, `τ(m) ≤ (2τ(d))^{3·log 3/log 2}`; raise to the 4th power, bound `(2τ(d))^{4·3log3/log2} ≤ 2^20 τ(d)^20` using `τ(d) ≥ 1` and `4·3·log 3/log 2 < 20`, and keep the single term `d` of the sum (`Finset.single_le_sum`). -/
theorem tau4_le_sum_cuberoot (m : ℕ) (hm : 1 ≤ m) :
    ((m.divisors.card : ℝ)) ^ 4
      ≤ (2 : ℝ) ^ (20 : ℕ) *
        ∑ d ∈ (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d ^ 3 ≤ m),
          ((d.divisors.card : ℝ)) ^ 20 := by
  obtain ⟨d, hdvd, hd3, hcard⟩ :=
    Commons.NumberTheory.Divisors.small_divisor_tau_le (k := 3) (n := m) (by norm_num) hm
  have hcard' : (m.divisors.card : ℝ)
      ≤ (2 * (d.divisors.card : ℝ)) ^ (3 * Real.log 3 / Real.log 2) := by
    simpa using hcard
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hm
  have hd0 : d ≠ 0 := by omega
  have hτd1 : (1 : ℝ) ≤ (d.divisors.card : ℝ) := by
    have h : 1 ≤ d.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hd0⟩
    exact_mod_cast h
  have hτm0 : (0 : ℝ) ≤ (m.divisors.card : ℝ) := Nat.cast_nonneg _
  have hstep : ((m.divisors.card : ℝ)) ^ 4
      ≤ (2 : ℝ) ^ (20 : ℕ) * ((d.divisors.card : ℝ)) ^ 20 :=
    tau4_pow_le_of_le_cuberoot_rpow hτm0 hτd1 hcard'
  have hmem : d ∈ (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d ^ 3 ≤ m) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hd1, Nat.le_of_dvd (by omega) hdvd⟩, hdvd, hd3⟩
  have hnn : ∀ e ∈ (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d ^ 3 ≤ m),
      0 ≤ ((e.divisors.card : ℝ)) ^ 20 := fun e _ => by positivity
  have hsingle := Finset.single_le_sum hnn hmem
  exact le_trans hstep (mul_le_mul_of_nonneg_left hsingle (by positivity))

end Work.FIArea2.R6
