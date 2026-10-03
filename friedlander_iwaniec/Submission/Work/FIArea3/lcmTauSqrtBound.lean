import Mathlib
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea3.sum_tau_pow_div_sqrt_le

set_option maxHeartbeats 800000

namespace Work.FIArea3

open Finset

/-- Elementary square-root identity: `√(x/y) · √x = x/√y` for `x ≥ 0`, `y > 0`. -/
lemma sqrt_div_mul_sqrt_self {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.sqrt (x / y) * Real.sqrt x = x / Real.sqrt y := by
  have h1 : Real.sqrt (x / y) * Real.sqrt x = Real.sqrt ((x / y) * x) :=
    (Real.sqrt_mul (div_nonneg hx hy.le) x).symm
  rw [h1]
  have h2 : (x / y) * x = x ^ 2 / y := by ring
  rw [h2, Real.sqrt_div (by positivity) y, Real.sqrt_sq hx]

/-- `τ` is bounded by its value on the product: `τ([d,e]) ≤ τ(d)·τ(e)`. -/
lemma card_divisors_lcm_le {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    ((Nat.lcm d e).divisors.card : ℝ) ≤ (d.divisors.card : ℝ) * (e.divisors.card : ℝ) := by
  have hde0 : d * e ≠ 0 := by positivity
  have hdl : Nat.lcm d e ∣ d * e := Nat.lcm_dvd (Nat.dvd_mul_right d e) (Nat.dvd_mul_left e d)
  have hsub : (Nat.lcm d e).divisors ⊆ (d * e).divisors := Nat.divisors_subset_of_dvd hde0 hdl
  have hcard : (Nat.lcm d e).divisors.card ≤ (d * e).divisors.card := Finset.card_le_card hsub
  have hmul : (d * e).divisors.card ≤ d.divisors.card * e.divisors.card := by
    rw [Nat.divisors_mul]; exact Finset.card_mul_le
  have h1 : ((Nat.lcm d e).divisors.card : ℝ) ≤ ((d * e).divisors.card : ℝ) := by
    exact_mod_cast hcard
  have h2 : (((d * e).divisors.card : ℕ) : ℝ) ≤ ((d.divisors.card * e.divisors.card : ℕ) : ℝ) := by
    exact_mod_cast hmul
  calc ((Nat.lcm d e).divisors.card : ℝ) ≤ ((d * e).divisors.card : ℝ) := h1
    _ ≤ ((d.divisors.card * e.divisors.card : ℕ) : ℝ) := h2
    _ = (d.divisors.card : ℝ) * (e.divisors.card : ℝ) := by push_cast; ring

/-- `√(√d)·√(√e) ≤ √(lcm d e)` for positive `d, e`. -/
lemma sqrt_sqrt_mul_le_sqrt_lcm {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    Real.sqrt (Real.sqrt (d : ℝ)) * Real.sqrt (Real.sqrt (e : ℝ))
      ≤ Real.sqrt ((Nat.lcm d e : ℕ) : ℝ) := by
  have hdl : d ≤ Nat.lcm d e := Nat.le_lcm_left d (by omega)
  have hel : e ≤ Nat.lcm d e := Nat.le_lcm_right e (by omega)
  have hdR : (d : ℝ) ≤ ((Nat.lcm d e : ℕ) : ℝ) := by exact_mod_cast hdl
  have heR : (e : ℝ) ≤ ((Nat.lcm d e : ℕ) : ℝ) := by exact_mod_cast hel
  have hsq : (d : ℝ) * (e : ℝ) ≤ ((Nat.lcm d e : ℕ) : ℝ) * ((Nat.lcm d e : ℕ) : ℝ) :=
    mul_le_mul hdR heR (Nat.cast_nonneg e) (Nat.cast_nonneg _)
  have hsqrt2 : Real.sqrt (d : ℝ) * Real.sqrt (e : ℝ) ≤ ((Nat.lcm d e : ℕ) : ℝ) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg d) (e : ℝ)]
    calc Real.sqrt ((d : ℝ) * (e : ℝ))
          ≤ Real.sqrt (((Nat.lcm d e : ℕ) : ℝ) * ((Nat.lcm d e : ℕ) : ℝ)) := Real.sqrt_le_sqrt hsq
      _ = ((Nat.lcm d e : ℕ) : ℝ) := Real.sqrt_mul_self (Nat.cast_nonneg _)
  have h1 : Real.sqrt (Real.sqrt (d : ℝ) * Real.sqrt (e : ℝ))
      ≤ Real.sqrt (((Nat.lcm d e : ℕ) : ℝ)) := Real.sqrt_le_sqrt hsqrt2
  have h2 : Real.sqrt (Real.sqrt (d : ℝ) * Real.sqrt (e : ℝ))
      = Real.sqrt (Real.sqrt (d : ℝ)) * Real.sqrt (Real.sqrt (e : ℝ)) :=
    Real.sqrt_mul (Real.sqrt_nonneg _) _
  rwa [h2] at h1

/-- The pointwise estimate
`τ(d)^8 τ(e)^8 τ([d,e])/√[d,e] ≤ (τ(d)^9/√√d)(τ(e)^9/√√e)`. -/
lemma lcm_term_le {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    ((d.divisors.card : ℝ)) ^ 8 * ((e.divisors.card : ℝ)) ^ 8
        * (((Nat.lcm d e).divisors.card : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ))
      ≤ (((d.divisors.card : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (d : ℝ)))
        * (((e.divisors.card : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (e : ℝ))) := by
  have htle := card_divisors_lcm_le hd he
  have hsqrt := sqrt_sqrt_mul_le_sqrt_lcm hd he
  have hsd_pos : 0 < Real.sqrt (Real.sqrt (d : ℝ)) * Real.sqrt (Real.sqrt (e : ℝ)) :=
    mul_pos (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < d by omega))))
            (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < e by omega))))
  have hkey : ((Nat.lcm d e).divisors.card : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ)
      ≤ ((d.divisors.card : ℝ) * (e.divisors.card : ℝ))
          / (Real.sqrt (Real.sqrt (d : ℝ)) * Real.sqrt (Real.sqrt (e : ℝ))) := by
    calc ((Nat.lcm d e).divisors.card : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ)
        ≤ ((d.divisors.card : ℝ) * (e.divisors.card : ℝ)) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right htle (Real.sqrt_nonneg _)
      _ ≤ ((d.divisors.card : ℝ) * (e.divisors.card : ℝ))
            / (Real.sqrt (Real.sqrt (d : ℝ)) * Real.sqrt (Real.sqrt (e : ℝ))) :=
          div_le_div_of_nonneg_left (by positivity) hsd_pos hsqrt
  calc ((d.divisors.card : ℝ)) ^ 8 * ((e.divisors.card : ℝ)) ^ 8
        * (((Nat.lcm d e).divisors.card : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ))
      ≤ ((d.divisors.card : ℝ)) ^ 8 * ((e.divisors.card : ℝ)) ^ 8
        * (((d.divisors.card : ℝ) * (e.divisors.card : ℝ))
            / (Real.sqrt (Real.sqrt (d : ℝ)) * Real.sqrt (Real.sqrt (e : ℝ)))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (((d.divisors.card : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (d : ℝ)))
        * (((e.divisors.card : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (e : ℝ))) := by
        rw [div_mul_div_comm]; ring

theorem lcmTauSqrtBound :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ,
      (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          (((d.divisors.card : ℕ) : ℝ) ^ (8 : ℕ)) * (((e.divisors.card : ℕ) : ℝ) ^ (8 : ℕ))
            * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ)))
        ≤ C * (K : ℝ) * Real.sqrt (K : ℝ) * (Real.log (K : ℝ) + 2) ^ (1024 : ℕ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FIArea2.sum_tau_pow_le 9
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FIArea3.sum_tau_pow_div_sqrt_le 9
  refine ⟨C1 * C2, mul_pos hC1pos hC2pos, ?_⟩
  intro K
  have hLnn : 0 ≤ Real.log (K : ℝ) + 2 := by
    have := Real.log_natCast_nonneg K; linarith
  have hStepA :
      (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          (((d.divisors.card : ℕ) : ℝ) ^ (8 : ℕ)) * (((e.divisors.card : ℕ) : ℝ) ^ (8 : ℕ))
            * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ)))
        ≤ (∑ d ∈ Finset.Icc 1 K,
            (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (d : ℝ))) ^ 2 := by
    calc _ ≤ ∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
              ((((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (d : ℝ)))
              * ((((e.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (e : ℝ))) := by
          apply Finset.sum_le_sum; intro d hd
          apply Finset.sum_le_sum; intro e he
          exact lcm_term_le (mem_Icc.mp hd).1 (mem_Icc.mp he).1
      _ = (∑ d ∈ Finset.Icc 1 K,
            (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (d : ℝ))) ^ 2 := by
          rw [sq, Finset.sum_mul_sum]
  have hStepB :
      (∑ d ∈ Finset.Icc 1 K,
          (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (d : ℝ))) ^ 2
        ≤ (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (d : ℝ))
          * (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9) := by
    have hCS : (∑ d ∈ Finset.Icc 1 K,
          (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (d : ℝ)))
        ≤ Real.sqrt (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (d : ℝ))
          * Real.sqrt (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9) := by
      have hsum_eq : ∑ n ∈ Icc 1 K,
            Real.sqrt ((((n.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (n : ℝ))
              * Real.sqrt ((((n.divisors.card : ℕ) : ℝ)) ^ 9)
          = ∑ d ∈ Icc 1 K,
              (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (d : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
        have hy : 0 < Real.sqrt (n : ℝ) :=
          Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
        exact sqrt_div_mul_sqrt_self (by positivity) hy
      rw [← hsum_eq]
      exact Real.sum_sqrt_mul_sqrt_le (Icc 1 K) (fun n => by positivity) (fun n => by positivity)
    have hS1nn : 0 ≤ ∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (d : ℝ) := by
      positivity
    have hS2nn : 0 ≤ ∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9 := by positivity
    calc (∑ d ∈ Finset.Icc 1 K,
            (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (Real.sqrt (d : ℝ))) ^ 2
        ≤ (Real.sqrt (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (d : ℝ))
            * Real.sqrt (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hCS 2
      _ = (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (d : ℝ))
          * (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9) := by
          rw [mul_pow, Real.sq_sqrt hS1nn, Real.sq_sqrt hS2nn]
  have hF : (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9 / Real.sqrt (d : ℝ))
      ≤ C2 * Real.sqrt (K : ℝ) * (Real.log (K : ℝ) + 2) ^ (2 ^ 9) := hC2 K
  have hG : (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ)) ^ 9)
      ≤ C1 * (K : ℝ) * (Real.log (K : ℝ) + 2) ^ (2 ^ 9) := hC1 K
  have hb : 0 ≤ C2 * Real.sqrt (K : ℝ) * (Real.log (K : ℝ) + 2) ^ (2 ^ 9) :=
    mul_nonneg (mul_nonneg hC2pos.le (Real.sqrt_nonneg _)) (pow_nonneg hLnn _)
  calc (∑ d ∈ Finset.Icc 1 K, ∑ e ∈ Finset.Icc 1 K,
          (((d.divisors.card : ℕ) : ℝ) ^ (8 : ℕ)) * (((e.divisors.card : ℕ) : ℝ) ^ (8 : ℕ))
            * ((((Nat.lcm d e).divisors.card : ℕ) : ℝ) / Real.sqrt ((Nat.lcm d e : ℕ) : ℝ)))
      ≤ _ := hStepA
    _ ≤ _ := hStepB
    _ ≤ (C2 * Real.sqrt (K : ℝ) * (Real.log (K : ℝ) + 2) ^ (2 ^ 9))
          * (C1 * (K : ℝ) * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)) :=
        mul_le_mul hF hG (by positivity) hb
    _ = C1 * C2 * (K : ℝ) * Real.sqrt (K : ℝ)
          * ((Real.log (K : ℝ) + 2) ^ (2 ^ 9) * (Real.log (K : ℝ) + 2) ^ (2 ^ 9)) := by
        ac_rfl
    _ = C1 * C2 * (K : ℝ) * Real.sqrt (K : ℝ) * (Real.log (K : ℝ) + 2) ^ (1024 : ℕ) := by
        rw [← pow_add, show (2 : ℕ) ^ 9 + 2 ^ 9 = (1024 : ℕ) by norm_num]

end Work.FIArea3
