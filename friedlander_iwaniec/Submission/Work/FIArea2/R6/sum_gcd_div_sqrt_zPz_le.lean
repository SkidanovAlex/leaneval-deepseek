import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.Count.sum_int_natAbs_le
import Submission.Commons.Data.Nat.gcd_eq_sum_totient_divisors_of_ne_zero

open Finset
open scoped BigOperators

namespace Work.FIArea2.R6

/-! ### Elementary ingredients

The proof of `sum_gcd_div_sqrt_zPz_le` runs through three elementary facts:

* `sum_inv_sqrt_Icc_le`: `∑_{k=1}^{N} 1/√k ≤ 2√N` (telescoping);
* `sum_multiples_inv_sqrt_Icc_le`: the multiples of `e ≥ 1` in `[1,S]` carry at most `2√S/e`
  of the weight `1/√n`;
* `sum_gcd_div_sqrt_eq`: the totient reindexing `gcd(g,d) = ∑_{e ∣ d, e ∣ g} φ(e)` of the
  `1/√g`-weighted sum.
-/

/-- `∑_{k=1}^{N} 1/√k ≤ 2√N`, by the telescoping termwise bound `1/√k ≤ 2(√k - √(k-1))`. -/
private lemma sum_inv_sqrt_Icc_le (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt (k : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hstep : 1 / Real.sqrt ((n : ℝ) + 1)
        ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1))]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity),
        sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ))]
    have hgoal : 2 * Real.sqrt (n : ℝ)
        + 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ))
        = 2 * Real.sqrt ((n : ℝ) + 1) := by ring
    linarith [ih, hstep, hgoal]

/-- For `e ≥ 1`, the sum of `1/√n` over the multiples of `e` inside `[1,S]`, written with an
indicator, is at most `2√S/e`. -/
private lemma sum_multiples_inv_sqrt_Icc_le (e S : ℕ) (he : 1 ≤ e) :
    ∑ n ∈ Finset.Icc 1 S, (if e ∣ n then (1 : ℝ) / Real.sqrt (n : ℝ) else 0)
      ≤ 2 * Real.sqrt (S : ℝ) / (e : ℝ) := by
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hene : (e : ℝ) ≠ 0 := ne_of_gt hepos
  have hterm : ∀ k : ℕ, (1 : ℝ) / Real.sqrt (((e * k : ℕ) : ℝ))
      = (1 / Real.sqrt ((e : ℝ))) * ((1 : ℝ) / Real.sqrt ((k : ℝ))) := by
    intro k
    have hcast : (((e * k : ℕ) : ℝ)) = (e : ℝ) * (k : ℝ) := by push_cast; ring
    rw [hcast, Real.sqrt_mul (le_of_lt hepos), div_mul_div_comm, one_mul]
  rw [← Finset.sum_filter]
  rw [← Work.FIArea2.image_mul_Icc_eq_filter (d := e) (X := S) he]
  rw [Finset.sum_image (fun a _ b _ hab => Nat.mul_left_cancel (by omega) hab)]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_le (S / e)) (by positivity)) ?_
  have hMdiv : S / e * e ≤ S := Nat.div_mul_le_self S e
  have hMe : (((S / e : ℕ)) : ℝ) * (e : ℝ) ≤ (S : ℝ) := by exact_mod_cast hMdiv
  calc (1 / Real.sqrt ((e : ℝ))) * (2 * Real.sqrt (((S / e : ℕ) : ℝ)))
      = 2 * Real.sqrt ((((S / e : ℕ)) : ℝ) * (e : ℝ)) / (e : ℝ) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (((S / e : ℕ)) : ℝ))]
        field_simp
        rw [Real.sq_sqrt (le_of_lt hepos)]
        ring
    _ ≤ 2 * Real.sqrt (S : ℝ) / (e : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hepos)
        linarith [Real.sqrt_le_sqrt hMe]

/-- The totient reindexing of the `1/√g`-weighted gcd sum: for `d ≥ 1`,
`∑_{1 ≤ g ≤ R} gcd(g,d)/√g = ∑_{e ∣ d} φ(e)·∑_{1 ≤ g ≤ R, e ∣ g} 1/√g`. -/
private lemma sum_gcd_div_sqrt_eq (d R : ℕ) (hd : 1 ≤ d) :
    ∑ g ∈ Finset.Icc 1 R, (Nat.gcd g d : ℝ) / Real.sqrt (g : ℝ)
      = ∑ e ∈ d.divisors, (Nat.totient e : ℝ)
          * (∑ g ∈ (Finset.Icc 1 R).filter (fun g => e ∣ g), (1 : ℝ) / Real.sqrt (g : ℝ)) := by
  have hd0 : d ≠ 0 := by omega
  have h1 : ∀ g : ℕ, (Nat.gcd g d : ℝ)
      = ∑ e ∈ d.divisors, (if e ∣ g then (Nat.totient e : ℝ) else 0) := by
    intro g
    rw [Commons.Data.Nat.gcd_eq_sum_totient_divisors_of_ne_zero (c := g) hd0,
      Finset.sum_filter]
    push_cast
    simp
  calc ∑ g ∈ Finset.Icc 1 R, (Nat.gcd g d : ℝ) / Real.sqrt (g : ℝ)
      = ∑ g ∈ Finset.Icc 1 R,
          (∑ e ∈ d.divisors, (if e ∣ g then (Nat.totient e : ℝ) else 0))
            / Real.sqrt (g : ℝ) := by
        simp_rw [h1]
    _ = ∑ g ∈ Finset.Icc 1 R, ∑ e ∈ d.divisors,
          (if e ∣ g then (Nat.totient e : ℝ) else 0) / Real.sqrt (g : ℝ) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.sum_div]
    _ = ∑ g ∈ Finset.Icc 1 R, ∑ e ∈ d.divisors,
          (if e ∣ g then (Nat.totient e : ℝ) / Real.sqrt (g : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [ite_div, zero_div]
    _ = ∑ e ∈ d.divisors, ∑ g ∈ Finset.Icc 1 R,
          (if e ∣ g then (Nat.totient e : ℝ) / Real.sqrt (g : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ e ∈ d.divisors, (Nat.totient e : ℝ)
          * (∑ g ∈ Finset.Icc 1 R,
              (if e ∣ g then (1 : ℝ) / Real.sqrt (g : ℝ) else 0)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        by_cases h : e ∣ g
        · rw [if_pos h, if_pos h, div_eq_mul_one_div]
        · rw [if_neg h, if_neg h, mul_zero]
    _ = ∑ e ∈ d.divisors, (Nat.totient e : ℝ)
          * (∑ g ∈ (Finset.Icc 1 R).filter (fun g => e ∣ g),
              (1 : ℝ) / Real.sqrt (g : ℝ)) := by
        simp_rw [Finset.sum_filter]

/-- `Σ_{v ∈ zPz S} gcd(|v|, c) / √|v| ≤ 4 √S τ(c)` for `c ≥ 1`, where
`zPz S = ([-S,S] : Finset ℤ) \ {0}` (from `Submission/Work/FIArea2/R6/BSBoxDefs.lean`).
Hint: `gcd(v, c) = Σ_{e ∣ c, e ∣ v} φ(e)`; the same identity is
`Commons.Data.Nat.gcd_eq_sum_totient_divisors_of_ne_zero` in
`Submission/Commons/Data/Nat/gcd_eq_sum_totient_divisors_of_ne_zero.lean` (importable as
`Submission.Commons.Data.Nat.gcd_eq_sum_totient_divisors_of_ne_zero`), or prove it directly from
`Nat.sum_totient`. For fixed `e ≥ 1` the non-zero multiples of `e` in `[-S,S]` are `± e k`,
`1 ≤ k ≤ S/e`, so the inner sum is `2 Σ_{k ≤ S/e} 1/√(e k) = (2/√e) Σ_{k ≤ S/e} 1/√k ≤ (2/√e) · 2 √(S/e)
= 4 √S / e`; here `Σ_{k=1}^{N} 1/√k ≤ 2 √N` follows from `1/√k ≤ 2(√k - √(k-1))` and telescoping.
Summing `φ(e) · 4 √S / e ≤ 4 √S τ(c)` uses `φ(e)/e ≤ 1`. -/
theorem sum_gcd_div_sqrt_zPz_le (c S : ℕ) (hc : 1 ≤ c) :
    ∑ v ∈ Work.FIArea2.R6.zPz S, (Nat.gcd v.natAbs c : ℝ) / Real.sqrt (v.natAbs : ℝ)
      ≤ 4 * Real.sqrt (S : ℝ) * (c.divisors.card : ℝ) := by
  -- Step 1: `v ↦ |v|` is two-to-one from `zPz S` onto `{1, …, S}`.
  have hred : ∑ v ∈ Work.FIArea2.R6.zPz S, (Nat.gcd v.natAbs c : ℝ) / Real.sqrt (v.natAbs : ℝ)
      ≤ 2 * ∑ n ∈ Finset.Icc 1 S, (Nat.gcd n c : ℝ) / Real.sqrt (n : ℝ) :=
    Work.FIArea2.Count.sum_int_natAbs_le S (fun n => (Nat.gcd n c : ℝ) / Real.sqrt (n : ℝ))
      (fun n => by positivity)
  -- Step 2: on the positive half, expand `gcd` over the divisors of `c` and use the
  -- multiplicity-`1` bound `∑_{e ∣ n ≤ S} 1/√n ≤ 2√S/e`.
  have hcore : ∑ n ∈ Finset.Icc 1 S, (Nat.gcd n c : ℝ) / Real.sqrt (n : ℝ)
      ≤ 2 * Real.sqrt (S : ℝ) * (c.divisors.card : ℝ) := by
    rw [sum_gcd_div_sqrt_eq c S hc]
    calc ∑ e ∈ c.divisors, (Nat.totient e : ℝ)
            * (∑ g ∈ (Finset.Icc 1 S).filter (fun g => e ∣ g), (1 : ℝ) / Real.sqrt (g : ℝ))
        ≤ ∑ e ∈ c.divisors, (Nat.totient e : ℝ) * (2 * Real.sqrt (S : ℝ) / (e : ℝ)) := by
          refine Finset.sum_le_sum fun e he => ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Finset.sum_filter]
          exact sum_multiples_inv_sqrt_Icc_le e S (Nat.pos_of_mem_divisors he)
      _ ≤ ∑ _e ∈ c.divisors, 2 * Real.sqrt (S : ℝ) := by
          refine Finset.sum_le_sum fun e he => ?_
          have hepos : (0 : ℝ) < (e : ℝ) := by
            exact_mod_cast (Nat.pos_of_mem_divisors he)
          have hφ : (Nat.totient e : ℝ) ≤ (e : ℝ) := by exact_mod_cast Nat.totient_le e
          have hdiv : (Nat.totient e : ℝ) / (e : ℝ) ≤ 1 :=
            div_le_one_of_le₀ hφ (le_of_lt hepos)
          calc (Nat.totient e : ℝ) * (2 * Real.sqrt (S : ℝ) / (e : ℝ))
              = 2 * Real.sqrt (S : ℝ) * ((Nat.totient e : ℝ) / (e : ℝ)) := by
                field_simp
            _ ≤ 2 * Real.sqrt (S : ℝ) * 1 := mul_le_mul_of_nonneg_left hdiv (by positivity)
            _ = 2 * Real.sqrt (S : ℝ) := by ring
      _ = 2 * Real.sqrt (S : ℝ) * (c.divisors.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  calc ∑ v ∈ Work.FIArea2.R6.zPz S, (Nat.gcd v.natAbs c : ℝ) / Real.sqrt (v.natAbs : ℝ)
      ≤ 2 * (2 * Real.sqrt (S : ℝ) * (c.divisors.card : ℝ)) := by linarith
    _ = 4 * Real.sqrt (S : ℝ) * (c.divisors.card : ℝ) := by ring

end Work.FIArea2.R6
