/-
  Companion paper, §9: the density-tail bound, the last input of (9.7).

  The density tail is `gtail(d,m) = ∑_{ν ≤ m} μ(ν)·(g([ν²,d]) − g̃(d)·g(ν²))` (S9g).  Once the
  two Euler-product identities (9.8)/(9.9) are known — i.e. the *full* sums

      `∑'_ν μ(ν)·g(ν²) = G`   and   `∑'_ν μ(ν)·g([ν²,d]) = g̃(d)·G`

  are equal — `gtail(d,m)` is (minus) the tail of the absolutely convergent series
  `∑ μ(ν)(g([ν²,d]) − g̃(d)g(ν²))`, hence `≪ 1/m`, which is smaller than any negative power of
  `log m`.  This file proves exactly that reduction; the identities themselves are
  `S9k.Gprod_eq_tsum` (9.8) and the corrected `NumberTheory/EulerProduct/tsum_moebius_lcm_eq` (9.9).
-/
import Mathlib
import Submission.ASP.S9g
import Submission.ASP.S9k
import Submission.Commons.Analysis.Hilbert.discrete_hilbert_transform_maximal_weak_type_one_hilbert

set_option maxHeartbeats 1000000

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- A series whose terms are `≪ 1/n²` on `n ≥ 1` is summable. -/
lemma summable_of_abs_le_inv_sq {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, 1 ≤ n → |f n| ≤ C / (n : ℝ) ^ 2) : Summable f := by
  have hsum1 : Summable (fun n : ℕ => C * (1 / ((n : ℝ) + 1) ^ 2)) := by
    have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ) < 2)
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr (hbase.mul_left C)
  have hsum' : Summable (fun n : ℕ => f (n + 1)) := by
    refine Summable.of_norm_bounded hsum1 (fun n => ?_)
    rw [Real.norm_eq_abs]
    have h1 : 1 ≤ n + 1 := Nat.le_add_left 1 n
    refine le_trans (hb (n + 1) h1) (le_of_eq ?_)
    push_cast
    rw [mul_one_div]
  exact (summable_nat_add_iff 1).mp hsum'

/-- Tail bound for a series with summand `≪ 1/n²`: the difference between the total sum and the
partial sum up to `m` is `≤ 2C/m`. -/
theorem abs_tsum_sub_sum_range_le {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, 1 ≤ n → |f n| ≤ C / (n : ℝ) ^ 2) (m : ℕ) (hm : 1 ≤ m) :
    |(∑' n : ℕ, f n) - ∑ n ∈ Finset.range (m + 1), f n| ≤ 2 * C / (m : ℝ) := by
  classical
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsum : Summable f := summable_of_abs_le_inv_sq hC hb
  have hgeo : ∀ N : ℕ, (∑ n ∈ Finset.Ico (m + 1) N, (1 / (n : ℝ) ^ 2))
      ≤ 2 / ((m : ℝ) + 1) := by
    intro N
    have h := Commons.Analysis.Hilbert.sum_inv_sq_le_of_ge (R := m + 1) (by omega)
      (t := Finset.Ico (m + 1) N) (fun d hd => (Finset.mem_Ico.mp hd).1)
    simpa [Nat.cast_add, Nat.cast_one] using h
  have htend : Filter.Tendsto
      (fun N : ℕ => |(∑ n ∈ Finset.range N, f n) - ∑ n ∈ Finset.range (m + 1), f n|)
      Filter.atTop (nhds |(∑' n : ℕ, f n) - ∑ n ∈ Finset.range (m + 1), f n|) :=
    (hsum.hasSum.tendsto_sum_nat.sub tendsto_const_nhds).abs
  refine le_of_tendsto htend ?_
  refine Filter.eventually_atTop.mpr ⟨m + 1, fun N hN => ?_⟩
  have hsplit : (∑ n ∈ Finset.range N, f n) - ∑ n ∈ Finset.range (m + 1), f n
      = ∑ n ∈ Finset.Ico (m + 1) N, f n := (Finset.sum_Ico_eq_sub f hN).symm
  rw [hsplit]
  calc |∑ n ∈ Finset.Ico (m + 1) N, f n|
      ≤ ∑ n ∈ Finset.Ico (m + 1) N, |f n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ico (m + 1) N, C * (1 / (n : ℝ) ^ 2) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        refine le_trans (hb n (by have := (Finset.mem_Ico.mp hn).1; omega)) (le_of_eq ?_)
        rw [mul_one_div]
    _ = C * ∑ n ∈ Finset.Ico (m + 1) N, (1 / (n : ℝ) ^ 2) := (Finset.mul_sum _ _ C).symm
    _ ≤ C * (2 / ((m : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hgeo N) hC
    _ ≤ 2 * C / (m : ℝ) := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) hm0]
        nlinarith

/-- `gtail` written as a sum over `range (m+1)` (the `ν = 0` term vanishes). -/
lemma gtail_eq_sum_range (g gtil : ℕ → ℝ) (d m : ℕ) :
    gtail g gtil d m
      = ∑ n ∈ Finset.range (m + 1),
          (ArithmeticFunction.moebius n : ℝ)
            * (g (Nat.lcm (n ^ 2) d) - gtil d * g (n ^ 2)) := by
  rw [gtail]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hx).2; omega)
  · intro x hx1 hx2
    have hx0 : x = 0 := by
      by_contra hne
      exact hx2 (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, by
        have := Finset.mem_range.mp hx1; omega⟩)
    rw [hx0]
    simp

/-- **Companion §9, the density-tail bound**: given the two Euler-product identities (9.8)/(9.9)
in the form `∑'_ν μ(ν)g(ν²) = G`, `∑'_ν μ(ν)g([ν²,d]) = g̃(d)·G`, and the `1/ν²` bounds for the
two summands, the density tail is `≤ 2(C₁ + |g̃(d)|C₂)/m`. -/
theorem gtail_le (g gtil : ℕ → ℝ) (d m : ℕ) (hm : 1 ≤ m) {G Gd C1 C2 : ℝ}
    (hG : (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * g (ν ^ 2)) = G)
    (hGd : (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * g (Nat.lcm (ν ^ 2) d)) = Gd)
    (hcons : Gd = gtil d * G) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hb1 : ∀ ν : ℕ, 1 ≤ ν → |g (Nat.lcm (ν ^ 2) d)| ≤ C1 / (ν : ℝ) ^ 2)
    (hb2 : ∀ ν : ℕ, 1 ≤ ν → |g (ν ^ 2)| ≤ C2 / (ν : ℝ) ^ 2) :
    |gtail g gtil d m| ≤ 2 * (C1 + |gtil d| * C2) / (m : ℝ) := by
  classical
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hA : Summable (fun ν : ℕ => (ArithmeticFunction.moebius ν : ℝ) * g (Nat.lcm (ν ^ 2) d)) :=
    summable_of_abs_le_inv_sq hC1 (fun n hn => by
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc |(ArithmeticFunction.moebius n : ℝ)| * |g (Nat.lcm (n ^ 2) d)|
          ≤ 1 * (C1 / (n : ℝ) ^ 2) :=
            mul_le_mul hmu (hb1 n hn) (abs_nonneg _) (by norm_num)
        _ = C1 / (n : ℝ) ^ 2 := one_mul _)
  have hB : Summable (fun ν : ℕ => (ArithmeticFunction.moebius ν : ℝ) * g (ν ^ 2)) :=
    summable_of_abs_le_inv_sq hC2 (fun n hn => by
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc |(ArithmeticFunction.moebius n : ℝ)| * |g (n ^ 2)|
          ≤ 1 * (C2 / (n : ℝ) ^ 2) :=
            mul_le_mul hmu (hb2 n hn) (abs_nonneg _) (by norm_num)
        _ = C2 / (n : ℝ) ^ 2 := one_mul _)
  have hsub := Summable.tsum_sub hA (hB.mul_left (gtil d))
  rw [tsum_mul_left] at hsub
  have hfull : (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ)
      * (g (Nat.lcm (ν ^ 2) d) - gtil d * g (ν ^ 2))) = 0 := by
    have h1 : (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ)
          * (g (Nat.lcm (ν ^ 2) d) - gtil d * g (ν ^ 2)))
        = ∑' ν : ℕ, ((ArithmeticFunction.moebius ν : ℝ) * g (Nat.lcm (ν ^ 2) d)
            - gtil d * ((ArithmeticFunction.moebius ν : ℝ) * g (ν ^ 2))) :=
      tsum_congr (fun ν => by ring)
    rw [h1, hsub, hG, hGd, hcons]
    ring
  have hb : ∀ ν : ℕ, 1 ≤ ν →
      |(ArithmeticFunction.moebius ν : ℝ)
        * (g (Nat.lcm (ν ^ 2) d) - gtil d * g (ν ^ 2))| ≤ (C1 + |gtil d| * C2) / (ν : ℝ) ^ 2 := by
    intro ν hν
    rw [abs_mul]
    have hmu : |(ArithmeticFunction.moebius ν : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h1 := hb1 ν hν
    have h2 := hb2 ν hν
    have hν2 : (0 : ℝ) < (ν : ℝ) ^ 2 := by positivity
    calc |(ArithmeticFunction.moebius ν : ℝ)| * |g (Nat.lcm (ν ^ 2) d) - gtil d * g (ν ^ 2)|
        ≤ 1 * (|g (Nat.lcm (ν ^ 2) d)| + |gtil d| * |g (ν ^ 2)|) := by
          refine mul_le_mul hmu ?_ (abs_nonneg _) (by norm_num)
          calc |g (Nat.lcm (ν ^ 2) d) - gtil d * g (ν ^ 2)|
              ≤ |g (Nat.lcm (ν ^ 2) d)| + |gtil d * g (ν ^ 2)| := abs_sub _ _
            _ = |g (Nat.lcm (ν ^ 2) d)| + |gtil d| * |g (ν ^ 2)| := by rw [abs_mul]
      _ = |g (Nat.lcm (ν ^ 2) d)| + |gtil d| * |g (ν ^ 2)| := by rw [one_mul]
      _ ≤ C1 / (ν : ℝ) ^ 2 + |gtil d| * (C2 / (ν : ℝ) ^ 2) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ = (C1 + |gtil d| * C2) / (ν : ℝ) ^ 2 := by ring
  rw [gtail_eq_sum_range]
  have h := abs_tsum_sub_sum_range_le (C := C1 + |gtil d| * C2)
    (add_nonneg hC1 (mul_nonneg (abs_nonneg _) hC2)) hb m hm
  rw [hfull, zero_sub] at h
  rwa [abs_neg] at h


end

end Submission.ASP
