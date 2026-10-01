import Mathlib
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.ZeroDensity.Jutila.DcInvSumDyadic
import Submission.Work.ZeroDensity.Jutila.ExpSumNegSqrtSqBound

namespace Work.ZeroDensity.Jutila

/-!
# The tail bound for the exponentially decaying envelope `Dc`

`Dc c x = exp(-(c * sqrt (log x)))` is the decay envelope of the Möbius/Kappa sums of the
development.  This file proves

`∑_{N ≤ m ≤ M} Dc c m * log (1 + 1/m) ≤ K (1 + 1/c)^2 Dc (c/2) N`,

uniformly in `c > 0` and in the range `N ≤ M`: the two powers of the envelope are bought by
splitting `Dc c m = Dc (c/2) m * Dc (c/2) m`, so that the whole extra cost is the
`log (1 + 1/m)`-weighted sum of `Dc (c/2)`, which is an `O(1)` ("harmonic mass") quantity
bounded dyadically by an exponential sum in `√(k log 2)`.

## Structure

* `Dc_eq_mul_self`, `log_one_add_inv_*`, `sum_Icc_le_sum_Icc_one`, `arith_tail_bound`:
  elementary reductions and arithmetic.
* `DcInvSumDyadic`: the `Dc`-weighted sum over `[1,M]` is at most the sum of the exponential
  factors `exp (-(d √(k log 2)))` over the dyadic blocks (proved separately).
* `ExpSumNegSqrtSqBound`: `∑_{k ≤ J} exp (-(a √k)) ≤ 10 + 10/a^2` (proved separately).
* `KMDcTailBound_aux`: the assembly of the two inputs.
-/

/-- `Dc c m` is the square of `Dc (c / 2) m`: the two halves of the exponent multiply. -/
lemma Dc_eq_mul_self (c : ℝ) (m : ℕ) : Dc c m = Dc (c / 2) m * Dc (c / 2) m := by
  have h : Real.exp (-(c * Real.sqrt (Real.log (m : ℝ))))
      = Real.exp (-((c / 2) * Real.sqrt (Real.log (m : ℝ))))
        * Real.exp (-((c / 2) * Real.sqrt (Real.log (m : ℝ)))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact h

lemma log_one_add_inv_nonneg (m : ℕ) : 0 ≤ Real.log (1 + 1 / (m : ℝ)) := by
  apply Real.log_nonneg
  have : (0 : ℝ) ≤ 1 / (m : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg m)
  linarith

lemma log_one_add_inv_le_inv (m : ℕ) : Real.log (1 + 1 / (m : ℝ)) ≤ 1 / (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h
    have hpos : 0 < 1 + 1 / (m : ℝ) := by
      have : (0 : ℝ) < 1 / (m : ℝ) := div_pos zero_lt_one hm
      linarith
    have := Real.log_le_sub_one_of_pos hpos
    linarith

/-- Comparison of a sum over `[N,M]` with the sum over `[1,M]`, for a nonnegative summand
vanishing at `0`. -/
lemma sum_Icc_le_sum_Icc_one {f : ℕ → ℝ} (h0 : f 0 = 0) (hnn : ∀ m, 0 ≤ f m)
    {N M : ℕ} (hNM : N ≤ M) :
    ∑ m ∈ Finset.Icc N M, f m ≤ ∑ m ∈ Finset.Icc 1 M, f m := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hset : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp [h0]
  · have hsub : Finset.Icc N M ⊆ Finset.Icc 1 M := by
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hnn m)

/-- Elementary arithmetic: `10 + 10/(d^2 L) ≤ (10 + 10/L) (1 + 1/d)^2` for `d, L > 0`. -/
lemma arith_tail_bound {d L : ℝ} (hd : 0 < d) (hL : 0 < L) :
    10 + 10 / (d ^ 2 * L) ≤ (10 + 10 / L) * (1 + 1 / d) ^ 2 := by
  have hu : (0 : ℝ) ≤ 1 / d := le_of_lt (div_pos zero_lt_one hd)
  have h1 : (10 : ℝ) ≤ 10 * (1 + 1 / d) ^ 2 := by
    have hsq : (0 : ℝ) ≤ (1 / d) ^ 2 := sq_nonneg _
    nlinarith
  have h2 : 10 / (d ^ 2 * L) ≤ (10 / L) * (1 + 1 / d) ^ 2 := by
    have heq : 10 / (d ^ 2 * L) = (10 / L) * (1 / d) ^ 2 := by
      field_simp
    rw [heq]
    have hmono : (1 / d) ^ 2 ≤ (1 + 1 / d) ^ 2 := by nlinarith [sq_nonneg (1 / d)]
    exact mul_le_mul_of_nonneg_left hmono (div_nonneg (by norm_num) hL.le)
  calc 10 + 10 / (d ^ 2 * L)
      ≤ 10 * (1 + 1 / d) ^ 2 + (10 / L) * (1 + 1 / d) ^ 2 := by linarith
    _ = (10 + 10 / L) * (1 + 1 / d) ^ 2 := by ring

/-- **Core assembly.**  The two analytic inputs are the dyadic decomposition of the
`Dc`-weighted reciprocal sum and the exponential-sum bound; everything else is done here. -/
theorem KMDcTailBound_aux
    (hDyadic : ∀ (d : ℝ), 0 < d → ∀ M : ℕ,
      (∑ m ∈ Finset.Icc 1 M, Dc d m / (m : ℝ))
        ≤ ∑ k ∈ Finset.range (Nat.log 2 M + 1),
            Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))))
    (hExp : ∀ (a : ℝ), 0 < a → ∀ J : ℕ,
      (∑ k ∈ Finset.range (J + 1), Real.exp (-(a * Real.sqrt (k : ℝ))))
        ≤ 10 + 10 / a ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 0 < c → ∀ N M : ℕ, N ≤ M →
      (∑ m ∈ Finset.Icc N M, Dc c m * Real.log (1 + 1 / (m : ℝ)))
        ≤ K * (1 + 1 / c) ^ 2 * Dc (c / 2) N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < 4 * (10 + 10 / Real.log 2) := by
    have h : 0 < 10 / Real.log 2 := div_pos (by norm_num) hlog2
    linarith
  refine ⟨4 * (10 + 10 / Real.log 2), hK, ?_⟩
  intro c hc N M hNM
  set d : ℝ := c / 2 with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  have hDcN : 0 < Dc d N := Dc_pos d N
  have hpoint : ∀ m ∈ Finset.Icc N M,
      Dc c m * Real.log (1 + 1 / (m : ℝ))
        ≤ (Dc d N * Dc d m) * Real.log (1 + 1 / (m : ℝ)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hanti : Dc d m ≤ Dc d N := Dc_antitone hd.le hm.1
    have hle : Dc c m ≤ Dc d N * Dc d m := by
      rw [Dc_eq_mul_self c m]
      exact mul_le_mul_of_nonneg_right hanti (Dc_pos d m).le
    exact mul_le_mul_of_nonneg_right hle (log_one_add_inv_nonneg m)
  have hstep1 : (∑ m ∈ Finset.Icc N M, Dc c m * Real.log (1 + 1 / (m : ℝ)))
      ≤ Dc d N * ∑ m ∈ Finset.Icc N M, Dc d m * Real.log (1 + 1 / (m : ℝ)) := by
    calc (∑ m ∈ Finset.Icc N M, Dc c m * Real.log (1 + 1 / (m : ℝ)))
        ≤ ∑ m ∈ Finset.Icc N M, (Dc d N * Dc d m) * Real.log (1 + 1 / (m : ℝ)) :=
          Finset.sum_le_sum hpoint
      _ = Dc d N * ∑ m ∈ Finset.Icc N M, Dc d m * Real.log (1 + 1 / (m : ℝ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun m _ => by ring)
  have hstep2 : Dc d N * ∑ m ∈ Finset.Icc N M, Dc d m * Real.log (1 + 1 / (m : ℝ))
      ≤ Dc d N * ∑ m ∈ Finset.Icc 1 M, Dc d m / (m : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hDcN.le
    calc ∑ m ∈ Finset.Icc N M, Dc d m * Real.log (1 + 1 / (m : ℝ))
        ≤ ∑ m ∈ Finset.Icc N M, Dc d m * (1 / (m : ℝ)) :=
          Finset.sum_le_sum (fun m _ =>
            mul_le_mul_of_nonneg_left (log_one_add_inv_le_inv m) (Dc_pos d m).le)
      _ = ∑ m ∈ Finset.Icc N M, Dc d m / (m : ℝ) :=
          Finset.sum_congr rfl (fun m _ => by ring)
      _ ≤ ∑ m ∈ Finset.Icc 1 M, Dc d m / (m : ℝ) :=
          sum_Icc_le_sum_Icc_one (by simp)
            (fun m => div_nonneg (Dc_pos d m).le (Nat.cast_nonneg m)) hNM
  have hstep3 : Dc d N * ∑ m ∈ Finset.Icc 1 M, Dc d m / (m : ℝ)
      ≤ Dc d N * ∑ k ∈ Finset.range (Nat.log 2 M + 1),
          Real.exp (-((d * Real.sqrt (Real.log 2)) * Real.sqrt (k : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hDcN.le
    calc ∑ m ∈ Finset.Icc 1 M, Dc d m / (m : ℝ)
        ≤ ∑ k ∈ Finset.range (Nat.log 2 M + 1),
            Real.exp (-(d * Real.sqrt ((k : ℝ) * Real.log 2))) := hDyadic d hd M
      _ = ∑ k ∈ Finset.range (Nat.log 2 M + 1),
            Real.exp (-((d * Real.sqrt (Real.log 2)) * Real.sqrt (k : ℝ))) := by
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          rw [Real.sqrt_mul (Nat.cast_nonneg k) (Real.log 2)]
          ring
  have hstep4 : Dc d N * (∑ k ∈ Finset.range (Nat.log 2 M + 1),
        Real.exp (-((d * Real.sqrt (Real.log 2)) * Real.sqrt (k : ℝ))))
      ≤ Dc d N * ((10 + 10 / Real.log 2) * (1 + 1 / d) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hDcN.le
    have ha : 0 < d * Real.sqrt (Real.log 2) := mul_pos hd (Real.sqrt_pos.mpr hlog2)
    have hsq : (d * Real.sqrt (Real.log 2)) ^ 2 = d ^ 2 * Real.log 2 := by
      rw [mul_pow, Real.sq_sqrt hlog2.le]
    calc ∑ k ∈ Finset.range (Nat.log 2 M + 1),
            Real.exp (-((d * Real.sqrt (Real.log 2)) * Real.sqrt (k : ℝ)))
        ≤ 10 + 10 / (d * Real.sqrt (Real.log 2)) ^ 2 := hExp _ ha (Nat.log 2 M)
      _ = 10 + 10 / (d ^ 2 * Real.log 2) := by rw [hsq]
      _ ≤ (10 + 10 / Real.log 2) * (1 + 1 / d) ^ 2 := arith_tail_bound hd hlog2
  have hstep5 : Dc d N * ((10 + 10 / Real.log 2) * (1 + 1 / d) ^ 2)
      ≤ Dc d N * ((10 + 10 / Real.log 2) * (4 * (1 + 1 / c) ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hDcN.le
    have hC : (0 : ℝ) ≤ 10 + 10 / Real.log 2 := by
      have h : 0 < 10 / Real.log 2 := div_pos (by norm_num) hlog2
      linarith
    apply mul_le_mul_of_nonneg_left _ hC
    have hdc : 1 + 1 / d = 1 + 2 / c := by rw [hd_def]; ring
    have hle : 1 + 1 / d ≤ 2 * (1 + 1 / c) := by
      rw [hdc]
      have : (2 : ℝ) * (1 + 1 / c) = 2 + 2 / c := by ring
      linarith
    have h1d : (0 : ℝ) ≤ 1 + 1 / d := by
      have : (0 : ℝ) ≤ 1 / d := le_of_lt (div_pos zero_lt_one hd)
      linarith
    have h2c : (0 : ℝ) ≤ 2 * (1 + 1 / c) := by positivity
    calc (1 + 1 / d) ^ 2
        = (1 + 1 / d) * (1 + 1 / d) := by ring
      _ ≤ (2 * (1 + 1 / c)) * (2 * (1 + 1 / c)) := mul_le_mul hle hle h1d h2c
      _ = 4 * (1 + 1 / c) ^ 2 := by ring
  calc (∑ m ∈ Finset.Icc N M, Dc c m * Real.log (1 + 1 / (m : ℝ)))
      ≤ Dc d N * ∑ m ∈ Finset.Icc N M, Dc d m * Real.log (1 + 1 / (m : ℝ)) := hstep1
    _ ≤ Dc d N * ∑ m ∈ Finset.Icc 1 M, Dc d m / (m : ℝ) := hstep2
    _ ≤ Dc d N * (∑ k ∈ Finset.range (Nat.log 2 M + 1),
          Real.exp (-((d * Real.sqrt (Real.log 2)) * Real.sqrt (k : ℝ)))) := hstep3
    _ ≤ Dc d N * ((10 + 10 / Real.log 2) * (1 + 1 / d) ^ 2) := hstep4
    _ ≤ Dc d N * ((10 + 10 / Real.log 2) * (4 * (1 + 1 / c) ^ 2)) := hstep5
    _ = 4 * (10 + 10 / Real.log 2) * (1 + 1 / c) ^ 2 * Dc (c / 2) N := by
        rw [← hd_def]; ring

/-- **Jutila (Linnik) tail bound for the envelope `Dc`.**  There is an absolute constant `K`
with
`∑_{N ≤ m ≤ M} Dc c m * log (1 + 1/m) ≤ K (1 + 1/c)^2 Dc (c/2) N`
for all `c > 0` and all `N ≤ M`. -/
theorem KMDcTailBound : ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 0 < c → ∀ N M : ℕ, N ≤ M →
    (∑ m ∈ Finset.Icc N M, Dc c m * Real.log (1 + 1 / (m : ℝ)))
      ≤ K * (1 + 1 / c) ^ 2 * Dc (c / 2) N :=
  KMDcTailBound_aux (fun d hd M => DcInvSumDyadic (d := d) hd M)
    (fun a ha J => ExpSumNegSqrtSqBound (a := a) ha J)

end Work.ZeroDensity.Jutila
