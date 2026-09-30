/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mean-square bound for the inverse of a power series on a circle of radius `ρ < 1/2`

Let `a : ℕ → ℂ` satisfy `a 0 = 1` and `‖a n‖ ≤ 1` for all `n`, and let

`F(z) = ∑_{e} a e * z ^ e`

be the associated power series (absolutely convergent for `‖z‖ < 1`).  We write
`invCoeff a n` for the coefficients of the inverse power series `1/F`, so that
`(∑ e, a e * z^e) * (∑ n, invCoeff a n * z^n) = 1`.  Since `‖invCoeff a n‖ ≤ 2 ^ n`
(the trivial Cauchy-product bound, with `a 0 = 1` and `‖a n‖ ≤ 1`), for `0 < ρ < 1/2`
and `z = ρ e^{iθ}` we get

`(∑ e, a e * z^e)⁻¹ = ∑ n, invCoeff a n * z^n`,

whence, expanding in the orthonormal family `θ ↦ e^{i n θ}` on `[0, 2π]`,

`∫_0^{2π} ‖(∑ e, a e * (ρ e^{iθ})^e)⁻¹‖^2 dθ ≤ 2π / (1 - 2ρ)`.

The main result of this file is precisely this bound, stated as
`Work.BMF.mrlas.powerSeries_circle_inv_L2`.
-/

namespace Work.BMF.mrlas

open Finset MeasureTheory

noncomputable section

/-! ## 1. The coefficients of the inverse power series -/

/-- `invCoeff a n` is the `n`-th coefficient of the inverse of the power series
`1 + ∑_{e ≥ 1} a e * z^e`, defined by the recurrence
`invCoeff a 0 = 1` and `invCoeff a (n+1) = - ∑_{e ≤ n} a (e+1) * invCoeff a (n - e)`. -/
def invCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  match n with
  | 0 => 1
  | (k+1) => -∑ e ∈ Finset.range (k+1), a (e+1) * invCoeff a (k - e)
termination_by n
decreasing_by
  all_goals (try simp_all)

@[simp] lemma invCoeff_zero (a : ℕ → ℂ) : invCoeff a 0 = 1 := by simp only [invCoeff]

lemma invCoeff_succ (a : ℕ → ℂ) (k : ℕ) :
    invCoeff a (k+1) = -∑ e ∈ Finset.range (k+1), a (e+1) * invCoeff a (k - e) := by
  simp only [invCoeff]

/-- The defining convolution identity for `invCoeff`: for `a 0 = 1`,
`∑_{e ≤ n} a e * invCoeff a (n - e) = [n = 0]`. -/
lemma invCoeff_conv (a : ℕ → ℂ) (ha : a 0 = 1) (n : ℕ) :
    ∑ e ∈ Finset.range (n+1), a e * invCoeff a (n - e) = if n = 0 then 1 else 0 := by
  rcases n with _ | k
  · simp [ha]
  · rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [ha, one_mul]
    have hsum : (∑ e ∈ Finset.range (k+1), a (e+1) * invCoeff a (k - e))
        = - invCoeff a (k+1) := by
      rw [invCoeff_succ]; abel
    rw [hsum]
    simp

/-- `∑_{j < m} 2^j ≤ 2^m`; the geometric-series estimate used for the inverse coefficients. -/
lemma sum_range_two_pow_le (m : ℕ) : ∑ j ∈ Finset.range m, (2:ℝ)^j ≤ 2^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

/-- The norm of a nonnegative real, viewed as a complex number. -/
lemma norm_complex_ofReal (r : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  simpa using abs_of_nonneg hr

/-- The trivial bound on the coefficients of the inverse power series:
if `‖a n‖ ≤ 1` then `‖invCoeff a n‖ ≤ 2^n`. -/
lemma invCoeff_bound (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (n : ℕ) : ‖invCoeff a n‖ ≤ 2^n := by
  refine Nat.strong_induction_on n (fun n ih => ?_)
  rcases n with _ | k
  · simp
  · rw [invCoeff_succ, norm_neg]
    calc ‖∑ e ∈ Finset.range (k+1), a (e+1) * invCoeff a (k - e)‖
        ≤ ∑ e ∈ Finset.range (k+1), ‖a (e+1) * invCoeff a (k - e)‖ := norm_sum_le _ _
      _ ≤ ∑ e ∈ Finset.range (k+1), (2:ℝ)^(k - e) := by
          refine Finset.sum_le_sum (fun e he => ?_)
          simp only [Finset.mem_range] at he
          rw [norm_mul]
          calc ‖a (e+1)‖ * ‖invCoeff a (k - e)‖ ≤ 1 * (2:ℝ)^(k - e) :=
                mul_le_mul (ha (e+1)) (ih (k - e) (by omega)) (norm_nonneg _) zero_le_one
            _ = (2:ℝ)^(k - e) := one_mul _
      _ = ∑ j ∈ Finset.range (k+1), (2:ℝ)^j := by
          rw [← Finset.sum_range_reflect (fun j => (2:ℝ)^j) (k+1)]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          simp only [Finset.mem_range] at hj
          congr 1
      _ ≤ (2:ℝ)^(k+1) := sum_range_two_pow_le (k+1)

/-! ## 2. Summability of the two power series and the Cauchy product identity -/

lemma summable_norm_mul_pow (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => ‖a n * z^n‖) := by
  refine Summable.of_norm_bounded (g := fun n => ‖z‖^n)
    (summable_geometric_of_lt_one (norm_nonneg z) hz) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n) (ha n)

lemma summable_norm_invCoeff_pow (a : ℕ → ℂ) (hb : ∀ n, ‖invCoeff a n‖ ≤ 2^n) {z : ℂ}
    (hz : ‖z‖ * 2 < 1) : Summable (fun n => ‖invCoeff a n * z^n‖) := by
  have h2z : 0 ≤ 2 * ‖z‖ := by positivity
  have hlt : 2 * ‖z‖ < 1 := by linarith
  refine Summable.of_norm_bounded (g := fun n => (2 * ‖z‖)^n)
    (summable_geometric_of_lt_one h2z hlt) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, norm_pow]
  calc ‖invCoeff a n‖ * ‖z‖^n ≤ 2^n * ‖z‖^n :=
        mul_le_mul_of_nonneg_right (hb n) (pow_nonneg (norm_nonneg z) n)
    _ = (2 * ‖z‖)^n := (mul_pow 2 ‖z‖ n).symm

/-- The Cauchy-product (power-series inverse) identity: for `‖z‖ < 1/2`,
the product of `∑ e, a e * z^e` with the inverse power series is `1`. -/
lemma tsum_mul_tsum_invCoeff (a : ℕ → ℂ) (ha0 : a 0 = 1) (ha : ∀ n, ‖a n‖ ≤ 1)
    (hb : ∀ n, ‖invCoeff a n‖ ≤ 2^n) {z : ℂ} (hz : ‖z‖ * 2 < 1) :
    (∑' e, a e * z^e) * (∑' n, invCoeff a n * z^n) = 1 := by
  have hz1 : ‖z‖ < 1 := by linarith [norm_nonneg z]
  have hf : Summable (fun n => ‖a n * z^n‖) := summable_norm_mul_pow a ha hz1
  have hg : Summable (fun n => ‖invCoeff a n * z^n‖) := summable_norm_invCoeff_pow a hb hz
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg]
  have hterm : ∀ n, (∑ k ∈ Finset.range (n+1), (a k * z^k) * (invCoeff a (n-k) * z^(n-k)))
      = (if n = 0 then 1 else 0) * z^n := by
    intro n
    have h1 : ∀ k ∈ Finset.range (n+1), (a k * z^k) * (invCoeff a (n-k) * z^(n-k))
        = (a k * invCoeff a (n-k)) * z^n := by
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [show (a k * z^k) * (invCoeff a (n-k) * z^(n-k))
            = (a k * invCoeff a (n-k)) * (z^k * z^(n-k)) by ring]
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, invCoeff_conv a ha0 n]
  rw [tsum_congr hterm, tsum_eq_single 0 (fun b' hb' => by simp [hb'])]
  simp

/-- The inverse of the power series is the power series with coefficients `invCoeff a`. -/
lemma inv_tsum_eq (a : ℕ → ℂ) (ha0 : a 0 = 1) (ha : ∀ n, ‖a n‖ ≤ 1)
    (hb : ∀ n, ‖invCoeff a n‖ ≤ 2^n) {z : ℂ} (hz : ‖z‖ * 2 < 1) :
    (∑' e, a e * z^e)⁻¹ = ∑' n, invCoeff a n * z^n :=
  inv_eq_of_mul_eq_one_right (tsum_mul_tsum_invCoeff a ha0 ha hb hz)

/-! ## 3. Orthogonality on `[0, 2π]` and Parseval for trigonometric polynomials -/

/-- The exponential monomial `θ ↦ exp (k θ i)`. -/
def trigExp (k : ℤ) (θ : ℝ) : ℂ := Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)

lemma trigExp_add (k l : ℤ) (θ : ℝ) : trigExp (k + l) θ = trigExp k θ * trigExp l θ := by
  simp only [trigExp, ← Complex.exp_add]; congr 1; push_cast; ring

lemma trigExp_conj (k : ℤ) (θ : ℝ) : (starRingEnd ℂ) (trigExp k θ) = trigExp (-k) θ := by
  rw [trigExp, ← Complex.exp_conj, trigExp]
  congr 1
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  push_cast
  ring

/-- The orthogonality relation `∫_0^{2π} exp (k θ i) dθ = 2π [k = 0]`. -/
lemma integral_trigExp (k : ℤ) :
    (∫ θ in (0)..(2 * Real.pi), trigExp k θ)
      = if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [ite_eq_left rfl]
    simp only [trigExp, Int.cast_zero, zero_mul, Complex.exp_zero]
    rw [intervalIntegral.integral_const]
    simp
  · rw [ite_eq_right hk]
    have hc : (k : ℂ) * Complex.I ≠ 0 := by simp [hk]
    have h1 : trigExp k = fun θ : ℝ => Complex.exp (((k : ℂ) * Complex.I) * (θ : ℂ)) := by
      funext θ; simp only [trigExp]; ring_nf
    rw [h1, integral_exp_mul_complex hc]
    have hexp : Complex.exp (((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have h := Complex.exp_int_mul_two_pi_mul_I k
      convert h using 2
      push_cast
      ring
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, hexp]
    ring

/-- Parseval's identity in complex form for a trigonometric polynomial. -/
lemma integral_trigpoly_complex (c : ℕ → ℂ) (N : ℕ) :
    (∫ θ in (0)..(2*Real.pi),
        (∑ n ∈ Finset.range N, c n * trigExp n θ)
          * (starRingEnd ℂ (∑ n ∈ Finset.range N, c n * trigExp n θ)))
      = ((2*Real.pi * ∑ n ∈ Finset.range N, ‖c n‖^2 : ℝ) : ℂ) := by
  have hpt : ∀ θ : ℝ, (∑ n ∈ Finset.range N, c n * trigExp n θ)
        * (starRingEnd ℂ (∑ n ∈ Finset.range N, c n * trigExp n θ))
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (c n * (starRingEnd ℂ) (c m)) * trigExp ((n:ℤ) - m) θ := by
    intro θ
    simp only [map_sum, map_mul, trigExp_conj]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    rw [show (c n * trigExp (n:ℤ) θ) * ((starRingEnd ℂ) (c m) * trigExp (-(m:ℤ)) θ)
        = (c n * (starRingEnd ℂ) (c m)) * (trigExp (n:ℤ) θ * trigExp (-(m:ℤ)) θ) by ring]
    rw [← trigExp_add]
    ring_nf
  rw [intervalIntegral.integral_congr fun θ _ => hpt θ]
  have hInt : (∫ θ in (0)..(2*Real.pi),
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (c n * (starRingEnd ℂ) (c m)) * trigExp ((n:ℤ)-m) θ)
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (c n * (starRingEnd ℂ) (c m)) * (if (n:ℤ)-m = 0 then ((2*Real.pi:ℝ):ℂ) else 0) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun m hm => ?_
        rw [intervalIntegral.integral_const_mul, integral_trigExp]
      · intro m hm
        have hcont : Continuous (fun θ : ℝ => c n * (starRingEnd ℂ) (c m) * trigExp ((n:ℤ)-m) θ) := by
          simp only [trigExp]; fun_prop
        exact hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2*Real.pi)
    · intro n hn
      have hcont : Continuous (fun θ : ℝ =>
          ∑ m ∈ Finset.range N, c n * (starRingEnd ℂ) (c m) * trigExp ((n:ℤ)-m) θ) := by
        simp only [trigExp]; fun_prop
      exact hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2*Real.pi)
  rw [hInt]
  have hdiag : (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (c n * (starRingEnd ℂ) (c m)) * (if (n:ℤ)-m = 0 then ((2*Real.pi:ℝ):ℂ) else 0))
      = ∑ n ∈ Finset.range N, (c n * (starRingEnd ℂ) (c n)) * ((2*Real.pi:ℝ):ℂ) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      have hne : ((n:ℤ) - m) ≠ 0 := by
        simp only [Finset.mem_range] at hm hn
        omega
      simp [hne]
    · intro hn'; exact absurd hn hn'
  rw [hdiag]
  trans ∑ n ∈ Finset.range N, (((2*Real.pi:ℝ):ℂ) * ((‖c n‖^2 : ℝ) : ℂ))
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    ring
  · rw [← Finset.mul_sum, ← Complex.ofReal_sum, ← Complex.ofReal_mul]

/-- **Parseval's identity** for the trigonometric polynomial
`θ ↦ ∑_{n < N} c n * exp (n θ i)` on `[0, 2π]`. -/
lemma trigpoly_L2_identity (c : ℕ → ℂ) (N : ℕ) :
    (∫ θ in (0)..(2*Real.pi),
        ‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2)
      = 2*Real.pi * ∑ n ∈ Finset.range N, ‖c n‖^2 := by
  apply Complex.ofReal_inj.mp
  rw [← intervalIntegral.integral_ofReal]
  trans ∫ θ in (0)..(2*Real.pi),
      (∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I))
        * (starRingEnd ℂ (∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)))
  · refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  · simpa only [trigExp, Int.cast_natCast] using integral_trigpoly_complex c N

/-! ## 4. Passing to the limit: dominated convergence -/

/-- If the partial sums `θ ↦ ∑_{n < N} c n * exp (n θ i)` all have `L²`-norm square at most `B`
on `[0, 2π]`, the same holds for the full (absolutely convergent) series. -/
lemma tsum_exp_L2_bound (c : ℕ → ℂ) (hc : Summable fun n => ‖c n‖) (B : ℝ)
    (hB : ∀ N, (∫ θ in (0)..(2*Real.pi),
        ‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2) ≤ B) :
    (∫ θ in (0)..(2*Real.pi),
        ‖∑' n, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2) ≤ B := by
  set M : ℝ := ∑' n, ‖c n‖ with hM
  have hMnn : 0 ≤ M := tsum_nonneg (fun n => norm_nonneg _)
  have hExp_norm : ∀ (n : ℕ) (θ : ℝ), ‖Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖ = 1 := by
    intro n θ
    rw [Complex.norm_exp]
    have hre : ((n : ℂ) * (θ : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  have hsummable : ∀ θ : ℝ, Summable (fun n => c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)) := by
    intro θ
    refine Summable.of_norm_bounded hc (fun n => ?_)
    rw [norm_mul, hExp_norm n θ, mul_one]
  have hlim : ∀ θ : ℝ, Filter.Tendsto
      (fun N : ℕ => ‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2)
      Filter.atTop (nhds (‖∑' n, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2)) := by
    intro θ
    exact ((hsummable θ).hasSum.tendsto_sum_nat).norm.pow 2
  have hbound : ∀ (N : ℕ) (θ : ℝ),
      ‖‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2‖ ≤ M^2 := by
    intro N θ
    have h1 : ‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖ ≤ M := by
      calc ‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖
          ≤ ∑ n ∈ Finset.range N, ‖c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.range N, ‖c n‖ := by
            refine Finset.sum_congr rfl (fun n hn => ?_)
            rw [norm_mul, hExp_norm n θ, mul_one]
        _ ≤ M := by
            rw [hM]
            exact Summable.sum_le_tsum _ (fun i hi => norm_nonneg _) hc
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hDCT : Filter.Tendsto
      (fun N : ℕ => ∫ θ in (0)..(2*Real.pi),
        ‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2)
      Filter.atTop
      (nhds (∫ θ in (0)..(2*Real.pi),
        ‖∑' n, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := Filter.atTop) (a := (0:ℝ)) (b := 2*Real.pi)
      (F := fun N θ => ‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2)
      (f := fun θ => ‖∑' n, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2)
      (bound := fun _ => M^2) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall (fun N => (by fun_prop : Continuous (fun θ : ℝ =>
        ‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2)).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun N => Filter.Eventually.of_forall (fun θ _ => hbound N θ))
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun θ _ => hlim θ)
  exact le_of_tendsto' hDCT hB

/-! ## 5. The main theorem -/

theorem powerSeries_circle_inv_L2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ), a 0 = 1 → (∀ n, ‖a n‖ ≤ 1) → ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 →
      (∫ θ in (0)..(2 * Real.pi),
        ‖(∑' e : ℕ, a e * (ρ * Complex.exp (θ * Complex.I)) ^ e)⁻¹‖ ^ 2) ≤ C / (1 - 2 * ρ) := by
  refine ⟨4 * Real.pi, by positivity, ?_⟩
  intro a ha0 ha ρ hρ0 hρ
  set c : ℕ → ℂ := fun n => invCoeff a n * (ρ : ℂ)^n with hc_def
  have hbnd : ∀ n, ‖invCoeff a n‖ ≤ 2^n := invCoeff_bound a ha
  have h2ρ : 2 * ρ < 1 := by linarith
  have h4ρ : 4 * ρ^2 < 1 := by nlinarith
  have hcn : ∀ n, ‖c n‖ ≤ (2*ρ)^n := by
    intro n
    rw [hc_def, norm_mul, Complex.norm_pow, norm_complex_ofReal ρ hρ0.le]
    calc ‖invCoeff a n‖ * ρ^n ≤ 2^n * ρ^n :=
          mul_le_mul_of_nonneg_right (hbnd n) (pow_nonneg hρ0.le n)
      _ = (2*ρ)^n := (mul_pow 2 ρ n).symm
  have hpoint : ∀ θ : ℝ,
      ‖(∑' e : ℕ, a e * (ρ * Complex.exp (θ * Complex.I))^e)⁻¹‖^2
        = ‖∑' n, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2 := by
    intro θ
    set z : ℂ := (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz_def
    have hzn : ‖z‖ = ρ := by
      rw [hz_def, norm_mul, Complex.norm_exp]
      have hre : ((θ : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
      rw [hre, Real.exp_zero, mul_one, norm_complex_ofReal ρ hρ0.le]
    have hz2 : ‖z‖ * 2 < 1 := by rw [hzn]; linarith
    have hsum : (∑' n, invCoeff a n * z^n)
        = ∑' n, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I) := by
      refine tsum_congr (fun n => ?_)
      rw [hc_def, hz_def, mul_pow, ← Complex.exp_nat_mul]
      ring_nf
    rw [inv_tsum_eq a ha0 ha hbnd hz2, hsum]
  have hc : Summable (fun n => ‖c n‖) := by
    refine Summable.of_norm_bounded (g := fun n => (2*ρ)^n)
      (summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ 2*ρ) h2ρ) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hcn n
  have hpartial : ∀ N, (∫ θ in (0)..(2*Real.pi),
        ‖∑ n ∈ Finset.range N, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2)
      ≤ 2*Real.pi/(1-4*ρ^2) := by
    intro N
    rw [trigpoly_L2_identity c N]
    have hterm : ∀ n, ‖c n‖^2 ≤ (4*ρ^2)^n := by
      intro n
      calc ‖c n‖^2 ≤ ((2*ρ)^n)^2 := pow_le_pow_left₀ (norm_nonneg _) (hcn n) 2
        _ = (4*ρ^2)^n := by
            rw [← pow_mul, mul_comm n 2, pow_mul, show (4:ℝ)*ρ^2 = (2*ρ)^2 by ring]
    have hsum_le : ∑ n ∈ Finset.range N, ‖c n‖^2 ≤ ∑' n, (4*ρ^2)^n := by
      refine le_trans (Finset.sum_le_sum (fun n hn => hterm n)) ?_
      exact Summable.sum_le_tsum _ (fun i hi => pow_nonneg (by positivity) i)
        (summable_geometric_of_lt_one (by positivity) h4ρ)
    calc 2*Real.pi * ∑ n ∈ Finset.range N, ‖c n‖^2
        ≤ 2*Real.pi * ∑' n, (4*ρ^2)^n :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = 2*Real.pi * (1-4*ρ^2)⁻¹ := by rw [tsum_geometric_of_lt_one (by positivity) h4ρ]
      _ = 2*Real.pi/(1-4*ρ^2) := by rw [div_eq_mul_inv]
  have hmain : (∫ θ in (0)..(2*Real.pi),
        ‖∑' n, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2) ≤ 2*Real.pi/(1-4*ρ^2) :=
    tsum_exp_L2_bound c hc (2*Real.pi/(1-4*ρ^2)) hpartial
  calc (∫ θ in (0)..(2*Real.pi),
        ‖(∑' e : ℕ, a e * (ρ * Complex.exp (θ * Complex.I))^e)⁻¹‖^2)
      = ∫ θ in (0)..(2*Real.pi),
          ‖∑' n, c n * Complex.exp ((n:ℂ)*(θ:ℂ)*Complex.I)‖^2 :=
        intervalIntegral.integral_congr fun θ _ => hpoint θ
    _ ≤ 2*Real.pi/(1-4*ρ^2) := hmain
    _ ≤ 4*Real.pi/(1-2*ρ) := by
        have h2 : (0:ℝ) < 1 - 2*ρ := by linarith
        have hle : 1 - 2*ρ ≤ 1 - 4*ρ^2 := by nlinarith
        exact div_le_div₀ (by positivity) (by linarith [Real.pi_pos]) h2 hle

end

end Work.BMF.mrlas
