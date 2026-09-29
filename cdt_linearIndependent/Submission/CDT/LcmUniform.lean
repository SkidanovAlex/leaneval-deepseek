import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_error_sum_uniform
import Submission.Commons.NumberTheory.Chebyshev.log_lcm_window_erase_zero_sub_theta_sub_bad_le
import Submission.Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq
import Submission.Commons.Analysis.Sum.tendsto_sqrt_mul_log_div

open Finset Filter
open scoped Topology BigOperators

/-
# The uniform window-`lcm` asymptotic (Lemma `lcm lemma` (1) of Calegari–Dimitrov–Tang)

This module formalises the *uniform* version of the paper's `lcm lemma`, part (1): the
asymptotic
`log L_{n,k} / n → γ Σ_{h ≤ ⌊1/γ⌋−1} 1/h + 1/⌊1/γ⌋`,   `k = ⌊γ n⌋`,

where `L_{n,k} = lcm(n-k, …, n)`, with an error term that is **uniform for `γ ∈ [γ₀, 1]`**
(`γ₀ > 0` fixed).  The paper's non-uniform version is
`Commons.NumberTheory.Chebyshev.log_lcm_window_div_id_tendsto`.

The proof follows the paper:  `log L_{n,k} = θ(n) − Σ_{p bad} log p + O(√n log n)`
(`Commons.NumberTheory.Chebyshev.log_lcm_window_erase_zero_sub_theta_sub_bad_le`), the bad
primes are exactly those in the gaps `(n/(m+1), (n-k-1)/m]`
(`Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq`), and the resulting finite sum is
compared to its model by the pointwise prime number theorem
(`Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_isLittleO`).  The two uniformity
ingredients are

* `window_index_dichotomy`: the number `(n-1)/(k+1) − 1` of gaps is within `1` of `⌊1/γ⌋−1`
  as soon as `n γ² ≥ 1`;
* the derived numeric estimate `window_F_bound`, which compares the model
  `((k+1)/n) H_M + 1/(M+1)` with `γ H_{⌊1/γ⌋−1} + 1/⌊1/γ⌋`.

The range `γ ∈ [1/2, 1]` is treated separately (`log_lcm_window_uniform_ge_half`): there the
value is `1` and no bad primes occur.
-/

namespace Submission.CDT.LcmUniform

theorem theta_rel_error (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ x : ℝ, Y₀ ≤ x → |Chebyshev.theta x - x| ≤ δ * x := by
  have h := Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_isLittleO
  rw [Asymptotics.isLittleO_iff] at h
  have h1 := h (c := δ) hδ
  rw [eventually_atTop] at h1
  obtain ⟨Y₁, hY₁⟩ := h1
  refine ⟨max Y₁ 0, fun x hx => ?_⟩
  have hx1 : Y₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
  have := hY₁ x hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0] at this
  exact this

theorem hsum_le (j : ℕ) :
    (∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹) ≤ (j : ℝ) := by
  calc (∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹)
      ≤ ∑ _m ∈ Finset.Icc 1 j, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        rw [Finset.mem_Icc] at hm
        have hm0 : (0 : ℝ) < (m : ℝ) := by
          have : 0 < m := by omega
          exact_mod_cast this
        rw [inv_le_one₀ hm0]
        exact_mod_cast hm.1
    _ = ((Finset.Icc 1 j).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (j : ℝ) := by
        rw [Nat.card_Icc]
        have : j + 1 - 1 ≤ j := by omega
        exact_mod_cast this

theorem sum_window_div_telescope (n k M : ℕ) (hk : k + 1 ≤ n) :
    (∑ m ∈ Finset.Icc 1 M, (((n - k - 1 : ℕ) : ℝ) / (m : ℝ) - (n : ℝ) / ((m : ℝ) + 1)))
      = (n : ℝ) - ((k : ℝ) + 1) * (∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹)
          - (n : ℝ) / ((M : ℝ) + 1) := by
  have hcast : (((n - k - 1 : ℕ)) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
    rw [show n - k - 1 = n - (k + 1) by omega, Nat.cast_sub hk]
    push_cast
    ring
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)
          (fun m => ((n - k - 1 : ℕ) : ℝ) / (m : ℝ) - (n : ℝ) / ((m : ℝ) + 1)),
        Finset.sum_Icc_succ_top (by omega) (fun m => ((m : ℝ))⁻¹), ih]
    push_cast
    rw [hcast]
    have h1 : ((M : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((M : ℝ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

theorem real_index_bound (n γ j : ℝ) (hγ : 0 < γ) (hn : 0 < n) (hjn : j ≤ γ * n)
    (hjγ : γ * j ≤ 1) : j - 1 ≤ (n - 1) / (γ * n + 1) := by
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith [hjn, hjγ, hn, hγ, mul_nonneg hγ.le hn.le]

theorem window_index_dichotomy (n : ℕ) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hnγ : 1 ≤ (n : ℝ) * γ ^ 2) :
    (⌊1 / γ⌋₊ - 1 ≤ (n - 1) / (⌊γ * (n : ℝ)⌋₊ + 1)) ∧
      ((n - 1) / (⌊γ * (n : ℝ)⌋₊ + 1) ≤ ⌊1 / γ⌋₊) := by
  set k : ℕ := ⌊γ * (n : ℝ)⌋₊ with hk
  set j : ℕ := ⌊1 / γ⌋₊ with hj
  have hnpos : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    norm_num at hnγ
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have h_inv_le : 1 / γ ≤ γ * (n : ℝ) := by
    rw [div_le_iff₀ hγ]
    nlinarith [hnγ]
  have hγn_ge : 1 ≤ γ * (n : ℝ) := by
    have h : (1 : ℝ) ≤ 1 / γ := (one_le_div hγ).mpr hγ1
    linarith
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Nat.le_floor (by push_cast; exact hγn_ge)
  have hk_le : (k : ℝ) ≤ γ * (n : ℝ) := by
    rw [hk]; exact Nat.floor_le (by positivity)
  have hk_lt : γ * (n : ℝ) < (k : ℝ) + 1 := by
    rw [hk]; exact Nat.lt_floor_add_one _
  have hj1 : 1 ≤ j := by
    rw [hj]
    refine Nat.le_floor ?_
    push_cast
    rw [one_le_div hγ]
    exact hγ1
  have hj_le : (j : ℝ) ≤ 1 / γ := by
    rw [hj]; exact Nat.floor_le (by positivity)
  have hγj_le : γ * (j : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hj_le hγ.le
    rwa [mul_one_div, div_self (ne_of_gt hγ)] at h
  have hγn_ge_j : (j : ℝ) ≤ γ * (n : ℝ) := le_trans hj_le h_inv_le
  constructor
  · have hAeq : ((n - 1) / (k + 1) : ℕ) = ⌊(((n - 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))⌋₊ := by
      rw [Nat.floor_div_natCast]
      simp
    have h1 : (((n - 1) / (k + 1) : ℕ) : ℝ) > (((n - 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) - 1 := by
      rw [hAeq]
      exact Nat.sub_one_lt_floor _
    have h2 : (((n - 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) ≥ ((n : ℝ) - 1) / (γ * (n : ℝ) + 1) := by
      have h3 : ((k + 1 : ℕ) : ℝ) ≤ γ * (n : ℝ) + 1 := by push_cast; linarith
      have h4 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; positivity
      have h5 : (0 : ℝ) < γ * (n : ℝ) + 1 := by linarith [hγn_ge]
      have h6 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      rw [show ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 from by
        rw [Nat.cast_sub hnpos]; norm_num]
      exact div_le_div_of_nonneg_left h6 h4 h3
    have h7 : (j : ℝ) - 1 ≤ ((n : ℝ) - 1) / (γ * (n : ℝ) + 1) :=
      real_index_bound _ _ _ hγ hn0R hγn_ge_j hγj_le
    have h8 : (j - 1 : ℕ) ≤ (n - 1) / (k + 1) := by
      by_cases hj2 : 2 ≤ j
      · have hcast : ((j - 2 : ℕ) : ℝ) = (j : ℝ) - 2 := by
          rw [Nat.cast_sub hj2]; norm_num
        have hlt : ((j - 2 : ℕ) : ℝ) < (((n - 1) / (k + 1) : ℕ) : ℝ) := by
          rw [hcast]; linarith
        have := Nat.cast_lt.mp hlt
        omega
      · omega
    exact h8
  · have h1 : (((n - 1) / (k + 1) : ℕ) : ℝ) ≤ ((n : ℝ) - 1) / (γ * (n : ℝ)) := by
      have h2 : (((n - 1) / (k + 1) : ℕ) : ℝ) ≤ (((n - 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
        have := Nat.cast_div_le (α := ℝ) (m := n - 1) (n := k + 1)
        simpa using this
      have h3 : (((n - 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) ≤ ((n : ℝ) - 1) / (γ * (n : ℝ)) := by
        have h4 : γ * (n : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
        have h5 : (0 : ℝ) < γ * (n : ℝ) := by linarith [hγn_ge]
        have h6 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
        rw [show ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 from by
          rw [Nat.cast_sub hnpos]; norm_num]
        exact div_le_div_of_nonneg_left h6 h5 h4
      exact le_trans h2 h3
    have h2 : ((n : ℝ) - 1) / (γ * (n : ℝ)) < 1 / γ := by
      rw [div_lt_div_iff₀ (by linarith [hγn_ge]) hγ]
      nlinarith [hγ, hn0R]
    by_contra hcon
    push Not at hcon
    have h4 : ((j : ℝ) + 1) ≤ (((n - 1) / (k + 1) : ℕ) : ℝ) := by
      have hjc : j + 1 ≤ (n - 1) / (k + 1) := hcon
      exact_mod_cast hjc
    have h5 : 1 / γ < (j : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (1 / γ)
      rw [← hj] at this
      exact this
    linarith

theorem window_F_bound (n k j A : ℕ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hn : 0 < n) (hk : (k : ℝ) ≤ γ * (n : ℝ)) (hk' : γ * (n : ℝ) ≤ (k : ℝ) + 1)
    (hj : (j : ℝ) ≤ 1 / γ) (hj' : 1 / γ < (j : ℝ) + 1) (hγj : γ * (j : ℝ) ≤ 1)
    (hle : A ≤ j) (hge : j - 1 ≤ A)
    (hsmall : A = j - 1 → 1 - γ * (j : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ)) :
    |((k : ℝ) + 1) / (n : ℝ) * (∑ m ∈ Finset.Icc 1 (A - 1), ((m : ℝ))⁻¹) + ((A : ℝ))⁻¹
        - (γ * (∑ m ∈ Finset.Icc 1 (j - 1), ((m : ℝ))⁻¹) + ((j : ℝ))⁻¹)|
      ≤ (4 / γ + 4) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2inv : (2 : ℝ) ≤ 1 / γ := by rw [le_div_iff₀ hγ]; linarith
  have hj2 : 2 ≤ j := by
    have h1 : (2 : ℝ) < (j : ℝ) + 1 := lt_of_le_of_lt h2inv hj'
    have h2 : (1 : ℝ) < (j : ℝ) := by linarith
    have h3 : (1 : ℕ) < j := by exact_mod_cast h2
    omega
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
  have hjm1R : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
  have hjm2R : ((j - 2 : ℕ) : ℝ) = (j : ℝ) - 2 := by rw [Nat.cast_sub hj2]; norm_num
  have hHj_nonneg : 0 ≤ ∑ m ∈ Finset.Icc 1 (j - 1), ((m : ℝ))⁻¹ :=
    Finset.sum_nonneg (fun m _ => by positivity)
  have hHj2_nonneg : 0 ≤ ∑ m ∈ Finset.Icc 1 (j - 2), ((m : ℝ))⁻¹ :=
    Finset.sum_nonneg (fun m _ => by positivity)
  have hHj_le : (∑ m ∈ Finset.Icc 1 (j - 1), ((m : ℝ))⁻¹) ≤ (j : ℝ) :=
    le_trans (hsum_le (j - 1)) (by rw [hjm1R]; linarith)
  have hHj2_le : (∑ m ∈ Finset.Icc 1 (j - 2), ((m : ℝ))⁻¹) ≤ (j : ℝ) :=
    le_trans (hsum_le (j - 2)) (by rw [hjm2R]; linarith)
  have hsplit : (∑ m ∈ Finset.Icc 1 (j - 1), ((m : ℝ))⁻¹)
      = (∑ m ∈ Finset.Icc 1 (j - 2), ((m : ℝ))⁻¹) + ((j : ℝ) - 1)⁻¹ := by
    have h1 : j - 1 = (j - 2) + 1 := by omega
    rw [h1, Finset.sum_Icc_succ_top (by omega) (fun m => ((m : ℝ))⁻¹)]
    congr 1
    rw [show j - 2 + 1 = j - 1 by omega, hjm1R]
  have hcoef : |((k : ℝ) + 1) / (n : ℝ) - γ| ≤ 1 / (n : ℝ) := by
    have h1 : ((k : ℝ) + 1) - γ * (n : ℝ) ≤ 1 := by linarith [hk']
    have h2 : 0 ≤ ((k : ℝ) + 1) - γ * (n : ℝ) := by linarith [hk]
    have h3 : ((k : ℝ) + 1) / (n : ℝ) - γ = (((k : ℝ) + 1) - γ * (n : ℝ)) / (n : ℝ) := by
      field_simp
    rw [h3, abs_div, abs_of_pos hnR]
    exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, h1⟩) hnR.le
  have hfinal : (1 / γ + 2) / (n : ℝ) ≤ (4 / γ + 4) / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR.le
    have h : (0:ℝ) < 1/γ := by positivity
    rw [show (1:ℝ)/γ = 1 * (1/γ) by ring, show (4:ℝ)/γ = 4 * (1/γ) by ring]
    linarith
  have hcase : A = j ∨ A = j - 1 := by omega
  rcases hcase with hA | hA
  · rw [hA]
    have h1 : ((k : ℝ) + 1) / (n : ℝ) * (∑ m ∈ Finset.Icc 1 (j - 1), ((m : ℝ))⁻¹) + ((j : ℝ))⁻¹
        - (γ * (∑ m ∈ Finset.Icc 1 (j - 1), ((m : ℝ))⁻¹) + ((j : ℝ))⁻¹)
        = (((k : ℝ) + 1) / (n : ℝ) - γ) * (∑ m ∈ Finset.Icc 1 (j - 1), ((m : ℝ))⁻¹) := by
      ring
    rw [h1, abs_mul]
    have h3 : |(∑ m ∈ Finset.Icc 1 (j - 1), ((m : ℝ))⁻¹)| ≤ (j : ℝ) := by
      rw [abs_of_nonneg hHj_nonneg]; exact hHj_le
    calc |((k : ℝ) + 1) / (n : ℝ) - γ| * |(∑ m ∈ Finset.Icc 1 (j - 1), ((m : ℝ))⁻¹)|
        ≤ (1 / (n : ℝ)) * (j : ℝ) := by
          refine mul_le_mul hcoef h3 (abs_nonneg _) (by positivity)
      _ ≤ (1 / (n : ℝ)) * (1 / γ) := by
          refine mul_le_mul_of_nonneg_left hj (by positivity)
      _ ≤ (4 / γ + 4) / (n : ℝ) := by
          have h4 : (1 / (n : ℝ)) * (1 / γ) ≤ (1 / (n : ℝ)) * (4 / γ + 4) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h : (0:ℝ) < 1/γ := by positivity
            rw [show (4:ℝ)/γ = 4 * (1/γ) by ring]
            linarith
          have h5 : (1 / (n : ℝ)) * (4 / γ + 4) = (4 / γ + 4) / (n : ℝ) := by ring
          linarith [h4, h5.symm.le, h5.le]
  · rw [hA]
    rw [show j - 1 - 1 = j - 2 from by omega, hjm1R, hsplit]
    have h1 : ((k : ℝ) + 1) / (n : ℝ) * (∑ m ∈ Finset.Icc 1 (j - 2), ((m : ℝ))⁻¹)
          + ((j : ℝ) - 1)⁻¹
        - (γ * ((∑ m ∈ Finset.Icc 1 (j - 2), ((m : ℝ))⁻¹) + ((j : ℝ) - 1)⁻¹) + ((j : ℝ))⁻¹)
        = (((k : ℝ) + 1) / (n : ℝ) - γ) * (∑ m ∈ Finset.Icc 1 (j - 2), ((m : ℝ))⁻¹)
          + (1 - γ * (j : ℝ)) / ((j : ℝ) * ((j : ℝ) - 1)) := by
      have hj0 : (j : ℝ) ≠ 0 := by positivity
      have hjm10 : (j : ℝ) - 1 ≠ 0 := by nlinarith [hjR]
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
      field_simp
      ring
    rw [h1]
    have hkey : 0 ≤ ((k : ℝ) + 1) / (n : ℝ) - γ := by
      rw [sub_nonneg, le_div_iff₀ hnR]; linarith [hk']
    have hnum : 0 ≤ 1 - γ * (j : ℝ) := by linarith [hγj]
    have hden : 0 < (j : ℝ) * ((j : ℝ) - 1) := by nlinarith [hjR]
    have ht2 : 0 ≤ (1 - γ * (j : ℝ)) / ((j : ℝ) * ((j : ℝ) - 1)) := div_nonneg hnum hden.le
    rw [abs_of_nonneg (add_nonneg (mul_nonneg hkey hHj2_nonneg) ht2)]
    have hsmall' : 1 - γ * (j : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := hsmall hA
    have hcoef' : ((k : ℝ) + 1) / (n : ℝ) - γ ≤ 1 / (n : ℝ) := by
      rw [← abs_of_nonneg hkey]; exact hcoef
    have hb1 : (((k : ℝ) + 1) / (n : ℝ) - γ) * (∑ m ∈ Finset.Icc 1 (j - 2), ((m : ℝ))⁻¹)
        ≤ (1 / (n : ℝ)) * (j : ℝ) :=
      mul_le_mul hcoef' hHj2_le hHj2_nonneg (by positivity)
    have hb2 : (1 - γ * (j : ℝ)) / ((j : ℝ) * ((j : ℝ) - 1))
        ≤ (((j : ℝ) + 1) / (n : ℝ)) / ((j : ℝ) * ((j : ℝ) - 1)) :=
      div_le_div_of_nonneg_right hsmall' hden.le
    have hb3 : (((j : ℝ) + 1) / (n : ℝ)) / ((j : ℝ) * ((j : ℝ) - 1)) ≤ (3 / 2) / (n : ℝ) := by
      rw [div_div, div_le_div_iff₀ (by positivity) hnR]
      have h6 : ((j : ℝ) + 1) * 1 ≤ (3 / 2) * ((j : ℝ) * ((j : ℝ) - 1)) := by nlinarith [hjR]
      nlinarith [h6, hnR]
    calc (((k : ℝ) + 1) / (n : ℝ) - γ) * (∑ m ∈ Finset.Icc 1 (j - 2), ((m : ℝ))⁻¹)
          + (1 - γ * (j : ℝ)) / ((j : ℝ) * ((j : ℝ) - 1))
        ≤ (1 / (n : ℝ)) * (j : ℝ) + (3 / 2) / (n : ℝ) := add_le_add hb1 (le_trans hb2 hb3)
      _ ≤ (1 / γ + 2) / (n : ℝ) := by
          have h8 : (1 / (n : ℝ)) * (j : ℝ) = (j : ℝ) / (n : ℝ) := by ring
          rw [h8, ← add_div]
          apply div_le_div_of_nonneg_right _ hnR.le
          linarith [hj]
      _ ≤ (4 / γ + 4) / (n : ℝ) := hfinal

theorem abs_add4_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

theorem abs_sum_theta_sub_le (M : ℕ) (u v : ℕ → ℝ) (δ Y₀ : ℝ)
    (hY : ∀ x, Y₀ ≤ x → |Chebyshev.theta x - x| ≤ δ * x)
    (hu : ∀ m ∈ Finset.Icc 1 M, Y₀ ≤ u m) (hv : ∀ m ∈ Finset.Icc 1 M, Y₀ ≤ v m) :
    |(∑ m ∈ Finset.Icc 1 M, (u m - Chebyshev.theta (u m)))
        - (∑ m ∈ Finset.Icc 1 M, (v m - Chebyshev.theta (v m)))|
      ≤ δ * (∑ m ∈ Finset.Icc 1 M, (u m + v m)) := by
  have h1 : (∑ m ∈ Finset.Icc 1 M, (u m - Chebyshev.theta (u m)))
      - (∑ m ∈ Finset.Icc 1 M, (v m - Chebyshev.theta (v m)))
      = ∑ m ∈ Finset.Icc 1 M,
          ((u m - Chebyshev.theta (u m)) - (v m - Chebyshev.theta (v m))) := by
    first | (simp only [Finset.sum_sub_distrib]; ring) | simp only [Finset.sum_sub_distrib]
  rw [h1]
  calc |∑ m ∈ Finset.Icc 1 M,
          ((u m - Chebyshev.theta (u m)) - (v m - Chebyshev.theta (v m)))|
      ≤ ∑ m ∈ Finset.Icc 1 M,
          |(u m - Chebyshev.theta (u m)) - (v m - Chebyshev.theta (v m))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M,
          (|u m - Chebyshev.theta (u m)| + |v m - Chebyshev.theta (v m)|) :=
        Finset.sum_le_sum (fun m _ => by
          have h := abs_sub_le (u m - Chebyshev.theta (u m)) 0
            (v m - Chebyshev.theta (v m))
          have h2 : |(0 : ℝ) - (v m - Chebyshev.theta (v m))|
              = |v m - Chebyshev.theta (v m)| := by
            rw [zero_sub, abs_neg]
          rw [h2] at h
          simpa using h)
    _ ≤ ∑ m ∈ Finset.Icc 1 M, (δ * u m + δ * v m) := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        have h2 := hY (u m) (hu m hm)
        have h3 := hY (v m) (hv m hm)
        rw [abs_sub_comm (u m) (Chebyshev.theta (u m)),
          abs_sub_comm (v m) (Chebyshev.theta (v m))]
        linarith
    _ = δ * (∑ m ∈ Finset.Icc 1 M, (u m + v m)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        ring

theorem sum_div_le_mul_sum_inv (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ m ∈ Finset.Icc 1 M, c / (m : ℝ)) ≤ c * (∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun m _ => ?_)
  rw [div_eq_mul_inv]

theorem sum_div_add_one_le (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ m ∈ Finset.Icc 1 M, c / ((m : ℝ) + 1)) ≤ c * (M : ℝ) := by
  calc (∑ m ∈ Finset.Icc 1 M, c / ((m : ℝ) + 1)) ≤ ∑ _m ∈ Finset.Icc 1 M, c := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        rw [Finset.mem_Icc] at hm
        rw [div_le_iff₀ (by positivity)]
        have hm1' : (1 : ℝ) ≤ (m : ℝ) + 1 := by
          have h1 : (1 : ℝ) ≤ (m : ℝ) := by
            have : (1 : ℕ) ≤ m := hm.1
            exact_mod_cast this
          linarith
        nlinarith [hc, hm1']
    _ = (M : ℝ) * c := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have h : ((M + 1 - 1 : ℕ) : ℝ) = (M : ℝ) := by
          rw [Nat.add_sub_cancel]
        rw [h]
    _ = c * (M : ℝ) := by ring


set_option maxHeartbeats 1000000 in
/-- **Lemma `lcm lemma` (1) of Calegari–Dimitrov–Tang (arXiv:2408.15403), uniform form.** -/
theorem log_lcm_window_uniform_half (γ₀ ε : ℝ) (hγ₀ : 0 < γ₀) (hγ₀2 : γ₀ ≤ 1 / 2)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ γ : ℝ, γ₀ ≤ γ → γ ≤ 1 / 2 →
      |Real.log ((((Finset.Icc (n - ⌊γ * (n : ℝ)⌋₊) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
          / (n : ℝ)
        - (γ * (∑ h ∈ Finset.Icc 1 (⌊1 / γ⌋₊ - 1), ((h : ℝ))⁻¹) + ((⌊1 / γ⌋₊ : ℝ))⁻¹)|
      ≤ ε := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 / γ₀ + 4 := ⟨_, rfl⟩
  have hKpos : 0 < K := by
    rw [hK, show (4 : ℝ) / γ₀ = 4 * (1 / γ₀) by ring]
    have h : (0 : ℝ) < 1 / γ₀ := by positivity
    linarith
  have hK0 : (0 : ℝ) ≤ K := hKpos.le
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (4 * (K + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hε (by linarith)
  have h4K : (0 : ℝ) < 4 * (K + 1) := by linarith
  have hδle : δ ≤ ε / 4 := by
    rw [hδ]
    exact div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
  have hδK : δ * K ≤ ε / 4 := by
    rw [hδ, div_mul_eq_mul_div]
    rw [div_le_div_iff₀ h4K (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hε, hKpos]
  obtain ⟨Y₀, hY₀⟩ := theta_rel_error δ hδpos
  have hT1 : ∀ᶠ n : ℕ in Filter.atTop, Y₀ ≤ (n : ℝ) := by
    rcases exists_nat_gt Y₀ with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hN.le (by exact_mod_cast hn)
  have hT2 : ∀ᶠ n : ℕ in Filter.atTop, 4 * Y₀ / γ₀ ≤ (n : ℝ) := by
    rcases exists_nat_gt (4 * Y₀ / γ₀) with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hN.le (by exact_mod_cast hn)
  have hT3 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ (n : ℝ) * γ₀ ^ 2 := by
    rcases exists_nat_gt (1 / γ₀ ^ 2) with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : 1 / γ₀ ^ 2 ≤ (n : ℝ) := le_trans hN.le hNn
    rw [div_le_iff₀ (pow_pos hγ₀ 2)] at h1
    linarith
  have hT4 : ∀ᶠ n : ℕ in Filter.atTop,
      2 * (Real.sqrt (n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) ≤ ε / 4 := by
    have ht := Commons.Analysis.Sum.tendsto_sqrt_mul_log_div.const_mul (2 : ℝ)
    have hε4 : (0 : ℝ) < ε / 4 := by
      rw [show ε / 4 = ε * (1/4) by ring]
      positivity
    have h := ht.eventually (eventually_lt_nhds (by linarith [hε4] : (2:ℝ) * 0 < ε / 4))
    exact h.mono (fun n hn => hn.le)
  have hT5 : ∀ᶠ n : ℕ in Filter.atTop, K ≤ (ε / 4) * (n : ℝ) := by
    rcases exists_nat_gt (K / (ε / 4)) with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : K / (ε / 4) ≤ (n : ℝ) := le_trans hN.le (by exact_mod_cast hn)
    have hε4 : (0 : ℝ) < ε / 4 := by
      rw [show ε / 4 = ε * (1/4) by ring]
      positivity
    rw [div_le_iff₀ hε4] at h1
    linarith
  filter_upwards [hT1, hT2, hT3, hT4, hT5] with n hn1 hn2 hn3 hn4 hn5
  intro γ hγγ hγ2
  have hγpos : 0 < γ := lt_of_lt_of_le hγ₀ hγγ
  have hγle1 : γ ≤ 1 := by linarith
  have hn4R : (4 : ℝ) ≤ (n : ℝ) := by
    have h24 : γ₀ ^ 2 ≤ 1 / 4 := by nlinarith [hγ₀, hγ₀2]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by nlinarith [hn3, hγ₀]
    have hmul : (n : ℝ) * γ₀ ^ 2 ≤ (n : ℝ) * (1 / 4) := mul_le_mul_of_nonneg_left h24 hnn
    have h1 : (1 : ℝ) ≤ (n : ℝ) * (1 / 4) := le_trans hn3 hmul
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1' : 1 ≤ n := by
    have : (1 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hnγ : 1 ≤ (n : ℝ) * γ ^ 2 := by
    have hsq : γ₀ ^ 2 ≤ γ ^ 2 := by nlinarith [hγγ, hγ₀]
    nlinarith [hn3, hsq]
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌊γ * (n : ℝ)⌋₊ := ⟨_, rfl⟩
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = ⌊1 / γ⌋₊ := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = (n - 1) / (k + 1) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = A - 1 := ⟨_, rfl⟩
  have hk_le : (k : ℝ) ≤ γ * (n : ℝ) := by
    rw [hkdef]; exact Nat.floor_le (by positivity)
  have hk_lt : γ * (n : ℝ) < (k : ℝ) + 1 := by
    rw [hkdef]; exact Nat.lt_floor_add_one _
  have hj_le : (j : ℝ) ≤ 1 / γ := by
    rw [hjdef]; exact Nat.floor_le (by positivity)
  have hj_lt : 1 / γ < (j : ℝ) + 1 := by
    rw [hjdef]; exact Nat.lt_floor_add_one _
  have hγj_le : γ * (j : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hj_le hγpos.le
    rwa [mul_one_div, div_self (ne_of_gt hγpos)] at h
  have hk1 : 1 ≤ k := by
    have h2 : (1 : ℝ) ≤ 1 / γ := (one_le_div hγpos).mpr hγle1
    have h3 : 1 / γ ≤ γ * (n : ℝ) := by
      rw [div_le_iff₀ hγpos]; nlinarith [hnγ]
    have h : (1 : ℝ) ≤ γ * (n : ℝ) := le_trans h2 h3
    rw [hkdef]
    exact Nat.le_floor (by push_cast; exact h)
  have hkn : k ≤ n := by
    have h : (k : ℝ) ≤ (n : ℝ) := by nlinarith [hk_le, hγ2, hnR]
    exact_mod_cast h
  have hk1n : k + 1 ≤ n := by
    have h : (k : ℝ) + 1 ≤ (n : ℝ) := by nlinarith [hk_le, hγ2, hnR, hn4R]
    exact_mod_cast h
  have hdich := window_index_dichotomy n γ hγpos hγle1 hnγ
  have hA_le_j : A ≤ j := by
    rw [← hkdef, ← hjdef, ← hAdef] at hdich
    exact hdich.2
  have hj1_le_A : j - 1 ≤ A := by
    rw [← hkdef, ← hjdef, ← hAdef] at hdich
    exact hdich.1
  have hj2 : 2 ≤ j := by
    have h2 : (2 : ℝ) ≤ 1 / γ := by rw [le_div_iff₀ hγpos]; linarith
    have h3 : (1 : ℝ) < (j : ℝ) := by linarith [lt_of_le_of_lt h2 hj_lt]
    have h4 : (1 : ℕ) < j := by exact_mod_cast h3
    omega
  have hA1 : 1 ≤ A := by omega
  have hMA : M + 1 = A := by rw [hMdef]; omega
  have hMle : M ≤ j := by rw [hMdef]; omega
  have hMR : (M : ℝ) ≤ 1 / γ₀ := by
    have h1 : (M : ℝ) ≤ (j : ℝ) := by exact_mod_cast hMle
    have h2 : (1 : ℝ) / γ ≤ 1 / γ₀ := one_div_le_one_div_of_le hγ₀ hγγ
    linarith [hj_le]
  have hγM : γ₀ * (M : ℝ) ≤ 1 := by
    have h' := mul_le_mul_of_nonneg_left hMR hγ₀.le
    rwa [mul_one_div, div_self (ne_of_gt hγ₀)] at h'
  have hY0le : Y₀ ≤ (n : ℝ) * γ₀ / 4 := by
    have h : 4 * Y₀ ≤ (n : ℝ) * γ₀ := by
      have h' : 4 * Y₀ / γ₀ ≤ (n : ℝ) := hn2
      rw [div_le_iff₀ hγ₀] at h'
      linarith
    linarith
  have hcast_nk : (((n - k - 1 : ℕ)) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
    have h1 : n - k - 1 = n - (k + 1) := by omega
    rw [h1, Nat.cast_sub hk1n]
    push_cast
    ring
  have hnk_ge : (n : ℝ) / 4 ≤ (n : ℝ) - (k : ℝ) - 1 := by
    have hk2 : (k : ℝ) ≤ (n : ℝ) / 2 := by
      have h' : γ * (n : ℝ) ≤ (n : ℝ) / 2 := by
        have h2 := mul_le_mul_of_nonneg_right hγ2 hnR.le
        nlinarith [h2]
      linarith [hk_le]
    have h2 : (n : ℝ) / 4 ≤ (n : ℝ) / 2 - 1 := by
      have e1 : (n : ℝ) / 4 = (n : ℝ) * (1 / 4) := by ring
      have e2 : (n : ℝ) / 2 = (n : ℝ) * (1 / 2) := by ring
      rw [e1, e2]; linarith [hn4R]
    linarith [h2, hk2]
  have hu_ge : ∀ m ∈ Finset.Icc 1 M, Y₀ ≤ (((n - k - 1 : ℕ)) : ℝ) / (m : ℝ) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmM⟩ := hm
    have hmR : (0 : ℝ) < (m : ℝ) := by
      have h : (0 : ℕ) < m := by omega
      exact_mod_cast h
    have hMRpos : (0 : ℝ) < (M : ℝ) := by
      have h : (0 : ℕ) < M := by omega
      exact_mod_cast h
    have hstep1 : (n : ℝ) * γ₀ / 4 ≤ (((n - k - 1 : ℕ)) : ℝ) / (M : ℝ) := by
      rw [hcast_nk]
      have h2 : (n : ℝ) / 4 ≤ (n : ℝ) - (k : ℝ) - 1 := hnk_ge
      have hA : (n : ℝ) * γ₀ / 4 ≤ ((n : ℝ) / 4) / (M : ℝ) := by
        rw [le_div_iff₀ hMRpos]
        nlinarith [hnR, hγM]
      have hB : ((n : ℝ) / 4) / (M : ℝ) ≤ ((n : ℝ) - (k : ℝ) - 1) / (M : ℝ) :=
        div_le_div_of_nonneg_right h2 hMRpos.le
      linarith
    have hstep2 : (((n - k - 1 : ℕ)) : ℝ) / (M : ℝ) ≤ (((n - k - 1 : ℕ)) : ℝ) / (m : ℝ) := by
      have h0 : (0 : ℝ) ≤ (((n - k - 1 : ℕ)) : ℝ) := by positivity
      have hmm : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
      exact div_le_div_of_nonneg_left h0 hmR hmm
    linarith [hY0le, hstep1, hstep2]
  have hv_ge : ∀ m ∈ Finset.Icc 1 M, Y₀ ≤ (n : ℝ) / ((m : ℝ) + 1) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmM⟩ := hm
    have hmR : (0 : ℝ) < (m : ℝ) + 1 := by
      have h : (0 : ℕ) < m := by omega
      have h' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h
      linarith
    have h1 : (A : ℝ) ≤ (j : ℝ) := by exact_mod_cast hA_le_j
    have hApos : (0 : ℝ) < (A : ℝ) := by
      have h : (0 : ℕ) < A := by omega
      exact_mod_cast h
    have h3 : (n : ℝ) / ((M : ℝ) + 1) ≤ (n : ℝ) / ((m : ℝ) + 1) := by
      have hmm : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
      exact div_le_div_of_nonneg_left hnR.le hmR (by linarith)
    have h4 : (n : ℝ) * γ ≤ (n : ℝ) / ((M : ℝ) + 1) := by
      rw [show ((M : ℝ) + 1) = (A : ℝ) by rw [← hMA]; push_cast; ring]
      have h5 : (n : ℝ) / (j : ℝ) ≤ (n : ℝ) / (A : ℝ) :=
        div_le_div_of_nonneg_left hnR.le hApos h1
      have h6 : (n : ℝ) * γ ≤ (n : ℝ) / (j : ℝ) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hnR, hγj_le, hγpos]
      linarith
    have h8 : (n : ℝ) * γ₀ / 4 ≤ (n : ℝ) * γ := by nlinarith [hγγ, hnR]
    linarith [hY0le, h3, h4, h8]
  have hsum_uv : (∑ m ∈ Finset.Icc 1 M,
      ((((n - k - 1 : ℕ)) : ℝ) / (m : ℝ) + (n : ℝ) / ((m : ℝ) + 1))) ≤ K * (n : ℝ) := by
    rw [Finset.sum_add_distrib]
    have hcast' : ((((n - k - 1 : ℕ)) : ℝ)) ≤ (n : ℝ) := by
      rw [hcast_nk]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hHnn : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹ :=
      Finset.sum_nonneg (fun m _ => by positivity)
    have h1 : (∑ m ∈ Finset.Icc 1 M, (((n - k - 1 : ℕ)) : ℝ) / (m : ℝ)) ≤ (n : ℝ) / γ₀ := by
      calc (∑ m ∈ Finset.Icc 1 M, (((n - k - 1 : ℕ)) : ℝ) / (m : ℝ))
          ≤ ((((n - k - 1 : ℕ)) : ℝ)) * (∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹) :=
            sum_div_le_mul_sum_inv M ((((n - k - 1 : ℕ)) : ℝ)) (by positivity)
        _ ≤ (n : ℝ) * (∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_right hcast' hHnn
        _ ≤ (n : ℝ) * (M : ℝ) := mul_le_mul_of_nonneg_left (hsum_le M) hnR.le
        _ ≤ (n : ℝ) / γ₀ := by
            rw [le_div_iff₀ hγ₀]; nlinarith [hnR, hMR, hγM]
    have h2 : (∑ m ∈ Finset.Icc 1 M, (n : ℝ) / ((m : ℝ) + 1)) ≤ (n : ℝ) / γ₀ := by
      refine le_trans (sum_div_add_one_le M ((n : ℝ)) hnR.le) ?_
      rw [le_div_iff₀ hγ₀]
      nlinarith [hnR, hMR, hγM]
    have hK2 : (n : ℝ) / γ₀ + (n : ℝ) / γ₀ ≤ K * (n : ℝ) := by
      rw [hK, show (4 : ℝ) / γ₀ = 4 * (1 / γ₀) by ring,
        show (n : ℝ) / γ₀ = (n : ℝ) * (1 / γ₀) by ring]
      have h : (0 : ℝ) < 1 / γ₀ := by positivity
      nlinarith [hnR, h]
    linarith
  have hE1 := Commons.NumberTheory.Chebyshev.log_lcm_window_erase_zero_sub_theta_sub_bad_le n k hkn
  have hbad := Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq n k hk1 hkn
  obtain ⟨Sb, hSb⟩ : ∃ Sb : ℝ, Sb = ∑ p ∈ (Finset.Icc 1 n).filter
      (fun p => p.Prime ∧ ¬ (∃ m ∈ Finset.Icc (n - k) n, p ∣ m)), Real.log (p : ℝ) := ⟨_, rfl⟩
  obtain ⟨Se, hSe⟩ : ∃ Se : ℝ, Se = ∑ m ∈ Finset.Icc 1 M,
      (Chebyshev.theta ((((n - k - 1 : ℕ)) : ℝ) / (m : ℝ))
        - Chebyshev.theta ((n : ℝ) / ((m : ℝ) + 1))) := ⟨_, rfl⟩
  obtain ⟨Sd, hSd⟩ : ∃ Sd : ℝ, Sd = ∑ m ∈ Finset.Icc 1 M,
      ((((n - k - 1 : ℕ)) : ℝ) / (m : ℝ) - (n : ℝ) / ((m : ℝ) + 1)) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ,
      L = Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨Vv, hVv⟩ : ∃ Vv : ℝ,
      Vv = γ * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹) + ((j : ℝ))⁻¹ := ⟨_, rfl⟩
  have hbad' : Sb = Se := by
    rw [hSb, hSe, hbad]
    congr 1
    rw [show (n - 1) / (k + 1) - 1 = M by rw [← hAdef, ← hMdef]]
  have htel := sum_window_div_telescope n k M hk1n
  have hSd' : Sd = (n : ℝ) - ((k : ℝ) + 1) * (∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹)
      - (n : ℝ) / ((M : ℝ) + 1) := by rw [hSd]; exact htel
  have hMAcast : ((M : ℝ) + 1) = (A : ℝ) := by
    rw [← hMA]; push_cast; ring
  have hFv : ((n : ℝ) - Sd) / (n : ℝ)
      = ((k : ℝ) + 1) / (n : ℝ) * (∑ m ∈ Finset.Icc 1 M, ((m : ℝ))⁻¹) + ((A : ℝ))⁻¹ := by
    rw [hSd', hMAcast]
    field_simp
    ring
  have hsmall : A = j - 1 → 1 - γ * (j : ℝ) ≤ ((j : ℝ) + 1) / (n : ℝ) := by
    intro hAj'
    have hxA : ⌊(((n - 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))⌋₊ = A := by
      rw [Nat.floor_div_natCast, Nat.floor_natCast]; exact hAdef.symm
    have hxlt : ((n - 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) < (j : ℝ) := by
      have h := Nat.lt_floor_add_one (((n - 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))
      rw [hxA] at h
      rw [hAj'] at h
      have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
      linarith
    have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      have h : (0 : ℕ) < k + 1 := by omega
      exact_mod_cast h
    have hmul : ((n - 1 : ℕ) : ℝ) < (j : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hkp] at hxlt
      linarith
    have hcast1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    have hkp2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast1, hkp2] at hmul
    have hγn1 : (k : ℝ) + 1 ≤ γ * (n : ℝ) + 1 := by linarith [hk_lt]
    have hjR0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have hfin : (n : ℝ) - 1 < (j : ℝ) * (γ * (n : ℝ) + 1) := by
      nlinarith [hmul, hγn1, hjR0]
    have hfin2 : (n : ℝ) * (1 - γ * (j : ℝ)) < (j : ℝ) + 1 := by
      have he : (n : ℝ) * (1 - γ * (j : ℝ)) = (n : ℝ) - (j : ℝ) * (γ * (n : ℝ)) := by ring
      rw [he]
      linarith [hfin]
    rw [le_div_iff₀ hnR]
    linarith [hfin2]
  have hn0' : 0 < n := by omega
  have hFb := window_F_bound n k j A γ hγpos hγ2 hn0' hk_le hk_lt.le hj_le hj_lt
    hγj_le hA_le_j hj1_le_A hsmall
  have hQeq : Sd - Se
      = (∑ m ∈ Finset.Icc 1 M,
            ((((n - k - 1 : ℕ)) : ℝ) / (m : ℝ)
              - Chebyshev.theta ((((n - k - 1 : ℕ)) : ℝ) / (m : ℝ))))
        - (∑ m ∈ Finset.Icc 1 M,
            ((n : ℝ) / ((m : ℝ) + 1) - Chebyshev.theta ((n : ℝ) / ((m : ℝ) + 1)))) := by
    rw [hSd, hSe]
    first | (simp only [Finset.sum_sub_distrib]; ring) | simp only [Finset.sum_sub_distrib]
  have hQ1 := abs_sum_theta_sub_le M (fun m => (((n - k - 1 : ℕ)) : ℝ) / (m : ℝ))
    (fun m => (n : ℝ) / ((m : ℝ) + 1)) δ Y₀ hY₀ hu_ge hv_ge
  have hQle : δ * (∑ m ∈ Finset.Icc 1 M,
      ((((n - k - 1 : ℕ)) : ℝ) / (m : ℝ) + (n : ℝ) / ((m : ℝ) + 1))) ≤ δ * K * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsum_uv hδpos.le
    have he : δ * (K * (n : ℝ)) = δ * K * (n : ℝ) := by ring
    linarith [h, he]
  have hQ : |Sd - Se| ≤ δ * K * (n : ℝ) := by
    rw [hQeq]
    exact le_trans hQ1 hQle
  have hθn := hY₀ (n : ℝ) hn1
  have hE1' : |L - (Chebyshev.theta (n : ℝ) - Se)| ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    rw [← hL, ← hSb, hbad'] at hE1
    exact hE1
  have b1 : |(L - (Chebyshev.theta (n : ℝ) - Se)) / (n : ℝ)| ≤ ε / 4 := by
    rw [abs_div, abs_of_pos hnR]
    have h2 : |L - (Chebyshev.theta (n : ℝ) - Se)| / (n : ℝ)
        ≤ (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hE1' hnR.le
    have h3 : (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ)
        = 2 * (Real.sqrt (n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) := by ring
    rw [h3] at h2
    exact le_trans h2 hn4
  have b2 : |(Chebyshev.theta (n : ℝ) - (n : ℝ)) / (n : ℝ)| ≤ ε / 4 := by
    rw [abs_div, abs_of_pos hnR]
    have h2 : |Chebyshev.theta (n : ℝ) - (n : ℝ)| / (n : ℝ) ≤ δ := by
      rw [div_le_iff₀ hnR]; linarith [hθn]
    exact le_trans h2 hδle
  have b3 : |((n : ℝ) - Sd) / (n : ℝ) - Vv| ≤ ε / 4 := by
    rw [← hMdef] at hFb
    rw [← hFv, ← hVv] at hFb
    have h2 : (4 / γ + 4) / (n : ℝ) ≤ K / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      rw [hK]
      have h5 : (1 : ℝ) / γ ≤ 1 / γ₀ := one_div_le_one_div_of_le hγ₀ hγγ
      have he : (4 : ℝ) / γ = 4 * (1 / γ) := by ring
      have he2 : (4 : ℝ) / γ₀ = 4 * (1 / γ₀) := by ring
      linarith
    have h3 : K / (n : ℝ) ≤ ε / 4 := by
      rw [div_le_iff₀ hnR]
      linarith [hn5]
    exact le_trans (le_trans hFb h2) h3
  have b4 : |(Sd - Se) / (n : ℝ)| ≤ ε / 4 := by
    rw [abs_div, abs_of_pos hnR]
    rw [div_le_iff₀ hnR]
    have h2 : δ * K * (n : ℝ) ≤ (ε / 4) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hδK hnR.le
    exact le_trans hQ h2
  have hdec : L / (n : ℝ) - Vv
      = (L - (Chebyshev.theta (n : ℝ) - Se)) / (n : ℝ)
        + (Chebyshev.theta (n : ℝ) - (n : ℝ)) / (n : ℝ)
        + (((n : ℝ) - Sd) / (n : ℝ) - Vv) + (Sd - Se) / (n : ℝ) := by ring
  have hfinal1 : |L / (n : ℝ) - Vv| ≤
      |(L - (Chebyshev.theta (n : ℝ) - Se)) / (n : ℝ)|
        + |(Chebyshev.theta (n : ℝ) - (n : ℝ)) / (n : ℝ)|
        + |((n : ℝ) - Sd) / (n : ℝ) - Vv| + |(Sd - Se) / (n : ℝ)| := by
    rw [hdec]
    exact abs_add4_le _ _ _ _
  rw [← hkdef, ← hjdef, ← hL, ← hVv]
  have hsum4 : |(L - (Chebyshev.theta (n : ℝ) - Se)) / (n : ℝ)|
        + |(Chebyshev.theta (n : ℝ) - (n : ℝ)) / (n : ℝ)|
        + |((n : ℝ) - Sd) / (n : ℝ) - Vv| + |(Sd - Se) / (n : ℝ)| ≤ ε := by
    linarith [b1, b2, b3, b4]
  exact le_trans hfinal1 hsum4


/-- For `γ ∈ [1/2, 1]` the target value of the window-lcm asymptotic is `1`. -/
theorem V_eq_one_of_half_le (γ : ℝ) (h1 : 1 / 2 ≤ γ) (h2 : γ ≤ 1) :
    γ * (∑ h ∈ Finset.Icc 1 (⌊1 / γ⌋₊ - 1), ((h : ℝ))⁻¹) + ((⌊1 / γ⌋₊ : ℝ))⁻¹ = 1 := by
  have hγpos : 0 < γ := by linarith
  have hinv1 : (1 : ℝ) ≤ 1 / γ := (one_le_div hγpos).mpr h2
  have hinv2 : 1 / γ ≤ 2 := by rw [div_le_iff₀ hγpos]; linarith
  have hj1 : 1 ≤ ⌊1 / γ⌋₊ := Nat.le_floor (by push_cast; exact hinv1)
  have hj2 : ⌊1 / γ⌋₊ ≤ 2 := by
    have h := Nat.floor_mono hinv2
    simpa using h
  rcases (by omega : ⌊1 / γ⌋₊ = 1 ∨ ⌊1 / γ⌋₊ = 2) with h | h
  · rw [h]
    norm_num
  · rw [h]
    have hge : (2 : ℝ) ≤ 1 / γ := by
      have hx := Nat.floor_le (show (0 : ℝ) ≤ 1 / γ by positivity)
      rw [h] at hx
      push_cast at hx
      linarith
    have hsum : (∑ x ∈ (Finset.Icc 1 (2 - 1) : Finset ℕ), ((x : ℝ))⁻¹) = 1 := by norm_num
    rw [hsum]
    have heq : γ = 1 / 2 := by
      have hx : (1 : ℝ) / γ = 2 := le_antisymm hinv2 hge
      rw [div_eq_iff (ne_of_gt hγpos)] at hx
      linarith
    rw [heq]
    norm_num

/-- Uniform window-lcm asymptotic in the range `γ ∈ [1/2, 1]` (where the value is `1`). -/
theorem log_lcm_window_uniform_ge_half (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ γ : ℝ, 1 / 2 ≤ γ → γ ≤ 1 →
      |Real.log ((((Finset.Icc (n - ⌊γ * (n : ℝ)⌋₊) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
          / (n : ℝ)
        - (γ * (∑ h ∈ Finset.Icc 1 (⌊1 / γ⌋₊ - 1), ((h : ℝ))⁻¹) + ((⌊1 / γ⌋₊ : ℝ))⁻¹)|
      ≤ ε := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨Y₀, hY₀⟩ := theta_rel_error δ hδpos
  have hT1 : ∀ᶠ n : ℕ in Filter.atTop, Y₀ ≤ (n : ℝ) := by
    rcases exists_nat_gt Y₀ with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hN.le (by exact_mod_cast hn)
  have hT2 : ∀ᶠ n : ℕ in Filter.atTop,
      2 * (Real.sqrt (n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) ≤ ε / 2 := by
    have ht := Commons.Analysis.Sum.tendsto_sqrt_mul_log_div.const_mul (2 : ℝ)
    have hε2 : (0 : ℝ) < ε / 2 := by
      rw [show ε / 2 = ε * (1 / 2) by ring]; positivity
    have h := ht.eventually (eventually_lt_nhds (by linarith [hε2] : (2 : ℝ) * 0 < ε / 2))
    exact h.mono (fun n hn => hn.le)
  have hT3 : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℕ) ≤ n := eventually_ge_atTop 2
  filter_upwards [hT1, hT2, hT3] with n hn1 hn2 hn3
  intro γ hγ1 hγ2
  have hγpos : 0 < γ := by linarith
  have hγle1 : γ ≤ 1 := hγ2
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌊γ * (n : ℝ)⌋₊ := ⟨_, rfl⟩
  have hk_le : (k : ℝ) ≤ γ * (n : ℝ) := by
    rw [hkdef]; exact Nat.floor_le (by positivity)
  have hk_lt : γ * (n : ℝ) < (k : ℝ) + 1 := by
    rw [hkdef]; exact Nat.lt_floor_add_one _
  have hk1 : 1 ≤ k := by
    rw [hkdef]
    refine Nat.le_floor ?_
    push_cast
    have h := mul_le_mul_of_nonneg_left hγ1 hnR.le
    linarith
  have hkn : k ≤ n := by
    have h : (k : ℝ) ≤ (n : ℝ) := by
      have h1 : γ * (n : ℝ) ≤ (n : ℝ) := by
        have h2 := mul_le_of_le_one_left hnR.le hγ2
        linarith [h2]
      linarith [hk_le, h1]
    exact_mod_cast h
  have hnn : n ≤ 2 * k + 2 := by
    have h : (n : ℝ) ≤ 2 * (k : ℝ) + 2 := by
      have h1 : γ * (n : ℝ) - 1 ≤ (k : ℝ) := by linarith [hk_lt]
      nlinarith [h1, hγ1, hnR]
    exact_mod_cast h
  have hM0 : (n - 1) / (k + 1) - 1 = 0 := by
    have h2 : (n - 1) / (k + 1) < 2 := Nat.div_lt_of_lt_mul (by omega)
    omega
  obtain ⟨Sb, hSb⟩ : ∃ Sb : ℝ, Sb = ∑ p ∈ (Finset.Icc 1 n).filter
      (fun p => p.Prime ∧ ¬ (∃ m ∈ Finset.Icc (n - k) n, p ∣ m)), Real.log (p : ℝ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ,
      L = Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) := ⟨_, rfl⟩
  have hE1 := Commons.NumberTheory.Chebyshev.log_lcm_window_erase_zero_sub_theta_sub_bad_le n k hkn
  have hbad := Commons.NumberTheory.Chebyshev.sum_log_primes_bad_eq n k hk1 hkn
  have hSb0 : Sb = 0 := by
    rw [hSb, hbad, hM0]
    simp
  have hE1' : |L - Chebyshev.theta (n : ℝ)| ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    rw [← hL, ← hSb, hSb0] at hE1
    simpa using hE1
  have hV : γ * (∑ h ∈ Finset.Icc 1 (⌊1 / γ⌋₊ - 1), ((h : ℝ))⁻¹) + ((⌊1 / γ⌋₊ : ℝ))⁻¹ = 1 :=
    V_eq_one_of_half_le γ hγ1 hγle1
  have hθn := hY₀ (n : ℝ) hn1
  have hb1 : |(L - Chebyshev.theta (n : ℝ)) / (n : ℝ)| ≤ ε / 2 := by
    rw [abs_div, abs_of_pos hnR]
    have h2 : |L - Chebyshev.theta (n : ℝ)| / (n : ℝ)
        ≤ (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hE1' hnR.le
    have h3 : (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ)
        = 2 * (Real.sqrt (n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) := by ring
    rw [h3] at h2
    exact le_trans h2 hn2
  have hb2 : |(Chebyshev.theta (n : ℝ) - (n : ℝ)) / (n : ℝ)| ≤ ε / 2 := by
    rw [abs_div, abs_of_pos hnR]
    have h2 : |Chebyshev.theta (n : ℝ) - (n : ℝ)| / (n : ℝ) ≤ δ := by
      rw [div_le_iff₀ hnR]; linarith [hθn]
    rw [hδ] at h2
    exact h2
  have hdec : L / (n : ℝ) - 1
      = (L - Chebyshev.theta (n : ℝ)) / (n : ℝ)
        + (Chebyshev.theta (n : ℝ) - (n : ℝ)) / (n : ℝ) := by
    field_simp
    ring
  have hf1 : |L / (n : ℝ) - 1| ≤
      |(L - Chebyshev.theta (n : ℝ)) / (n : ℝ)|
        + |(Chebyshev.theta (n : ℝ) - (n : ℝ)) / (n : ℝ)| := by
    rw [hdec]
    exact abs_add_le _ _
  rw [← hkdef, hV, ← hL]
  have hsum2 : |(L - Chebyshev.theta (n : ℝ)) / (n : ℝ)|
      + |(Chebyshev.theta (n : ℝ) - (n : ℝ)) / (n : ℝ)| ≤ ε := by linarith [hb1, hb2]
  exact le_trans hf1 hsum2


set_option maxHeartbeats 1000000 in
/-- **Lemma `lcm lemma` (1) of Calegari–Dimitrov–Tang (arXiv:2408.15403), uniform form.**
For `γ₀ ∈ (0, 1]` and every `ε > 0` there is `N` such that for all `n ≥ N` and every
`γ ∈ [γ₀, 1]`, with `k = ⌊γ n⌋` and `L_{n,k} = lcm(n-k, …, n)`,
`|log L_{n,k}/n − (γ Σ_{h ≤ ⌊1/γ⌋−1} 1/h + 1/⌊1/γ⌋)| ≤ ε`. -/
theorem log_lcm_window_uniform (γ₀ ε : ℝ) (hγ₀ : 0 < γ₀) (hγ₀1 : γ₀ ≤ 1)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ γ : ℝ, γ₀ ≤ γ → γ ≤ 1 →
      |Real.log ((((Finset.Icc (n - ⌊γ * (n : ℝ)⌋₊) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
          / (n : ℝ)
        - (γ * (∑ h ∈ Finset.Icc 1 (⌊1 / γ⌋₊ - 1), ((h : ℝ))⁻¹) + ((⌊1 / γ⌋₊ : ℝ))⁻¹)|
      ≤ ε := by
  by_cases hcase : γ₀ ≤ 1 / 2
  · filter_upwards [log_lcm_window_uniform_half γ₀ ε hγ₀ hcase hε,
      log_lcm_window_uniform_ge_half ε hε] with n h1 h2
    intro γ hγγ hγ1
    by_cases h : γ ≤ 1 / 2
    · exact h1 γ hγγ h
    · exact h2 γ (le_of_not_ge h) hγ1
  · filter_upwards [log_lcm_window_uniform_ge_half ε hε] with n h2
    intro γ hγγ hγ1
    exact h2 γ (le_trans (le_of_not_ge hcase) hγγ) hγ1

end LcmUniform
