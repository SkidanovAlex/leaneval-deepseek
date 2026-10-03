import Mathlib
import Submission.Commons.Analysis.Sums.tail_pow_abel_bound

namespace Commons.NumberTheory.LSeries

open scoped BigOperators

/-! ### The character `χ₄` -/

/-- The non-principal Dirichlet character modulo `4`, as a `ℂ`-valued function on `ℕ`:
`χ₄(n) = 1` if `n ≡ 1 (4)`, `-1` if `n ≡ 3 (4)` and `0` otherwise. -/
private def chi4 (n : ℕ) : ℂ := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

private lemma chi4_zero : chi4 0 = 0 := by simp [chi4]

private lemma chi4_norm_le_one (n : ℕ) : ‖chi4 n‖ ≤ 1 := by
  simp only [chi4]; split_ifs <;> simp

/-- `χ₄(n)` is the imaginary part of `i ^ n`. -/
private lemma chi4_eq_I_im (n : ℕ) : chi4 n = ((Complex.I ^ n).im : ℂ) := by
  have hchi : chi4 n = chi4 (n % 4) := by simp only [chi4]; rw [Nat.mod_mod]
  have hI : Complex.I ^ n = Complex.I ^ (n % 4) := by
    conv_lhs => rw [← Nat.div_add_mod n 4]
    rw [pow_add, pow_mul]
    have : Complex.I ^ 4 = 1 := Complex.I_pow_four
    rw [this]; simp
  rw [hchi, hI]
  have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp [chi4]

private lemma sum_Icc_I_pow_norm_le (x y : ℕ) (hxy : x ≤ y) :
    ‖∑ n ∈ Finset.Icc x y, Complex.I ^ n‖ ≤ 2 := by
  have hmul : (∑ n ∈ Finset.Icc x y, Complex.I ^ n) * (Complex.I - 1)
      = Complex.I ^ (y + 1) - Complex.I ^ x := by
    rw [Finset.sum_mul]
    have hterm : ∀ n : ℕ, Complex.I ^ n * (Complex.I - 1) = Complex.I ^ (n + 1) - Complex.I ^ n := by
      intro n; rw [pow_succ]; ring
    simp_rw [hterm]
    rw [Finset.sum_Icc_sub (f := fun n => Complex.I ^ n) hxy]
  have hge : 1 ≤ ‖Complex.I - 1‖ := by
    have h := Complex.abs_re_le_norm (Complex.I - 1)
    simp at h
    linarith
  have hprod : ‖∑ n ∈ Finset.Icc x y, Complex.I ^ n‖ * ‖Complex.I - 1‖ ≤ 2 := by
    rw [← norm_mul, hmul]
    calc ‖Complex.I ^ (y + 1) - Complex.I ^ x‖
        ≤ ‖Complex.I ^ (y + 1)‖ + ‖Complex.I ^ x‖ := norm_sub_le _ _
      _ = 1 + 1 := by simp
      _ = 2 := by norm_num
  have hnn : 0 ≤ ‖∑ n ∈ Finset.Icc x y, Complex.I ^ n‖ := norm_nonneg _
  nlinarith [hprod, hge]

private lemma sum_Icc_chi4_eq_complex (x y : ℕ) :
    (∑ n ∈ Finset.Icc x y, chi4 n) = (((∑ n ∈ Finset.Icc x y, Complex.I ^ n).im : ℝ) : ℂ) := by
  rw [show (∑ n ∈ Finset.Icc x y, chi4 n)
        = ∑ n ∈ Finset.Icc x y, (((Complex.I ^ n).im : ℝ) : ℂ) from by
      apply Finset.sum_congr rfl; intro n _; exact chi4_eq_I_im n]
  rw [← Complex.ofReal_sum, ← Complex.im_sum]

/-- Contiguous sums of `χ₄` are bounded by `2` in absolute value. -/
private lemma chi4_interval_sum_le (x y : ℕ) (hxy : x ≤ y) :
    ‖∑ n ∈ Finset.Icc x y, chi4 n‖ ≤ 2 := by
  rw [sum_Icc_chi4_eq_complex]
  calc ‖(((∑ n ∈ Finset.Icc x y, Complex.I ^ n).im : ℝ) : ℂ)‖
      = |(∑ n ∈ Finset.Icc x y, Complex.I ^ n).im| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖∑ n ∈ Finset.Icc x y, Complex.I ^ n‖ := Complex.abs_im_le_norm _
    _ ≤ 2 := sum_Icc_I_pow_norm_le x y hxy

/-! ### Rewriting range sums as interval sums -/

private lemma sum_Icc_one_eq_sum_range_succ (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ k ∈ Finset.range N, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 N]
  rw [Finset.sum_Ico_eq_sum_range f 1 (N + 1)]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.add_comm]

private lemma sum_range_eq_sum_Icc_one_sub_one {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, f n = ∑ n ∈ Finset.Icc 1 (N - 1), f n := by
  rcases N with _ | N
  · simp
  · rw [Nat.succ_sub_one, sum_Icc_one_eq_sum_range_succ f N]
    have h1 : (∑ n ∈ Finset.range (N + 1), f n) = ∑ k ∈ Finset.range N, f (k + 1) := by
      rw [Finset.sum_range_succ', hf, add_zero]
    rw [h1]

/-! ### Elementary real estimates -/

/-- `‖σ + i t‖ ≤ σ + |t|` for `σ ≥ 0`. -/
private lemma norm_s_le (σ t : ℝ) (hσ0 : 0 ≤ σ) :
    ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ σ + |t| := by
  calc ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = σ + |t| := by
        simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs]
        rw [abs_of_nonneg hσ0]

/-- `∑_{1 ≤ n ≤ M} n^{-σ} ≤ e^c (1 + log M)` under the hypotheses of the problem. -/
private lemma sum_Icc_rpow_neg_le (M : ℕ) (hM1 : 1 ≤ M) {σ c L : ℝ}
    (hL : 1 ≤ L) (hlogM : Real.log (M : ℝ) ≤ L) (hσ : 1 - c / L ≤ σ) (hc : 0 ≤ c) :
    ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ) ≤ Real.exp c * (1 + Real.log (M : ℝ)) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hlogM0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
  have hcL : 0 ≤ c / L := div_nonneg hc hLpos.le
  have hterm : ∀ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-1 : ℝ) * Real.exp c := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnle : n ≤ M := (Finset.mem_Icc.mp hn).2
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnle
    have hsplit : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (1 - σ) := by
      rw [show (-σ : ℝ) = -1 + (1 - σ) by ring, Real.rpow_add hnpos]
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hnpos.le (-1))
    by_cases hκ : 1 - σ ≤ 0
    · have h1 : (n : ℝ) ^ (1 - σ) ≤ 1 := by
        have := Real.rpow_le_rpow_of_exponent_le hnn hκ
        simpa using this
      exact le_trans h1 (Real.one_le_exp hc)
    · have hκpos : 0 ≤ 1 - σ := by linarith
      have hpow : (n : ℝ) ^ (1 - σ) ≤ Real.exp c := by
        have h1 : (n : ℝ) ^ (1 - σ) ≤ (M : ℝ) ^ (1 - σ) :=
          Real.rpow_le_rpow hnpos.le hnM hκpos
        rw [Real.rpow_def_of_pos hMpos (1 - σ)] at h1
        refine le_trans h1 ?_
        apply Real.exp_le_exp.mpr
        have hle : 1 - σ ≤ c / L := by linarith
        calc Real.log (M : ℝ) * (1 - σ) ≤ Real.log (M : ℝ) * (c / L) :=
              mul_le_mul_of_nonneg_left hle hlogM0
          _ ≤ L * (c / L) := mul_le_mul_of_nonneg_right hlogM hcL
          _ = c := by field_simp
      exact hpow
  have hharm : (∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-1 : ℝ)) = (harmonic M : ℝ) := by
    rw [show (∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-1 : ℝ)) = ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ from by
          apply Finset.sum_congr rfl; intro n _; rw [Real.rpow_neg_one]]
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  calc ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ)
      ≤ ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-1 : ℝ) * Real.exp c := Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-1 : ℝ)) * Real.exp c := by rw [Finset.sum_mul]
    _ = (harmonic M : ℝ) * Real.exp c := by rw [hharm]
    _ ≤ (1 + Real.log (M : ℝ)) * Real.exp c := by
        apply mul_le_mul_of_nonneg_right (harmonic_le_one_add_log M) (Real.exp_nonneg c)
    _ = Real.exp c * (1 + Real.log (M : ℝ)) := by ring

/-- `M^{1-σ} ≤ 2` under the hypotheses of the problem. -/
private lemma mpow_one_sub_le_two (M : ℕ) {σ c L : ℝ} (hM1 : 1 ≤ (M : ℝ))
    (hc : 0 ≤ c) (hLpos : 0 < L) (hlogM : Real.log (M : ℝ) ≤ L)
    (hσ : 1 - c / L ≤ σ) (hexp : Real.exp c ≤ 2) :
    (M : ℝ) ^ (1 - σ) ≤ 2 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  have hlogM0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  have hcL : 0 ≤ c / L := div_nonneg hc hLpos.le
  by_cases h : 1 - σ ≤ 0
  · have hle := Real.rpow_le_rpow_of_exponent_le hM1 h
    have : (M : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero _
    rw [this] at hle
    linarith
  · have hκpos : 0 ≤ 1 - σ := by linarith
    have h2 : (M : ℝ) ^ (1 - σ) = Real.exp (Real.log (M : ℝ) * (1 - σ)) :=
      Real.rpow_def_of_pos hMpos (1 - σ)
    rw [h2]
    calc Real.exp (Real.log (M : ℝ) * (1 - σ)) ≤ Real.exp c := by
          apply Real.exp_le_exp.mpr
          have hle : 1 - σ ≤ c / L := by linarith
          calc Real.log (M : ℝ) * (1 - σ) ≤ Real.log (M : ℝ) * (c / L) :=
                mul_le_mul_of_nonneg_left hle hlogM0
            _ ≤ L * (c / L) := mul_le_mul_of_nonneg_right hlogM hcL
            _ = c := by field_simp
      _ ≤ 2 := hexp

/-- The numerical factor produced by the Abel-summation tail estimate is bounded by `12`. -/
private lemma tail_factor_bound {M : ℕ} {σ T : ℝ} (hM2 : 2 ≤ (M : ℝ)) (hσ34 : 3 / 4 ≤ σ)
    (hT0 : 0 ≤ T) (hTM : T ≤ (M : ℝ)) (hpow : (M : ℝ) ^ (1 - σ) ≤ 2) :
    2 * (M : ℝ) ^ (-σ) * (1 + (σ + T) / σ) ≤ 12 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hσpos : 0 < σ := by linarith
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by linarith
  have hpow1 : (M : ℝ) ^ (-σ) ≤ 2 * (M : ℝ) ^ (-1 : ℝ) := by
    have h := Real.rpow_add hMpos (-1) (1 - σ)
    rw [show (-1 : ℝ) + (1 - σ) = -σ by ring] at h
    rw [h]
    calc (M : ℝ) ^ (-1 : ℝ) * (M : ℝ) ^ (1 - σ)
        ≤ (M : ℝ) ^ (-1 : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hMpos.le (-1))
      _ = 2 * (M : ℝ) ^ (-1 : ℝ) := by ring
  have hMinv : (M : ℝ)⁻¹ * 2 ≤ 1 := by
    have hle : (M : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hMpos (by norm_num)).mpr hM2
    calc (M : ℝ)⁻¹ * 2 ≤ (2 : ℝ)⁻¹ * 2 := mul_le_mul_of_nonneg_right hle (by norm_num)
      _ = 1 := by norm_num
  have hσ43 : 1 / σ ≤ 4 / 3 := by
    rw [div_le_iff₀ hσpos]; linarith
  have hXeq : 1 + (σ + T) / σ = 2 + T / σ := by
    field_simp; ring
  have hstep2 : (M : ℝ)⁻¹ * (1 + (σ + T) / σ) ≤ 7 / 3 := by
    rw [hXeq, mul_add]
    have hA : (M : ℝ)⁻¹ * 2 ≤ 1 := hMinv
    have hB : (M : ℝ)⁻¹ * (T / σ) ≤ 4 / 3 := by
      have hTM1 : T / (M : ℝ) ≤ 1 := by rw [div_le_one hMpos]; exact hTM
      have heq : (M : ℝ)⁻¹ * (T / σ) = (T / (M : ℝ)) * (1 / σ) := by field_simp
      rw [heq]
      calc (T / (M : ℝ)) * (1 / σ) ≤ 1 * (1 / σ) := by
            apply mul_le_mul_of_nonneg_right hTM1; positivity
        _ = 1 / σ := by ring
        _ ≤ 4 / 3 := hσ43
    linarith
  have hX0 : 0 ≤ 1 + (σ + T) / σ := by positivity
  have hmain : (M : ℝ) ^ (-σ) * (1 + (σ + T) / σ) ≤ (2 * (M : ℝ) ^ (-1 : ℝ)) * (1 + (σ + T) / σ) :=
    mul_le_mul_of_nonneg_right hpow1 hX0
  calc 2 * (M : ℝ) ^ (-σ) * (1 + (σ + T) / σ)
      = 2 * ((M : ℝ) ^ (-σ) * (1 + (σ + T) / σ)) := by ring
    _ ≤ 2 * ((2 * (M : ℝ) ^ (-1 : ℝ)) * (1 + (σ + T) / σ)) := by linarith
    _ = 4 * ((M : ℝ)⁻¹ * (1 + (σ + T) / σ)) := by
        rw [Real.rpow_neg_one]; ring
    _ ≤ 4 * (7 / 3) := by linarith
    _ ≤ 12 := by norm_num

/-- **The same logarithmic bound for the partial sums of the `χ₄` Dirichlet series as
`Commons.NumberTheory.LSeries.exists_bound_partial_sums_chi4_near_one`, but valid for
`1 ≤ |t|` instead of `2 ≤ |t|`.**

There are constants `C, c > 0` such that for all real `σ, t` with `1 ≤ |t|` and
`σ ≥ 1 - c/log(|t|+2)`, and every `N : ℕ`,

`‖∑_{n<N} χ₄(n) n^{-(σ+it)}‖ ≤ C log(|t|+2)`,  where `χ₄(n) = 1` if `n ≡ 1 (4)`,
`χ₄(n) = -1` if `n ≡ 3 (4)` and `χ₄(n) = 0` otherwise.

PROOF: copy the proof of `Commons.NumberTheory.LSeries.exists_bound_partial_sums_chi4_near_one`
(its file `Submission/Commons/NumberTheory/LSeries/exists_bound_partial_sums_chi4_near_one.lean`
contains a complete proof; it is also visible in the workspace) and check that every step
only needs `1 ≤ |t|` rather than `2 ≤ |t|`.  The only place where the size of `|t|` enters is the
choice `M = ⌊|t|⌋ + 1` of the splitting point of the `Abel` summation: for `|t| ≥ 1` we have
`M ≥ 2`, which is all that is used.  Adjust constants if necessary (any `C, c > 0` will do). -/
theorem exists_bound_partial_sums_chi4_near_one_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ σ t : ℝ, 1 ≤ |t| →
      1 - c / Real.log (|t| + 2) ≤ σ → ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N,
          (if n % 4 = 1 then (1 : ℂ) else if n % 4 = 3 then -1 else 0)
            / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log (|t| + 2) := by
  classical
  refine ⟨100, 1 / 4, by norm_num, by norm_num, ?_⟩
  intro σ t ht hσ N
  set L : ℝ := Real.log (|t| + 2) with hLdef
  set M : ℕ := Nat.floor |t| + 1 with hMdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h1 : (1 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
    have h2 : Real.log 3 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hMge : |t| ≤ (M : ℝ) := by
    have h := Nat.lt_floor_add_one |t|
    rw [hMdef]; push_cast; linarith
  have hMle : (M : ℝ) ≤ |t| + 2 := by
    have h := Nat.floor_le (abs_nonneg t)
    rw [hMdef]; push_cast; linarith
  have hM2 : 2 ≤ M := by
    have h1 : (1 : ℕ) ≤ Nat.floor |t| := by
      rw [Nat.le_floor_iff (abs_nonneg t)]
      simpa using ht
    rw [hMdef]; omega
  have hM2r : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hM1 : 1 ≤ M := by omega
  have hlogM : Real.log (M : ℝ) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by linarith) hMle
  have hσL : 1 - (1 / 4) / L ≤ σ := by simpa [hLdef] using hσ
  have hσ34 : 3 / 4 ≤ σ := by
    have hdiv : (1 / 4) / L ≤ 1 / 4 := by
      rw [div_le_iff₀ hLpos]; linarith
    linarith
  have hσpos : 0 < σ := by linarith
  have hexp : Real.exp (1 / 4 : ℝ) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hspos : 0 < s.re := by rw [hsre]; exact hσpos
  have hsum_eq : (∑ n ∈ Finset.range N,
        (if n % 4 = 1 then (1 : ℂ) else if n % 4 = 3 then -1 else 0) / (n : ℂ) ^ s)
      = ∑ n ∈ Finset.Icc 1 (N - 1), chi4 n * (n : ℂ) ^ (-s) := by
    rw [show (∑ n ∈ Finset.range N,
          (if n % 4 = 1 then (1 : ℂ) else if n % 4 = 3 then -1 else 0) / (n : ℂ) ^ s)
        = ∑ n ∈ Finset.range N, chi4 n * (n : ℂ) ^ (-s) from by
          apply Finset.sum_congr rfl; intro n _
          simp only [chi4]
          rw [div_eq_mul_inv, ← Complex.cpow_neg]]
    exact sum_range_eq_sum_Icc_one_sub_one (by simp [chi4_zero]) N
  have hmain : ‖∑ n ∈ Finset.Icc 1 (N - 1), chi4 n * (n : ℂ) ^ (-s)‖ ≤ 100 * L := by
    have hprefix : ∀ K : ℕ, K ≤ M →
        ‖∑ n ∈ Finset.Icc 1 K, chi4 n * (n : ℂ) ^ (-s)‖ ≤ 4 * L := by
      intro K hK
      have h1 : ‖∑ n ∈ Finset.Icc 1 K, chi4 n * (n : ℂ) ^ (-s)‖
          ≤ ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-σ) := by
        calc ‖∑ n ∈ Finset.Icc 1 K, chi4 n * (n : ℂ) ^ (-s)‖
            ≤ ∑ n ∈ Finset.Icc 1 K, ‖chi4 n * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-σ) := by
              apply Finset.sum_le_sum; intro n hn
              have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
              calc ‖chi4 n * (n : ℂ) ^ (-s)‖ ≤ ‖chi4 n‖ * ‖(n : ℂ) ^ (-s)‖ := norm_mul_le _ _
                _ ≤ 1 * (n : ℝ) ^ (-σ) := by
                    have hc := chi4_norm_le_one n
                    have h2 : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-σ) := by
                      rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n) (-s),
                        Complex.neg_re, hsre]
                    rw [h2]
                    exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by positivity) _)
                _ = (n : ℝ) ^ (-σ) := one_mul _
      have h2 : ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-σ) ≤ ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have h1 := Finset.mem_Icc.mp hn
          exact Finset.mem_Icc.mpr ⟨h1.1, le_trans h1.2 hK⟩
        · intro n _ _; exact Real.rpow_nonneg (by positivity) _
      have h3 : ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ)
          ≤ Real.exp (1 / 4) * (1 + Real.log (M : ℝ)) :=
        sum_Icc_rpow_neg_le M hM1 hL1 hlogM hσL (by norm_num)
      have h4 : Real.exp (1 / 4 : ℝ) * (1 + Real.log (M : ℝ)) ≤ 4 * L := by
        have h5 : 1 + Real.log (M : ℝ) ≤ 2 * L := by linarith
        have h6 : 0 < Real.exp (1 / 4 : ℝ) := Real.exp_pos _
        nlinarith [hexp, h5, h6, hL1]
      linarith
    by_cases hcase : N ≤ M
    · have := hprefix (N - 1) (by omega)
      linarith
    · push Not at hcase
      have hMN : M ≤ N - 1 := by omega
      have hsplit : Finset.Icc 1 (N - 1) = Finset.Icc 1 (M - 1) ∪ Finset.Icc M (N - 1) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 (M - 1)) (Finset.Icc M (N - 1)) := by
        rw [Finset.disjoint_left]; intro n hn1 hn2
        simp only [Finset.mem_Icc] at hn1 hn2; omega
      have hpre := hprefix (M - 1) (by omega)
      have htail : ‖∑ n ∈ Finset.Icc M (N - 1), chi4 n * (n : ℂ) ^ (-s)‖ ≤ 12 := by
        have hb := Commons.Analysis.Sums.tail_pow_abel_bound (a := chi4) 2
          (fun x y hxy => chi4_interval_sum_le x y hxy) s hspos hMN hM1
        rw [hsre] at hb
        have hsnorm : ‖s‖ ≤ σ + |t| := by
          rw [hsdef]; exact norm_s_le σ t hσpos.le
        have hpow := mpow_one_sub_le_two M (by linarith : (1 : ℝ) ≤ (M : ℝ))
          (by norm_num) hLpos hlogM hσL hexp
        have hfactor := tail_factor_bound (M := M) (σ := σ) (T := |t|)
          hM2r hσ34 (abs_nonneg t) hMge hpow
        have hle : (1 : ℝ) + ‖s‖ / σ ≤ 1 + (σ + |t|) / σ := by
          have := div_le_div_of_nonneg_right hsnorm hσpos.le
          linarith
        calc ‖∑ n ∈ Finset.Icc M (N - 1), chi4 n * (n : ℂ) ^ (-s)‖
            ≤ 2 * (M : ℝ) ^ (-σ) * (1 + ‖s‖ / σ) := hb
          _ ≤ 2 * (M : ℝ) ^ (-σ) * (1 + (σ + |t|) / σ) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
          _ ≤ 12 := hfactor
      rw [hsplit, Finset.sum_union hdisj]
      calc ‖(∑ n ∈ Finset.Icc 1 (M - 1), chi4 n * (n : ℂ) ^ (-s))
              + ∑ n ∈ Finset.Icc M (N - 1), chi4 n * (n : ℂ) ^ (-s)‖
          ≤ ‖∑ n ∈ Finset.Icc 1 (M - 1), chi4 n * (n : ℂ) ^ (-s)‖
              + ‖∑ n ∈ Finset.Icc M (N - 1), chi4 n * (n : ℂ) ^ (-s)‖ := norm_add_le _ _
        _ ≤ 4 * L + 12 := add_le_add hpre htail
        _ ≤ 100 * L := by linarith
  calc ‖∑ n ∈ Finset.range N,
          (if n % 4 = 1 then (1 : ℂ) else if n % 4 = 3 then -1 else 0) / (n : ℂ) ^ s‖
      = ‖∑ n ∈ Finset.Icc 1 (N - 1), chi4 n * (n : ℂ) ^ (-s)‖ := by rw [hsum_eq]
    _ ≤ 100 * L := hmain
    _ = 100 * Real.log (|t| + 2) := by rw [hLdef]


end Commons.NumberTheory.LSeries
