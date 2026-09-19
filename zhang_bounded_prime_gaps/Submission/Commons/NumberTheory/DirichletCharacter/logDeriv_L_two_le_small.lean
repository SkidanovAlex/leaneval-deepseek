import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_L_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le

open Complex DirichletCharacter
open scoped Real BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ## Two refined tail bounds

To get the constant `3` in the logarithmic-derivative bound on `Re s = 2` we need the sharper
numerical bounds
`∑_{n ≥ 2} ln n / n² ≤ 1` (for the derivative) and `∑_{n ≥ 2} 1 / n² ≤ 2/3` (for the lower bound
`|L(χ, 2+iT)| ≥ 1/3`).  Both are proved below from elementary estimates. -/

/-! ### Log-bounds for small integers -/

private lemma log2_lt : Real.log (2 : ℝ) < (7 : ℝ) / 10 := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

private lemma log3_lt : Real.log (3 : ℝ) < (11 : ℝ) / 10 := by
  have h := Real.log_three_lt_d9
  norm_num at h ⊢
  linarith

private lemma log2_gt : (2 : ℝ) / 3 < Real.log (2 : ℝ) := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

private lemma log4_gt_four_thirds : (4 : ℝ) / 3 < Real.log (4 : ℝ) := by
  have h2 := log2_gt
  have h4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    rw [Real.log_pow]
    norm_num
  nlinarith

/-! ### The bound `∑_{n ≥ 2} ln n / n² ≤ 1`

Proof.  For `m ≥ 1` put `A(m) = (1 + ln m)/m`.  For every `n ≥ 4` we show
`ln n / n² ≤ A(n-1) - A(n)`: equivalently `n·ln(n/(n-1)) ≤ 1 + ln n/n`, which follows from
`ln(1+u) ≤ u` (with `u = 1/(n-1)`) and `ln n ≥ n/(n-1)` (since `ln n ≥ ln 4 ≥ 4/3 ≥ n/(n-1)`).
Summing from `n = 4` telescopes the tail to `A(3) ≤ 7/10` (using `ln 3 < 11/10`), and the two
head terms `n = 2, 3` contribute at most `7/40 + 11/90` (using `ln 2 < 7/10`, `ln 3 < 11/10`),
so every partial sum is at most `359/360 < 1`. -/

private def A (m : ℕ) : ℝ := (1 + Real.log (m : ℝ)) / (m : ℝ)

private lemma A_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ A m := by
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  dsimp [A]
  positivity

private lemma A3_le : A 3 ≤ (7 : ℝ) / 10 := by
  dsimp [A]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  nlinarith [log3_lt]

private lemma log_div_sq_le_A_sub {n : ℕ} (hn : 4 ≤ n) :
    Real.log (n : ℝ) / (n : ℝ) ^ 2 ≤ A (n - 1) - A n := by
  let x : ℝ := Real.log (n : ℝ)
  let y : ℝ := Real.log (((n - 1 : ℕ) : ℝ))
  have hpos : 0 < ((n - 1 : ℕ) : ℝ) := by
    have : 0 < n - 1 := by omega
    exact_mod_cast this
  have hposn : 0 < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn1ne : (n : ℝ) - 1 ≠ 0 := by
    have hn4r : 4 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hnm1c : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hlin : Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ 1 / ((n - 1 : ℕ) : ℝ) := by
    have hle := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / ((n - 1 : ℕ) : ℝ) by positivity)
    have hu : 1 + 1 / ((n - 1 : ℕ) : ℝ) = (n : ℝ) / ((n - 1 : ℕ) : ℝ) := by
      rw [hnm1c]
      field_simp [hn1ne]
      ring
    rw [hu] at hle
    have hred : (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 = 1 / ((n - 1 : ℕ) : ℝ) := by
      rw [hnm1c]
      field_simp [hn1ne]
      ring
    rwa [hred] at hle
  have hmono : Real.log (4 : ℝ) ≤ x := by
    dsimp [x]
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    have : (4 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hn4r : 4 ≤ (n : ℝ) := by exact_mod_cast hn
  have h4le : (n : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ (4 : ℝ) / 3 := by
    rw [hnm1c]
    rw [div_le_iff₀ (show 0 < (n : ℝ) - 1 by nlinarith)]
    nlinarith
  have hlog4le : (4 : ℝ) / 3 ≤ Real.log (4 : ℝ) := le_of_lt log4_gt_four_thirds
  have hnn : (n : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ x := by
    calc
      (n : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ (4 : ℝ) / 3 := h4le
      _ ≤ Real.log (4 : ℝ) := hlog4le
      _ ≤ x := hmono
  have hbig : (n : ℝ) * (1 / ((n - 1 : ℕ) : ℝ)) ≤ 1 + x / (n : ℝ) := by
    have hstep : 1 / ((n - 1 : ℕ) : ℝ) ≤ x / (n : ℝ) := by
      have hmul : ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) / (n : ℝ) ≤ x / (n : ℝ) := by
        exact div_le_div_of_nonneg_right hnn (by positivity)
      have : ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) / (n : ℝ) = 1 / ((n - 1 : ℕ) : ℝ) := by
        field_simp [hposn.ne', hpos.ne']
      rwa [this] at hmul
    calc
      (n : ℝ) * (1 / ((n - 1 : ℕ) : ℝ)) = 1 + 1 / ((n - 1 : ℕ) : ℝ) := by
        rw [hnm1c]
        field_simp [hposn.ne', hn1ne]
        ring
      _ ≤ 1 + x / (n : ℝ) := by linarith [hstep]
  have hlogdiv : Real.log (n : ℝ) - Real.log (((n - 1 : ℕ) : ℝ)) = Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    rw [← Real.log_div hposn.ne' hpos.ne']
  have hperterm : (n : ℝ) * Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ 1 + x / (n : ℝ) := by
    calc
      (n : ℝ) * Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ (n : ℝ) * (1 / ((n - 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlin (by positivity)
      _ ≤ 1 + x / (n : ℝ) := hbig
  have hperterm' : (n : ℝ) * (x - y) ≤ 1 + x / (n : ℝ) := by
    rw [← hlogdiv] at hperterm
    simpa [x, y] using hperterm
  have hnum : (n : ℝ) ^ 2 * (x - y) ≤ (n : ℝ) + x := by
    have hscaled : (n : ℝ) * ((n : ℝ) * (x - y)) ≤ (n : ℝ) * (1 + x / (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hperterm' (by positivity)
    have hL : (n : ℝ) * ((n : ℝ) * (x - y)) = (n : ℝ) ^ 2 * (x - y) := by ring
    have hR : (n : ℝ) * (1 + x / (n : ℝ)) = (n : ℝ) + x := by
      field_simp [hposn.ne']
    rwa [hL, hR] at hscaled
  have hnum_nonneg : 0 ≤ (n : ℝ) + x - (n : ℝ) ^ 2 * (x - y) := by linarith
  have hd0 : 0 < (n : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) := by positivity
  have hdiv_nonneg : 0 ≤ ((n : ℝ) + x - (n : ℝ) ^ 2 * (x - y)) / ((n : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ)) := by
    exact div_nonneg hnum_nonneg (le_of_lt hd0)
  have heq : ((n : ℝ) + x - (n : ℝ) ^ 2 * (x - y)) / ((n : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ))
      = ((1 + y) / ((n - 1 : ℕ) : ℝ) - (1 + x) / (n : ℝ)) - x / (n : ℝ) ^ 2 := by
    rw [hnm1c]
    field_simp [hposn.ne', hn1ne]
    ring
  have hmain : x / (n : ℝ) ^ 2 ≤ (1 + y) / ((n - 1 : ℕ) : ℝ) - (1 + x) / (n : ℝ) := by
    have : 0 ≤ ((1 + y) / ((n - 1 : ℕ) : ℝ) - (1 + x) / (n : ℝ)) - x / (n : ℝ) ^ 2 := by
      simpa [heq] using hdiv_nonneg
    linarith
  have hAm : A (n - 1) = (1 + y) / ((n - 1 : ℕ) : ℝ) := by
    dsimp [A, y]
  have hAn : A n = (1 + x) / (n : ℝ) := by
    dsimp [A, x]
  rw [hAm, hAn]
  simpa [x] using hmain

private lemma tail_le_A3 (K : ℕ) :
    (∑ n ∈ (Finset.Ico (4:ℕ) K), Real.log (n : ℝ) / (n : ℝ) ^ 2) ≤ 7 / 10 := by
  by_cases hK : K ≤ 4
  · have hI : Finset.Ico (4:ℕ) K = ∅ := by
      ext n
      simp [Finset.mem_Ico]
      omega
    rw [hI]
    norm_num
  · have hK5 : 5 ≤ K := by omega
    have hsum_le : (∑ n ∈ (Finset.Ico (4:ℕ) K), Real.log (n : ℝ) / (n : ℝ) ^ 2)
        ≤ ∑ n ∈ (Finset.Ico (4:ℕ) K), (A (n - 1) - A n) := by
      exact Finset.sum_le_sum (fun n hn => log_div_sq_le_A_sub (n := n) ((Finset.mem_Ico.mp hn).1))
    have htel_eq : (∑ n ∈ (Finset.Ico (4:ℕ) K), (A (n - 1) - A n)) = A 3 - A (K - 1) := by
      calc
        (∑ n ∈ (Finset.Ico (4:ℕ) K), (A (n - 1) - A n))
            = ∑ r ∈ Finset.range (K - 4), (A (r + 3) - A (r + 4)) := by
              rw [Finset.sum_Ico_eq_sum_range]
              apply Finset.sum_congr rfl
              intro r hr
              have h1 : (4 + r - 1 : ℕ) = r + 3 := by omega
              have h2 : (4 + r : ℕ) = r + 4 := by omega
              rw [h1, h2]
        _ = ∑ r ∈ Finset.range (K - 4), (A (r + 3) - A (r + 1 + 3)) := by
              apply Finset.sum_congr rfl
              intro r hr
              have h3 : (r + 4 : ℕ) = r + 1 + 3 := by omega
              rw [h3]
        _ = A 3 - A ((K - 4) + 3) := by
              rw [Finset.sum_range_sub' (f := fun r : ℕ => A (r + 3)) (K - 4)]
        _ = A 3 - A (K - 1) := by
              have hsub : (K - 4) + 3 = K - 1 := by omega
              rw [hsub]
    have htelesc : (∑ n ∈ (Finset.Ico (4:ℕ) K), (A (n - 1) - A n)) ≤ A 3 - A (K - 1) := by
      rw [htel_eq]
    calc
      (∑ n ∈ (Finset.Ico (4:ℕ) K), Real.log (n : ℝ) / (n : ℝ) ^ 2)
          ≤ ∑ n ∈ (Finset.Ico (4:ℕ) K), (A (n - 1) - A n) := hsum_le
      _ ≤ A 3 - A (K - 1) := htelesc
      _ ≤ A 3 := by
        have hpos : 0 ≤ A (K - 1) := A_nonneg (by omega)
        linarith
      _ ≤ 7 / 10 := A3_le

private lemma term2_le : Real.log (2 : ℝ) / (2 : ℝ) ^ 2 ≤ 7 / 40 := by
  have h := log2_lt
  calc
    Real.log (2 : ℝ) / (2 : ℝ) ^ 2 ≤ (7 / 10) / (2 : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right h.le (by positivity)
    _ = 7 / 40 := by norm_num

private lemma term3_le : Real.log (3 : ℝ) / (3 : ℝ) ^ 2 ≤ 11 / 90 := by
  have h := log3_lt
  calc
    Real.log (3 : ℝ) / (3 : ℝ) ^ 2 ≤ (11 / 10) / (3 : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right h.le (by positivity)
    _ = 11 / 90 := by norm_num

private lemma head23_le : (∑ n ∈ (Finset.Ico (2:ℕ) 4), Real.log (n : ℝ) / (n : ℝ) ^ 2)
    ≤ 107 / 360 := by
  have hsum : (∑ n ∈ (Finset.Ico (2:ℕ) 4), Real.log (n : ℝ) / (n : ℝ) ^ 2)
      = Real.log (2 : ℝ) / (2 : ℝ) ^ 2 + Real.log (3 : ℝ) / (3 : ℝ) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show (4 - 2 : ℕ) = 2 by norm_num]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    norm_num
  calc
    (∑ n ∈ (Finset.Ico (2:ℕ) 4), Real.log (n : ℝ) / (n : ℝ) ^ 2)
        = Real.log (2 : ℝ) / (2 : ℝ) ^ 2 + Real.log (3 : ℝ) / (3 : ℝ) ^ 2 := hsum
    _ ≤ 7 / 40 + 11 / 90 := by exact add_le_add term2_le term3_le
    _ = 107 / 360 := by norm_num

/-- Partial sums of the log-guard `∑_{2 ≤ n} ln n / n²` are bounded by `1`. -/
private lemma partial_guard1_le (K : ℕ) :
    (∑ n ∈ Finset.range K, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0)) ≤ 1 := by
  have hrewrite : (∑ n ∈ Finset.range K, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0))
      = ∑ n ∈ (Finset.Ico (2:ℕ) K), (Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
    rw [← Finset.sum_filter (s := Finset.range K) (p := fun n : ℕ => 2 ≤ n)
      (f := fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2)]
    congr 1
    ext n
    simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hrewrite]
  by_cases hK : K ≤ 4
  · calc
      (∑ n ∈ (Finset.Ico (2:ℕ) K), Real.log (n : ℝ) / (n : ℝ) ^ 2)
          ≤ ∑ n ∈ (Finset.Ico (2:ℕ) 4), Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico (by omega) hK)
              (by intro n hn h; positivity)
      _ ≤ 107 / 360 := head23_le
      _ ≤ 1 := by norm_num
  · have hK5 : 5 ≤ K := by omega
    rw [← Finset.sum_Ico_consecutive (f := fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2)
      (m := (2:ℕ)) (n := (4:ℕ)) (k := K) (by norm_num) (by omega : (4 : ℕ) ≤ K)]
    calc
      (∑ n ∈ (Finset.Ico (2:ℕ) (4:ℕ)), Real.log (n : ℝ) / (n : ℝ) ^ 2)
          + (∑ n ∈ (Finset.Ico (4:ℕ) K), Real.log (n : ℝ) / (n : ℝ) ^ 2)
          ≤ 107 / 360 + 7 / 10 := by
            exact add_le_add head23_le (tail_le_A3 K)
      _ ≤ 1 := by norm_num

private lemma guard1_nonneg (n : ℕ) :
    0 ≤ if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0 := by
  by_cases h : 2 ≤ n
  · simp [h]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) (sq_nonneg (n : ℝ))
  · simp [h]

private lemma guard1_summable :
    Summable (fun n : ℕ => if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by
  exact summable_of_sum_range_le guard1_nonneg partial_guard1_le

private lemma guard1_tsum_le_one :
    (∑' n : ℕ, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0)) ≤ 1 := by
  exact Real.tsum_le_of_sum_range_le guard1_nonneg partial_guard1_le

/-! ### The bound `∑_{n ≥ 2} 1 / n² ≤ 2/3`

Proof: `1/4 + 1/9 + 1/16 + 1/25 + 1/5 = 2389/3600 < 2/3`, where the tail `∑_{n ≥ 6} 1/n² ≤ 1/5`
uses `1/n² ≤ 1/(n-1) - 1/n` (telescoping, via `sum_Ioc_inv_sq_le_sub`). -/

private lemma tail_6_le (K : ℕ) (hK : 6 ≤ K) :
    (∑ n ∈ (Finset.Ico (6:ℕ) K), (((n : ℝ) ^ 2)⁻¹)) ≤ 1 / 5 := by
  have heq : (Finset.Ico (6:ℕ) K) = (Finset.Ioc (5:ℕ) (K - 1)) := by
    ext n
    simp [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [heq]
  have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 5) (n := K - 1) (by norm_num : (5:ℕ) ≠ 0)
    (by omega : (5:ℕ) ≤ K - 1)
  calc
    (∑ i ∈ Finset.Ioc (5 : ℕ) (K - 1), ((i : ℝ) ^ 2)⁻¹) ≤ (5 : ℝ)⁻¹ - ((K - 1 : ℕ) : ℝ)⁻¹ := h
    _ ≤ 1 / 5 := by
      have hpos : 0 ≤ ((K - 1 : ℕ) : ℝ)⁻¹ := by positivity
      calc
        (5 : ℝ)⁻¹ - ((K - 1 : ℕ) : ℝ)⁻¹ ≤ (5 : ℝ)⁻¹ := by linarith
        _ = 1 / 5 := by norm_num

private lemma sum_head26 : (∑ n ∈ (Finset.Ico (2:ℕ) 6), (((n : ℝ) ^ 2)⁻¹)) = 1669 / 3600 := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num

/-- Partial sums of the tail majorant `∑_{2 ≤ n} 1 / n²` are bounded by `2 / 3`. -/
private lemma partial_guard2_le (K : ℕ) :
    (∑ n ∈ Finset.range K, (if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0)) ≤ 2 / 3 := by
  have hrewrite : (∑ n ∈ Finset.range K, (if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0))
      = ∑ n ∈ (Finset.Ico (2:ℕ) K), (((n : ℝ) ^ 2)⁻¹) := by
    rw [← Finset.sum_filter (s := Finset.range K) (p := fun n : ℕ => 2 ≤ n)
      (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)]
    congr 1
    ext n
    simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hrewrite]
  by_cases hK : K ≤ 6
  · calc
      (∑ n ∈ (Finset.Ico (2:ℕ) K), (((n : ℝ) ^ 2)⁻¹))
          ≤ ∑ n ∈ (Finset.Ico (2:ℕ) 6), (((n : ℝ) ^ 2)⁻¹) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico (by omega) hK)
              (by intro n hn h; positivity)
      _ = 1669 / 3600 := sum_head26
      _ ≤ 2 / 3 := by norm_num
  · have hK6 : 6 ≤ K := by omega
    rw [← Finset.sum_Ico_consecutive (f := fun n : ℕ => (((n : ℝ) ^ 2)⁻¹))
      (m := (2:ℕ)) (n := (6:ℕ)) (k := K) (by norm_num) hK6]
    calc
      (∑ n ∈ (Finset.Ico (2:ℕ) (6:ℕ)), (((n : ℝ) ^ 2)⁻¹))
          + (∑ n ∈ (Finset.Ico (6:ℕ) K), (((n : ℝ) ^ 2)⁻¹))
          ≤ 1669 / 3600 + 1 / 5 := by
            exact add_le_add (le_of_eq sum_head26) (tail_6_le K hK6)
      _ ≤ 2 / 3 := by norm_num

private lemma guard2_nonneg (n : ℕ) : 0 ≤ if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0 := by
  by_cases h : 2 ≤ n
  · simp [h]
  · simp [h]

private lemma guard2_summable :
    Summable (fun n : ℕ => if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0) := by
  exact summable_of_sum_range_le guard2_nonneg partial_guard2_le

/-! ### If `|L - 1| ≤ 2/3` then `|L| ≥ 1/3` -/

private lemma norm_LSeries_sub_one_le_two_thirds {f : ℕ → ℂ} {s : ℂ} (hf1 : f 1 = 1)
    (hsum : LSeriesSummable f s)
    (hterm : ∀ n : ℕ, 2 ≤ n → ‖LSeries.term f s n‖ ≤ ((n : ℝ) ^ 2)⁻¹) :
    ‖LSeries f s - 1‖ ≤ 2 / 3 := by
  let a : ℕ → ℂ := LSeries.term f s
  let c : ℕ → ℂ := fun n => if n = 1 then 0 else a n
  let guard : ℕ → ℝ := fun n => if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0
  have hc_le_guard : ∀ n : ℕ, ‖c n‖ ≤ guard n := by
    intro n
    by_cases hn1 : n = 1
    · subst n
      simp [c, guard]
    · by_cases hn0 : n = 0
      · subst n
        simp [c, guard, a]
      · have h2 : 2 ≤ n := by omega
        have hc : c n = a n := by simp [c, hn1]
        have hg : guard n = ((n : ℝ) ^ 2)⁻¹ := by simp [guard, h2]
        rw [hc, hg]
        exact hterm n h2
  have hnonneg : ∀ n : ℕ, 0 ≤ ‖c n‖ := fun n => norm_nonneg _
  have hps : ∀ K : ℕ, (∑ i ∈ Finset.range K, ‖c i‖) ≤ 2 / 3 := by
    intro K
    calc
      (∑ i ∈ Finset.range K, ‖c i‖) ≤ ∑ i ∈ Finset.range K, guard i := by
        exact Finset.sum_le_sum (fun i _ => hc_le_guard i)
      _ ≤ 2 / 3 := partial_guard2_le K
  have hsumm_c_norm : Summable (fun n => ‖c n‖) := summable_of_sum_range_le hnonneg hps
  have htsum_c_norm : (∑' n, ‖c n‖) ≤ 2 / 3 := Real.tsum_le_of_sum_range_le hnonneg hps
  have htail : (∑' n, c n) = (∑' n, a n) - 1 := by
    have hsum_a : Summable a := hsum
    have hsplit := Summable.tsum_eq_add_tsum_ite (f := a) hsum_a (b := 1)
    have ha1 : a 1 = 1 := by
      simp [a, hf1]
    calc
      (∑' n, c n) = (a 1 + ∑' n, c n) - a 1 := by ring
      _ = (∑' n, a n) - 1 := by
        rw [← hsplit]
        rw [ha1]
  have hL : LSeries f s - 1 = (∑' n, c n) := by
    change (∑' n : ℕ, LSeries.term f s n) - 1 = (∑' n : ℕ, c n)
    rw [← htail]
  have hnorm : ‖(∑' n, c n)‖ ≤ 2 / 3 := (norm_tsum_le_tsum_norm hsumm_c_norm).trans htsum_c_norm
  rw [hL]
  exact hnorm

private lemma char_term_sq_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖LSeries.term (fun m : ℕ => (χ (m : ZMod N) : ℂ)) ((2 : ℂ) + Complex.I * (T : ℂ)) n‖
      ≤ ((n : ℝ) ^ 2)⁻¹ := by
  rw [LSeries.norm_term_eq]
  have hn0 : n ≠ 0 := by omega
  rw [if_neg hn0]
  have hs : (((2 : ℂ) + Complex.I * (T : ℂ))).re = 2 := by simp
  rw [hs]
  norm_num
  rw [← one_div]
  exact div_le_div_of_nonneg_right (by simpa using (norm_le_one χ (n : ZMod N))) (sq_nonneg _)

/-- `|L(χ, 2 + iT)| ≥ 1/3` for every non-trivial Dirichlet character `χ`. -/
private lemma L_lower_one_third {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (T : ℝ) : (1 : ℝ) / 3 ≤ ‖DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
  let f : ℕ → ℂ := fun m : ℕ => (χ (m : ZMod N) : ℂ)
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hs : 1 < s.re := by simp [s]
  have hsum : LSeriesSummable f s := by
    simpa [f] using DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hf1 : f 1 = 1 := by
    simp [f]
  have hterm : ∀ n : ℕ, 2 ≤ n → ‖LSeries.term f s n‖ ≤ ((n : ℝ) ^ 2)⁻¹ := by
    intro n hn
    simpa [f, s] using char_term_sq_bound χ T hn
  have hnorm_series : ‖LSeries f s - 1‖ ≤ 2 / 3 :=
    norm_LSeries_sub_one_le_two_thirds (f := f) (s := s) hf1 hsum hterm
  have hLF : LFunction χ s = LSeries f s := by
    simpa [f] using DirichletCharacter.LFunction_eq_LSeries χ hs
  have hnormLF : ‖LFunction χ s - 1‖ ≤ 2 / 3 := by
    rw [hLF]
    exact hnorm_series
  have htri : ‖(1 : ℂ)‖ - ‖LFunction χ s‖ ≤ ‖LFunction χ s - 1‖ := by
    simpa [norm_sub_rev] using norm_sub_norm_le (a := (1 : ℂ)) (b := LFunction χ s)
  have hmain : (1 : ℝ) / 3 ≤ ‖LFunction χ s‖ := by
    have h2 : ‖(1 : ℂ)‖ - ‖LFunction χ s‖ ≤ 2 / 3 := htri.trans hnormLF
    have h3 : (1 : ℝ) - ‖LFunction χ s‖ ≤ 2 / 3 := by simpa using h2
    linarith
  simpa [s] using hmain

/-! ### `‖L′(χ, s)‖ ≤ 1` on the line `Re s = 2` -/

private lemma deriv_norm_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) :
    ‖deriv (LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 1 := by
  let f : ℕ → ℂ := fun n : ℕ => (χ (n : ZMod N) : ℂ)
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hs1 : 1 < s.re := by simp [s]
  have hs2 : s.re = 2 := by simp [s]
  have hder : deriv (LFunction χ) s = -LSeries (LSeries.logMul f) s := by
    have h1 := DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs1
    have habs : LSeries.abscissaOfAbsConv f < s.re := by
      have h := DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) χ
      rw [show LSeries.abscissaOfAbsConv f = 1 by simpa [f] using h]
      rw [hs2]
      exact EReal.coe_lt_coe_iff.mpr (by norm_num : (1 : ℝ) < 2)
    have h2 := LSeries_deriv (f := f) (s := s) habs
    calc
      deriv (LFunction χ) s = deriv (LSeries f) s := by simpa [f] using h1
      _ = -LSeries (LSeries.logMul f) s := by simpa [f] using h2
  have hterm : ∀ n : ℕ, ‖LSeries.term (LSeries.logMul f) s n‖ ≤
      (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by
    intro n
    by_cases hn : 2 ≤ n
    · have hn0 : n ≠ 0 := by omega
      have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      have hn0r : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hlogs : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
        symm
        exact Complex.ofReal_log hn0r
      have hnormlog : ‖Complex.log (n : ℂ)‖ = Real.log (n : ℝ) := by
        rw [hlogs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1r)]
      have hnormcoef : ‖LSeries.logMul f n‖ ≤ Real.log (n : ℝ) := by
        calc
          ‖LSeries.logMul f n‖ = ‖Complex.log (n : ℂ)‖ * ‖(χ (n : ZMod N) : ℂ)‖ := by
            simp [LSeries.logMul, f]
          _ ≤ ‖Complex.log (n : ℂ)‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ (n : ZMod N)) (norm_nonneg _)
          _ = Real.log (n : ℝ) := by rw [mul_one, hnormlog]
      have hnormden : (n : ℝ) ^ s.re = (n : ℝ) ^ 2 := by
        rw [hs2]
        simp
      calc
        ‖LSeries.term (LSeries.logMul f) s n‖
            = ‖LSeries.logMul f n‖ / (n : ℝ) ^ s.re := by
              rw [LSeries.norm_term_eq]
              simp [hn0]
        _ = ‖LSeries.logMul f n‖ / (n : ℝ) ^ 2 := by rw [hnormden]
        _ ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right hnormcoef (sq_nonneg _)
        _ = (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) := by simp [hn]
    · have hsmall : n = 0 ∨ n = 1 := by omega
      rcases hsmall with rfl | rfl
      · simp
      · simp [LSeries.logMul, f]
  have hsumm_norm : Summable (fun n : ℕ => ‖LSeries.term (LSeries.logMul f) s n‖) := by
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm guard1_summable
  calc
    ‖deriv (LFunction χ) s‖ = ‖LSeries (LSeries.logMul f) s‖ := by
      rw [hder, norm_neg]
    _ = ‖(∑' n, LSeries.term (LSeries.logMul f) s n)‖ := rfl
    _ ≤ ∑' n : ℕ, ‖LSeries.term (LSeries.logMul f) s n‖ := norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' n : ℕ, (if 2 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) :=
      Summable.tsum_le_tsum hterm hsumm_norm guard1_summable
    _ ≤ 1 := guard1_tsum_le_one

/-- Tightened logarithmic-derivative bound for a non-trivial Dirichlet L-function on
`Re s = 2`: `‖deriv (LFunction χ) (2+iT) / LFunction χ (2+iT)‖ ≤ 3` for all real `T`.

Method (refine the proof of `Commons.NumberTheory.DirichletCharacter.logDeriv_L_two_le`):
`LFunction χ (2+iT) = LSeries (χ·) (2+iT)` (convergence half-plane) with
`deriv (LSeries f) s = -LSeries (logMul f) s` (`LSeries_deriv`), so
`‖deriv L (2+iT)‖ ≤ ∑_{n≥2} (log n)/n² ≤ 1` (prove the tail bound elementarily, e.g.
`log n ≤ √n` for `n ≥ 2` and `∑_{n≥2} n^(−3/2) ≤ 2` by an integral comparison, or a sharper
elementary bound), while `‖LFunction χ (2+iT)‖ ≥ 1/3` (from
`‖LFunction χ (2+iT) - 1‖ ≤ ∑_{n≥2} 1/n² = ζ(2)-1 ≤ 2/3`; note `ζ(2)-1 < 2/3` by
`∑_{n≥2} n⁻² ≤ ∫_1^∞ x⁻² dx + 1 = 2`... take care to prove `ζ(2)-1 ≤ 2/3` properly, e.g.
`∑_{n≥2} n⁻² ≤ 1/4 + ∫_2^∞ x⁻² dx = 3/4` is not enough — split `2..3` by hand or use
`∑_{n≥2} n⁻² = (∑_{n≥2,n≤3} n⁻²) + (∑_{n≥4} n⁻²) ≤ 1/4 + 1/9 + ∫_3^∞ x⁻² dx < 2/3`).
Then `‖L′/L‖ ≤ 1 / (1/3) = 3`.  If you cannot quite reach `3`, state `4` instead (and note
it); `3` is preferred. -/
theorem logDeriv_L_two_le_small {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (T : ℝ) :
    ‖deriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ)) /
      DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 3 := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hdernorm : ‖deriv (LFunction χ) s‖ ≤ 1 := by
    simpa [s] using deriv_norm_le_one χ T
  have hden : (1 : ℝ) / 3 ≤ ‖LFunction χ s‖ := by
    simpa [s] using L_lower_one_third χ hχ T
  have hdenpos : 0 < ‖LFunction χ s‖ := by linarith
  rw [norm_div]
  rw [div_le_iff₀ hdenpos]
  have h2b : 1 ≤ 3 * ‖LFunction χ s‖ := by
    calc
      1 ≤ 3 * ((1 : ℝ) / 3) := by norm_num
      _ ≤ 3 * ‖LFunction χ s‖ := mul_le_mul_of_nonneg_left hden (by norm_num)
  nlinarith

end Commons.NumberTheory.DirichletCharacter