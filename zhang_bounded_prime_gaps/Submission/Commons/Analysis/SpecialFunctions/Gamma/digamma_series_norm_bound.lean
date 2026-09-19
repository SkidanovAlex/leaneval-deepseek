import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le

open Complex
open scoped Real BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma


/-- the complex term of the series -/
def dgTerm (x y : ℝ) (n : ℕ) : ℝ :=
  ‖(((n : ℂ) + 1)⁻¹ - ((((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ))⁻¹))‖

/-- complex algebra: norm of the term equals ‖z−1‖/((n+1)‖z+n‖) -/
lemma dgTerm_eq_norm_div (x y : ℝ) (hx1 : (1 : ℝ) / 4 ≤ x) (n : ℕ) :
    dgTerm x y n =
      ‖((x : ℂ) + (y : ℂ) * Complex.I) - 1‖ /
        (((n : ℝ) + 1) * ‖(x : ℂ) + (y : ℂ) * Complex.I + (n : ℂ)‖) := by
  have ha_ne : ((n : ℂ) + 1) ≠ 0 := by
    have hnorm : 0 < ‖((n : ℂ) + 1)‖ := by
      have hre : (((n : ℂ) + 1).re) = (n : ℝ) + 1 := by simp
      have habs : |(((n : ℂ) + 1).re)| ≤ ‖((n : ℂ) + 1)‖ := Complex.abs_re_le_norm _
      rw [hre] at habs
      have hpos : 0 < |(n : ℝ) + 1| := by positivity
      exact lt_of_lt_of_le hpos habs
    exact norm_pos_iff.mp hnorm
  have hz_ne : ((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ) ≠ 0 := by
    have hre : ((((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ)).re) = x + (n : ℝ) := by simp
    intro hz0
    have hre0 : ((((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ)).re) = 0 := congrArg Complex.re hz0
    rw [hre] at hre0
    linarith
  have hden : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have harg : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [harg]
    rw [Complex.norm_real ((n : ℝ) + 1)]
    exact abs_of_nonneg (by positivity)
  have halg : (((n : ℂ) + 1)⁻¹ - ((((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ))⁻¹)) =
      ((((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ)) - ((n : ℂ) + 1)) /
        (((n : ℂ) + 1) * (((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ))) := by
    field_simp [ha_ne, hz_ne]
  have hargs : ((((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ)) - ((n : ℂ) + 1)) =
      ((x : ℂ) + (y : ℂ) * Complex.I) - 1 := by
    ring
  calc
    dgTerm x y n =
        ‖((((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ)) - ((n : ℂ) + 1)) /
          (((n : ℂ) + 1) * (((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ)))‖ := by
      rw [dgTerm, halg]
    _ = ‖((x : ℂ) + (y : ℂ) * Complex.I) - 1‖ /
          (((n : ℝ) + 1) * ‖(x : ℂ) + (y : ℂ) * Complex.I + (n : ℂ)‖) := by
      rw [norm_div, norm_mul, hden, hargs]

/-- ‖z−1‖ ≤ |x−1| + |y| where z = x + iy -/
lemma norm_z_sub_one_le (x y : ℝ) : ‖((x : ℂ) + (y : ℂ) * Complex.I) - 1‖ ≤ |x - 1| + |y| := by
  calc
    ‖((x : ℂ) + (y : ℂ) * Complex.I) - 1‖ = ‖(((x : ℂ) - 1) + (y : ℂ) * Complex.I)‖ := by ring_nf
    _ ≤ ‖((x : ℂ) - 1)‖ + ‖((y : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = |x - 1| + |y| := by
      have hsub : (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [hsub, norm_mul, Complex.norm_I]
      rw [Complex.norm_real (x - 1), Complex.norm_real y]
      rw [mul_one]
      rfl

/-- ‖z+n‖ ≥ n + x (real part bound) -/
lemma norm_z_add_nat_ge (x y : ℝ) (n : ℕ) :
    (n : ℝ) + x ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I + (n : ℂ)‖ := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I + (n : ℂ)
  have hre : z.re = (n : ℝ) + x := by simp [z]; ring
  simpa [z, hre] using Complex.re_le_norm z

/-- ‖z+n‖ ≥ |y| (imaginary part bound) -/
lemma norm_z_add_nat_ge_abs_y (x y : ℝ) (n : ℕ) :
    |y| ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I + (n : ℂ)‖ := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I + (n : ℂ)
  have him : z.im = y := by simp [z]
  simpa [z, him] using Complex.abs_im_le_norm z

/-- pure-real: (A+Y)/(d·w) ≤ A/(d·u) + 1/d under w ≥ u, w ≥ Y, all nonneg -/
lemma real_bound_head {d u w A Y : ℝ} (hd : 0 < d) (hu : 0 < u) (hw : 0 < w)
    (hA : 0 ≤ A) (hwu : u ≤ w) (hwy : Y ≤ w) :
    (A + Y) / (d * w) ≤ A / (d * u) + 1 / d := by
  have hAdiv : A / (d * w) ≤ A / (d * u) := by
    exact div_le_div_of_nonneg_left hA (mul_pos hd hu) (mul_le_mul_of_nonneg_left hwu hd.le)
  have hYdiv : Y / (d * w) ≤ 1 / d := by
    have h1 : Y / w ≤ 1 := div_le_one_of_le₀ hwy hw.le
    have heq : Y / (d * w) = (1 / d) * (Y / w) := by
      field_simp [hd.ne', hw.ne']
    rw [heq]
    calc
      (1 / d) * (Y / w) ≤ (1 / d) * 1 :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (one_div_pos.mpr hd))
      _ = 1 / d := by ring
  rw [add_div]
  nlinarith

/-- pure-real: (A+Y)/(d·w) ≤ A/(d·u) + Y/(d·u) under w ≥ u -/
lemma real_bound_tail {d u w A Y : ℝ} (hd : 0 < d) (hu : 0 < u)
    (hA : 0 ≤ A) (hY : 0 ≤ Y) (hwu : u ≤ w) :
    (A + Y) / (d * w) ≤ A / (d * u) + Y / (d * u) := by
  have hduw : d * u ≤ d * w := mul_le_mul_of_nonneg_left hwu hd.le
  have hsum : (A + Y) / (d * w) ≤ (A + Y) / (d * u) := by
    exact div_le_div_of_nonneg_left (add_nonneg hA hY) (mul_pos hd hu) hduw
  rw [← add_div]
  exact hsum

/-- per-term upper bound used on the `n < M` part: A-part + 1/(n+1) -/
lemma dgTerm_le_head (x y : ℝ) (hx1 : (1 : ℝ) / 4 ≤ x) (n : ℕ) :
    dgTerm x y n ≤
      |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)) + 1 / ((n : ℝ) + 1) := by
  let w : ℝ := ‖(x : ℂ) + (y : ℂ) * Complex.I + (n : ℂ)‖
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hu : 0 < (n : ℝ) + x := by nlinarith
  have hw : 0 < w := by
    dsimp [w]
    exact lt_of_lt_of_le hu (norm_z_add_nat_ge x y n)
  have hwu : (n : ℝ) + x ≤ w := by simpa [w] using norm_z_add_nat_ge x y n
  have hwy : |y| ≤ w := by simpa [w] using norm_z_add_nat_ge_abs_y x y n
  calc
    dgTerm x y n = ‖((x : ℂ) + (y : ℂ) * Complex.I) - 1‖ / (((n : ℝ) + 1) * w) := by
      rw [dgTerm_eq_norm_div x y hx1 n]
    _ ≤ (|x - 1| + |y|) / (((n : ℝ) + 1) * w) := by
      exact div_le_div_of_nonneg_right (norm_z_sub_one_le x y) (by positivity)
    _ ≤ |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)) + 1 / ((n : ℝ) + 1) := by
      exact real_bound_head hd hu hw (abs_nonneg (x - 1)) hwu hwy
    _ = |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)) + 1 / ((n : ℝ) + 1) := rfl

/-- per-term upper bound used on the `n ≥ M` part: A-part + |y|-tail-part -/
lemma dgTerm_le_tail (x y : ℝ) (hx1 : (1 : ℝ) / 4 ≤ x) (n : ℕ) :
    dgTerm x y n ≤
      |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)) +
        |y| / (((n : ℝ) + 1) * ((n : ℝ) + x)) := by
  let w : ℝ := ‖(x : ℂ) + (y : ℂ) * Complex.I + (n : ℂ)‖
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hu : 0 < (n : ℝ) + x := by nlinarith
  have hw : 0 < w := by
    dsimp [w]
    exact lt_of_lt_of_le hu (norm_z_add_nat_ge x y n)
  have hwu : (n : ℝ) + x ≤ w := by simpa [w] using norm_z_add_nat_ge x y n
  calc
    dgTerm x y n = ‖((x : ℂ) + (y : ℂ) * Complex.I) - 1‖ / (((n : ℝ) + 1) * w) := by
      rw [dgTerm_eq_norm_div x y hx1 n]
    _ ≤ (|x - 1| + |y|) / (((n : ℝ) + 1) * w) := by
      exact div_le_div_of_nonneg_right (norm_z_sub_one_le x y) (by positivity)
    _ ≤ |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)) + |y| / (((n : ℝ) + 1) * ((n : ℝ) + x)) := by
      exact real_bound_tail hd hu (abs_nonneg (x - 1)) (abs_nonneg y) hwu
    _ = |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)) +
        |y| / (((n : ℝ) + 1) * ((n : ℝ) + x)) := rfl

/-- A-partial bound: Σ |x−1|/((n+1)(n+x)) ≤ 4 -/

lemma sum_inv_nat_succ_eq_harmonic (m : ℕ) :
    (∑ n ∈ Finset.range m, 1 / ((n : ℝ) + 1)) = (harmonic m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      norm_num

/-- monotonicity of range partial sums of a nonneg sequence -/


lemma range_sum_le_range_sum {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.range a, f n) ≤ ∑ n ∈ Finset.range b, f n := by
  have hb : b = a + (b - a) := by omega
  rw [hb, Finset.sum_range_add]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (by intro n hn; exact hf (a + n)))

/-- head: Σ_{n<M} 1/(n+1) ≤ 1 + log M -/


lemma head_harmonic_le_log (M : ℕ) :
    (∑ n ∈ Finset.range M, 1 / ((n : ℝ) + 1)) ≤ 1 + Real.log (M : ℝ) := by
  rw [sum_inv_nat_succ_eq_harmonic]
  exact harmonic_le_one_add_log M

/-- per-term tail bound: Y/((n+1)(n+x)) ≤ Y·(1/n − 1/(n+1)) -/


lemma tail_term_le (n : ℕ) (hn : 1 ≤ n) (x Y : ℝ) (hx : 0 ≤ x) (hY : 0 ≤ Y) :
    Y / (((n : ℝ) + 1) * ((n : ℝ) + x)) ≤ Y * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
  have hden2 : 0 < ((n : ℝ) * ((n : ℝ) + 1)) := by
    have h1 : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hle : Y / (((n : ℝ) + 1) * ((n : ℝ) + x)) ≤ Y / ((n : ℝ) * ((n : ℝ) + 1)) := by
    have hd : (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) * ((n : ℝ) + x) := by
      have : (n : ℝ) ≤ (n : ℝ) + x := by linarith
      calc (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + x) * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
        _ = ((n : ℝ) + 1) * ((n : ℝ) + x) := by ring
    exact div_le_div_of_nonneg_left hY hden2 hd
  have heq : Y / ((n : ℝ) * ((n : ℝ) + 1)) = Y * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
    field_simp [hden2.ne']
    ring
  calc
    Y / (((n : ℝ) + 1) * ((n : ℝ) + x)) ≤ Y / ((n : ℝ) * ((n : ℝ) + 1)) := hle
    _ = Y * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := heq

/-- tail bound lemma -/

lemma sum_range_inv_diff (a k : ℕ) :
    (∑ j ∈ Finset.range k, (1 / (((a + j : ℕ) : ℝ)) - 1 / (((a + j : ℕ) : ℝ) + 1))) =
      1 / (a : ℝ) - 1 / (((a + k : ℕ) : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hk1 : ((a + (k + 1) : ℕ) : ℝ) = ((a + k : ℕ) : ℝ) + 1 := by
        norm_num [Nat.cast_add]; ring
      -- 1/a − 1/(a+k) + (1/(a+k) − 1/(a+k+1)) = 1/a − 1/(a+k+1)
      rw [show ((a + (k + 1) : ℕ) : ℝ) = ((a + k : ℕ) : ℝ) + 1 by norm_num [Nat.cast_add]; ring]
      ring_nf


lemma sum_Ico_inv_sub_succ_le (M N : ℕ) (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Ico M N, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) ≤ 1 / (M : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  by_cases hk : N - M = 0
  · simp [hk]
  · have heq := sum_range_inv_diff M (N - M)
    calc
      (∑ j ∈ Finset.range (N - M),
          (1 / (((M + j : ℕ) : ℝ)) - 1 / (((M + j : ℕ) : ℝ) + 1)))
          = 1 / (M : ℝ) - 1 / ((M + (N - M) : ℕ) : ℝ) := by
            rw [heq]
      _ ≤ 1 / (M : ℝ) := by
        have hpos : 0 ≤ 1 / ((M + (N - M) : ℕ) : ℝ) := by positivity
        linarith

/-- per-term tail bound: Y/((n+1)(n+x)) ≤ Y·(1/n − 1/(n+1)) -/

lemma tail_Y_le (x Y : ℝ) (M N : ℕ) (hx1 : (1 : ℝ) / 4 ≤ x) (hY0 : 0 ≤ Y)
    (hM1 : 1 ≤ M) (hMY : (M : ℝ) ≥ Y + 1) :
    (∑ n ∈ Finset.Ico M N, Y / (((n : ℝ) + 1) * ((n : ℝ) + x))) ≤ 1 := by
  have hx0 : 0 ≤ x := by linarith
  have hpt : ∀ n ∈ Finset.Ico M N,
      Y / (((n : ℝ) + 1) * ((n : ℝ) + x)) ≤ Y * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
    intro n hn
    have hnM : M ≤ n := (Finset.mem_Ico.mp hn).1
    exact tail_term_le n (le_trans hM1 hnM) x Y hx0 hY0
  have hsum := Finset.sum_le_sum hpt
  calc
    (∑ n ∈ Finset.Ico M N, Y / (((n : ℝ) + 1) * ((n : ℝ) + x)))
        ≤ ∑ n ∈ Finset.Ico M N, Y * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := hsum
    _ = Y * (∑ n ∈ Finset.Ico M N, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
      rw [Finset.mul_sum]
    _ ≤ Y * (1 / (M : ℝ)) := mul_le_mul_of_nonneg_left (sum_Ico_inv_sub_succ_le M N hM1) hY0
    _ = Y / (M : ℝ) := by rw [mul_one_div]
    _ ≤ 1 := by
      have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM1
      have hYleM : Y ≤ (M : ℝ) := by linarith
      exact (div_le_one hMpos).2 hYleM


lemma harmonic_mono {a b : ℕ} (hab : a ≤ b) : (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  have hb : b = a + (b - a) := by omega
  have hsplit : (∑ n ∈ Finset.range (a + (b - a)), 1 / ((n : ℝ) + 1)) =
      (∑ n ∈ Finset.range a, 1 / ((n : ℝ) + 1)) +
        (∑ n ∈ Finset.range (b - a), 1 / (((a + n : ℕ) : ℝ) + 1)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_range_add (fun n : ℕ => 1 / ((n : ℝ) + 1)) a (b - a))
  have hS : 0 ≤ (∑ n ∈ Finset.range (b - a), 1 / (((a + n : ℕ) : ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  rw [hb]
  calc
    (harmonic a : ℝ) ≤ (harmonic a : ℝ) +
        (∑ n ∈ Finset.range (b - a), 1 / (((a + n : ℕ) : ℝ) + 1)) := le_add_of_nonneg_right hS
    _ = (∑ n ∈ Finset.range (a + (b - a)), 1 / ((n : ℝ) + 1)) := by
      rw [hsplit, sum_inv_nat_succ_eq_harmonic a]
    _ = (harmonic (a + (b - a)) : ℝ) := by
      rw [sum_inv_nat_succ_eq_harmonic (a + (b - a))]


lemma sum_inv_shift (c N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + ((c : ℝ) + 1))) =
      (harmonic (N + c) : ℝ) - (harmonic c : ℝ) := by
  have h := Finset.sum_range_add (fun n : ℕ => 1 / ((n : ℝ) + 1)) c N
  have hl : (∑ x ∈ Finset.range (c + N), 1 / ((x : ℝ) + 1)) = (harmonic (c + N) : ℝ) := by
    simpa [add_comm, add_left_comm, add_assoc] using (sum_inv_nat_succ_eq_harmonic (c + N))
  have hc : (∑ x ∈ Finset.range c, 1 / ((x : ℝ) + 1)) = (harmonic c : ℝ) :=
    sum_inv_nat_succ_eq_harmonic c
  have h' : (harmonic (c + N) : ℝ) =
      (harmonic c : ℝ) + (∑ x ∈ Finset.range N, 1 / (((c + x : ℕ) : ℝ) + 1)) := by
    rw [hl, hc] at h
    simpa [add_comm, add_left_comm, add_assoc] using h
  have h3 : (harmonic (N + c) : ℝ) - (harmonic c : ℝ) =
      (∑ x ∈ Finset.range N, 1 / (((c + x : ℕ) : ℝ) + 1)) := by
    rw [add_comm c N] at h'
    linarith
  calc
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + ((c : ℝ) + 1)))
        = ∑ n ∈ Finset.range N, 1 / (((c + n : ℕ) : ℝ) + 1) := by
          apply Finset.sum_congr rfl
          intro n hn
          congr 1
          norm_num [Nat.cast_add]
          ring
    _ = (harmonic (N + c) : ℝ) - (harmonic c : ℝ) := by
      rw [← h3]


lemma sumA_ge1_term (x : ℝ) (hx1 : (1 : ℝ) ≤ x) (hx2 : x ≤ 8) (n : ℕ) :
    (x - 1) / (((n : ℝ) + 1) * ((n : ℝ) + x)) ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 8) := by
  let B1 : ℝ := ((n : ℝ) + 1) * ((n : ℝ) + x)
  let B2 : ℝ := ((n : ℝ) + 1) * ((n : ℝ) + 8)
  have hpos1 : 0 < B1 := by
    dsimp [B1]
    have hxpos : 0 < (n : ℝ) + x := by nlinarith
    positivity
  have hpos2 : 0 < B2 := by
    dsimp [B2]; positivity
  have hcross : (x - 1) * B2 ≤ 7 * B1 := by
    have hfac : (x - 1) * B2 - 7 * B1 = ((n : ℝ) + 1)^2 * (x - 8) := by
      dsimp [B1, B2]
      ring
    have hsign : ((n : ℝ) + 1)^2 * (x - 8) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ((n : ℝ) + 1)) (sub_nonpos.mpr hx2)
    nlinarith
  have hstep : (x - 1) / B1 ≤ 7 / B2 := by
    rw [div_le_iff₀ hpos1]
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ hpos2]
    exact hcross
  calc
    (x - 1) / (((n : ℝ) + 1) * ((n : ℝ) + x)) = (x - 1) / B1 := rfl
    _ ≤ 7 / B2 := hstep
    _ = 7 / (((n : ℝ) + 1) * ((n : ℝ) + 8)) := rfl
    _ = 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 8) := by
      field_simp [hpos2.ne']
      ring


lemma sumA_ge1 (x : ℝ) (N : ℕ) (hx1 : (1 : ℝ) ≤ x) (hx2 : x ≤ 8) :
    (∑ n ∈ Finset.range N, (x - 1) / (((n : ℝ) + 1) * ((n : ℝ) + x))) ≤ 4 := by
  have hsumle : (∑ n ∈ Finset.range N, (x - 1) / (((n : ℝ) + 1) * ((n : ℝ) + x))) ≤
      ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 8)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact sumA_ge1_term x hx1 hx2 n
  calc
    (∑ n ∈ Finset.range N, (x - 1) / (((n : ℝ) + 1) * ((n : ℝ) + x)))
        ≤ ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 8)) := hsumle
    _ = (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) -
          (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 8)) := by
          rw [Finset.sum_sub_distrib]
    _ = (harmonic N : ℝ) - ((harmonic (N + 7) : ℝ) - (harmonic 7 : ℝ)) := by
          rw [sum_inv_nat_succ_eq_harmonic]
          congr 1
          have hs := sum_inv_shift 7 N
          rw [← hs]
          apply Finset.sum_congr rfl
          intro n hn
          congr 1
          ring
    _ ≤ 3 := by
          have hmono : (harmonic N : ℝ) ≤ (harmonic (N + 7) : ℝ) := harmonic_mono (by omega)
          have h7 : (harmonic 7 : ℝ) ≤ 3 := by norm_num [harmonic]
          nlinarith
    _ ≤ 4 := by norm_num

/-- 1/(n(n+1)) = 1/n − 1/(n+1) for n ≥ 1 -/

lemma one_div_mul_succ_eq (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) * ((n : ℝ) + 1)) = 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
  have hpos : (n : ℝ) ≠ 0 := by
    have : 0 < (n : ℝ) := by exact_mod_cast hn
    exact ne_of_gt this
  field_simp [hpos]
  ring

/-- telescoped Ico bound: Σ_{n ∈ Ico 1 N} (1/n − 1/(n+1)) ≤ 1 -/

lemma sum_Ico_inv_sub_succ_le_one (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) ≤ 1 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hid : ∀ k : ℕ, (∑ j ∈ Finset.range k,
      (1 / (((1 + j : ℕ) : ℝ)) - 1 / (((1 + j : ℕ) : ℝ) + 1))) = 1 - 1 / (((1 + k : ℕ) : ℝ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        rw [show ((1 + (k + 1) : ℕ) : ℝ) = ((1 + k : ℕ) : ℝ) + 1 by
          norm_num [Nat.cast_add]; ring]
        ring
  calc
    (∑ j ∈ Finset.range (N - 1), (1 / (((1 + j : ℕ) : ℝ)) - 1 / (((1 + j : ℕ) : ℝ) + 1)))
        = 1 - 1 / (((1 + (N - 1) : ℕ) : ℝ)) := hid (N - 1)
    _ ≤ 1 := by
      have hpos : 0 ≤ 1 / (((1 + (N - 1) : ℕ) : ℝ)) := by positivity
      linarith

/-- Σ_{n ∈ Ico 1 N} 1/(n(n+1)) ≤ 1 -/

lemma sum_Ico_one_div_mul_succ_le (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N, 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 1 := by
  calc
    (∑ n ∈ Finset.Ico 1 N, 1 / ((n : ℝ) * ((n : ℝ) + 1)))
        = ∑ n ∈ Finset.Ico 1 N, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
          apply Finset.sum_congr rfl
          intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
          exact one_div_mul_succ_eq n hn1
    _ ≤ 1 := sum_Ico_inv_sub_succ_le_one N

/-- per-term for x ≤ 1: |x−1|/B ≤ (3/4)/((n+1)(n+1/4)) -/

lemma sumA_le1_term (x : ℝ) (hx1 : (1 : ℝ) / 4 ≤ x) (hxlo : x ≤ 1) (n : ℕ) :
    |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)) ≤ (3 / 4) / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4))) := by
  have hA : |x - 1| = 1 - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hxlo)]
    ring
  have hden : ((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)) ≤ ((n : ℝ) + 1) * ((n : ℝ) + x) := by
    have hle : (n : ℝ) + (1 / 4) ≤ (n : ℝ) + x := by linarith
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hpos1 : 0 < ((n : ℝ) + 1) * ((n : ℝ) + x) := by
    have hxpos : 0 < (n : ℝ) + x := by nlinarith
    positivity
  have hpos2 : 0 < ((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)) := by positivity
  have hnum : 1 - x ≤ 3 / 4 := by nlinarith
  calc
    |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)) = (1 - x) / (((n : ℝ) + 1) * ((n : ℝ) + x)) := by
      rw [hA]
    _ ≤ (3 / 4) / (((n : ℝ) + 1) * ((n : ℝ) + x)) := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (3 / 4) / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4))) := by
      exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (3 / 4 : ℝ)) hpos2 hden

/-- Σ_{n<N} 1/((n+1)(n+1/4)) ≤ 5 -/

lemma sum_quarter_le_five (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)))) ≤ 5 := by
  by_cases hN : N = 0
  · simp [hN]
  · have hNpos : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN)
    -- range N = range 1 ∪ Ico 1 N
    have hunion : Finset.range 1 ∪ Finset.Ico 1 N = Finset.range N := by
      ext n
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range 1) (Finset.Ico 1 N) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_range, Finset.mem_Ico] at hn1 hn2
      omega
    have hterm : ∀ n ∈ Finset.Ico 1 N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4))) ≤
        1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
      have hpos1 : 0 < ((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)) := by positivity
      have hpos2 : 0 < ((n : ℝ) * ((n : ℝ) + 1)) := by
        have h : 0 < (n : ℝ) := by exact_mod_cast hn1
        positivity
      -- (n+1)(n+1/4) ≥ n(n+1)
      have hden : (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)) := by
        have hle : (n : ℝ) ≤ (n : ℝ) + 1 / 4 := by linarith
        calc (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + (1 / 4)) * ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
          _ = ((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)) := by ring
      exact div_le_div_of_nonneg_left zero_le_one hpos2 hden
    have htail := Finset.sum_le_sum hterm
    calc
      (∑ n ∈ Finset.range N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4))))
          = (∑ n ∈ Finset.range 1 ∪ Finset.Ico 1 N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)))) := by
            rw [← hunion]
      _ = (∑ n ∈ Finset.range 1, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)))) +
            (∑ n ∈ Finset.Ico 1 N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)))) := by
            rw [Finset.sum_union hdisj]
      _ ≤ 4 + 1 := by
        have h0 : (∑ n ∈ Finset.range 1, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)))) = 4 := by
          norm_num
        have ht : (∑ n ∈ Finset.Ico 1 N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)))) ≤ 1 := by
          calc
            (∑ n ∈ Finset.Ico 1 N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4))))
                ≤ ∑ n ∈ Finset.Ico 1 N, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := htail
            _ ≤ 1 := sum_Ico_one_div_mul_succ_le N
        nlinarith
      _ ≤ 5 := by norm_num

/-- bound for x ≤ 1 -/

lemma sumA_le1 (x : ℝ) (N : ℕ) (hx1 : (1 : ℝ) / 4 ≤ x) (hxlo : x ≤ 1) :
    (∑ n ∈ Finset.range N, |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x))) ≤ 4 := by
  have hsumle : (∑ n ∈ Finset.range N, |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x))) ≤
      ∑ n ∈ Finset.range N, (3 / 4) / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4))) := by
    apply Finset.sum_le_sum
    intro n hn
    exact sumA_le1_term x hx1 hxlo n
  calc
    (∑ n ∈ Finset.range N, |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)))
        ≤ ∑ n ∈ Finset.range N, (3 / 4) / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4))) := hsumle
    _ = (3 / 4) * (∑ n ∈ Finset.range N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + (1 / 4)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          field_simp
    _ ≤ (3 / 4) * 5 := mul_le_mul_of_nonneg_left (sum_quarter_le_five N) (by norm_num)
    _ ≤ 4 := by norm_num

/-- final A-sum bound -/

lemma sumA_le (x : ℝ) (N : ℕ) (hx1 : (1 : ℝ) / 4 ≤ x) (hx2 : x ≤ 8) :
    (∑ n ∈ Finset.range N, |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x))) ≤ 4 := by
  by_cases hge : (1 : ℝ) ≤ x
  · have hA : ∀ n, |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)) =
        (x - 1) / (((n : ℝ) + 1) * ((n : ℝ) + x)) := by
      intro n
      rw [abs_of_nonneg (sub_nonneg.mpr hge)]
    calc
      (∑ n ∈ Finset.range N, |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x)))
          = ∑ n ∈ Finset.range N, (x - 1) / (((n : ℝ) + 1) * ((n : ℝ) + x)) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hA n
      _ ≤ 4 := sumA_ge1 x N hge hx2
  · have hxlo : x ≤ 1 := by linarith
    exact sumA_le1 x N hx1 hxlo


/-- log M ≤ log(Y+2) when (M:ℝ) ≤ Y+2 -/
lemma log_M_le_log_Y_add_two (M : ℕ) (Y : ℝ) (hM1 : 1 ≤ M) (hMY : (M : ℝ) ≤ Y + 2) :
    Real.log (M : ℝ) ≤ Real.log (Y + 2) := by
  have hpos : 0 < (M : ℝ) := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    linarith
  exact Real.log_le_log hpos hMY

/-- split a range sum into the parts n<M and n≥M -/
lemma sum_range_split_lt_ge (f : ℕ → ℝ) (N M : ℕ) :
    (∑ n ∈ Finset.range N, f n) =
      (∑ n ∈ (Finset.range N).filter (fun n => n < M), f n) +
        (∑ n ∈ (Finset.range N).filter (fun n => M ≤ n), f n) := by
  have hunion : (Finset.range N).filter (fun n => n < M) ∪
      (Finset.range N).filter (fun n => M ≤ n) = Finset.range N := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    omega
  have hdisj : Disjoint ((Finset.range N).filter (fun n => n < M))
      ((Finset.range N).filter (fun n => M ≤ n)) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_filter, Finset.mem_range] at hn1 hn2
    omega
  conv_lhs => rw [← hunion]
  rw [Finset.sum_union hdisj]

lemma filter_lt_eq_range_min (N M : ℕ) :
    (Finset.range N).filter (fun n => n < M) = Finset.range (min N M) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma filter_ge_eq_Ico (N M : ℕ) :
    (Finset.range N).filter (fun n => M ≤ n) = Finset.Ico M N := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

lemma range_min_union_Ico (N M : ℕ) :
    Finset.range (min N M) ∪ Finset.Ico M N = Finset.range N := by
  ext n
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  omega

/-- partial sums of the series are bounded -/
lemma partial_sum_bound (x y : ℝ) (hx1 : (1 : ℝ) / 4 ≤ x) (hx2 : x ≤ 8) (N : ℕ) :
    (∑ n ∈ Finset.range N, dgTerm x y n) ≤ Real.log (2 + |y|) + 7 := by
  let Y : ℝ := |y|
  let M : ℕ := ⌈Y + 1⌉₊
  have hY0 : 0 ≤ Y := by dsimp [Y]; exact abs_nonneg y
  have hM1 : 1 ≤ M := by
    have h1 : (1 : ℝ) ≤ Y + 1 := by dsimp [Y]; have h := abs_nonneg y; linarith
    have hMYge : (Y + 1 : ℝ) ≤ (⌈Y + 1⌉₊ : ℝ) :=
      Nat.ceil_le.1 (le_rfl : (⌈Y + 1⌉₊ : ℕ) ≤ (⌈Y + 1⌉₊ : ℕ))
    exact_mod_cast (h1.trans hMYge)
  have hMY_ge : (M : ℝ) ≥ Y + 1 := by
    change (Y + 1 : ℝ) ≤ ((⌈Y + 1⌉₊ : ℕ) : ℝ)
    exact Nat.ceil_le.1 (le_rfl : (⌈Y + 1⌉₊ : ℕ) ≤ (⌈Y + 1⌉₊ : ℕ))
  have hMY_le : (M : ℝ) ≤ Y + 2 := by
    have hlt := Nat.ceil_lt_add_one (a := Y + 1) (by dsimp [Y]; linarith)
    change ((⌈Y + 1⌉₊ : ℕ) : ℝ) ≤ Y + 2
    linarith
  let Aterm : ℕ → ℝ := fun n => |x - 1| / (((n : ℝ) + 1) * ((n : ℝ) + x))
  let Hn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let Ytail : ℕ → ℝ := fun n => |y| / (((n : ℝ) + 1) * ((n : ℝ) + x))
  have hHn_nonneg : ∀ n, 0 ≤ Hn n := by intro n; dsimp [Hn]; positivity
  have hAcomb : (∑ n ∈ Finset.range (min N M), Aterm n) +
      (∑ n ∈ Finset.Ico M N, Aterm n) = ∑ n ∈ Finset.range N, Aterm n := by
    have hdisjA : Disjoint (Finset.range (min N M)) (Finset.Ico M N) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_range, Finset.mem_Ico] at hn1 hn2
      omega
    rw [← Finset.sum_union hdisjA]
    congr 1
    exact range_min_union_Ico N M
  calc
    (∑ n ∈ Finset.range N, dgTerm x y n)
        = (∑ n ∈ (Finset.range N).filter (fun n => n < M), dgTerm x y n) +
            (∑ n ∈ (Finset.range N).filter (fun n => M ≤ n), dgTerm x y n) := by
          rw [sum_range_split_lt_ge]
    _ ≤ (∑ n ∈ Finset.range (min N M), (Aterm n + Hn n)) +
          (∑ n ∈ Finset.Ico M N, (Aterm n + Ytail n)) := by
          have h1 : (∑ n ∈ (Finset.range N).filter (fun n => n < M), dgTerm x y n) ≤
              ∑ n ∈ Finset.range (min N M), (Aterm n + Hn n) := by
            rw [filter_lt_eq_range_min]
            apply Finset.sum_le_sum
            intro n hn
            exact dgTerm_le_head x y hx1 n
          have h2 : (∑ n ∈ (Finset.range N).filter (fun n => M ≤ n), dgTerm x y n) ≤
              ∑ n ∈ Finset.Ico M N, (Aterm n + Ytail n) := by
            rw [filter_ge_eq_Ico]
            apply Finset.sum_le_sum
            intro n hn
            exact dgTerm_le_tail x y hx1 n
          exact add_le_add h1 h2
    _ = (∑ n ∈ Finset.range (min N M), Aterm n) +
          (∑ n ∈ Finset.range (min N M), Hn n) +
          ((∑ n ∈ Finset.Ico M N, Aterm n) + (∑ n ∈ Finset.Ico M N, Ytail n)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ n ∈ Finset.range N, Aterm n) + (∑ n ∈ Finset.range (min N M), Hn n) +
          (∑ n ∈ Finset.Ico M N, Ytail n) := by
          rw [← hAcomb]
          ring
    _ ≤ (∑ n ∈ Finset.range N, Aterm n) + (∑ n ∈ Finset.range M, Hn n) +
          (∑ n ∈ Finset.Ico M N, Ytail n) := by
          have hmin : (∑ n ∈ Finset.range (min N M), Hn n) ≤ ∑ n ∈ Finset.range M, Hn n :=
            range_sum_le_range_sum hHn_nonneg (min_le_right N M)
          linarith
    _ ≤ 4 + (1 + Real.log (M : ℝ)) + 1 := by
          exact add_le_add
            (add_le_add (sumA_le x N hx1 hx2) (head_harmonic_le_log M))
            (tail_Y_le x (|y|) M N hx1 hY0 hM1 hMY_ge)
    _ ≤ Real.log (2 + |y|) + 7 := by
          have hlog : Real.log (M : ℝ) ≤ Real.log (Y + 2) := log_M_le_log_Y_add_two M Y hM1 hMY_le
          have hlog2 : Real.log (M : ℝ) ≤ Real.log (2 + Y) := by
            simpa [add_comm] using hlog
          have h : 4 + (1 + Real.log (M : ℝ)) + 1 ≤ Real.log (2 + Y) + 7 := by linarith
          simpa [Y] using h


/-- Bound for the absolute-value digamma series on the right half-strip:
`∑' n ‖1/(n+1) − 1/(x + n + iy)‖ ≤ log(2 + |y|) + 7` for `1/4 ≤ x ≤ 8`. -/
theorem digamma_series_norm_bound (x y : ℝ) (hx1 : (1 : ℝ) / 4 ≤ x) (hx2 : x ≤ 8) :
    (∑' n : ℕ, ‖((((n : ℂ) + 1)⁻¹) -
        ((((x : ℂ) + (y : ℂ) * Complex.I) + (n : ℂ))⁻¹))‖) ≤
      Real.log (2 + |y|) + 7 := by
  simpa [dgTerm] using
    (Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _)
      (fun N => partial_sum_bound x y hx1 hx2 N) :
        (∑' n : ℕ, dgTerm x y n) ≤ Real.log (2 + |y|) + 7)

end Commons.Analysis.SpecialFunctions.Gamma