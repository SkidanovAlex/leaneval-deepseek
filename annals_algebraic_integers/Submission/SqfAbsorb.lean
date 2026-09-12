import Mathlib
import Submission.SqfNumeric

/-!
# Elementary real inequalities for STAGE 2b of `core_squarefree`

Absorption of the product bound

    (B+n)^{n−M} · (2n)^{CR·√n} · (m+2)(2M+1) · a

into `n^{Cbig·√n}`, where `B = bSerre ≥ 0`, `a ≤ n^{Cb·√n}`,
`(n−M : ℝ) ≤ √n`, `m + 2 ≤ 2n`, `2M+1 ≤ 3n`, `n ≥ 2`.

All lemmas are pure real-number statements.  Namespace `Submission.SqfAbsorb`.
-/

noncomputable section
open scoped Real BigOperators

namespace Submission.SqfAbsorb

/-- `n ≥ 2` as reals. -/
lemma nat_two_le_cast {n : ℕ} (hn2 : 2 ≤ n) : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2

/-- `n ≥ 1` as reals. -/
lemma nat_one_le_cast {n : ℕ} (hn2 : 2 ≤ n) : (1 : ℝ) ≤ (n : ℝ) := by
  exact le_trans (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (nat_two_le_cast hn2)

/-- `n > 0` as reals. -/
lemma nat_pos_cast {n : ℕ} (hn2 : 2 ≤ n) : 0 < (n : ℝ) := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2 : ℝ)) (nat_two_le_cast hn2)

/-- `√n ≥ √2` for `n ≥ 2`. -/
lemma sqrt_ge_sqrt_two {n : ℕ} (hn2 : 2 ≤ n) : Real.sqrt 2 ≤ Real.sqrt (n : ℝ) := by
  exact Real.sqrt_le_sqrt (nat_two_le_cast hn2)

/-- `√2 > 0`. -/
lemma sqrt_two_pos : 0 < Real.sqrt 2 := by positivity

/-- `(5/√2)·√n ≥ 5` for `n ≥ 2`. -/
lemma five_over_sqrt2_mul_sqrt_ge_five {n : ℕ} (hn2 : 2 ≤ n) :
    (5 : ℝ) ≤ (5 / Real.sqrt 2) * Real.sqrt (n : ℝ) := by
  have h : (5 / Real.sqrt 2) * Real.sqrt 2 = 5 := by
    exact div_mul_cancel₀ (5 : ℝ) (ne_of_gt sqrt_two_pos)
  calc
    (5 : ℝ) = (5 / Real.sqrt 2) * Real.sqrt 2 := h.symm
    _ ≤ (5 / Real.sqrt 2) * Real.sqrt (n : ℝ) := by
      exact mul_le_mul_of_nonneg_left (sqrt_ge_sqrt_two hn2) (le_of_lt (by positivity))

/-- `6·n² ≤ n^5` for `n ≥ 2`. -/
lemma six_mul_sq_le_pow_five {n : ℕ} (hn2 : 2 ≤ n) :
    6 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 5 := by
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := nat_two_le_cast hn2
  have h3 : 8 ≤ (n : ℝ) ^ 3 := by
    calc
      (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn2R 3
  have hsq0 : 0 ≤ (n : ℝ) ^ 2 := by positivity
  calc
    6 * (n : ℝ) ^ 2 ≤ 8 * (n : ℝ) ^ 2 := by nlinarith [hsq0]
    _ = (n : ℝ) ^ 2 * 8 := by ring
    _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_left h3 hsq0
    _ = (n : ℝ) ^ 5 := by ring

/-- `6·n² ≤ n^{(5/√2)·√n}` for `n ≥ 2`. -/
lemma six_mul_sq_le_rpow {n : ℕ} (hn2 : 2 ≤ n) :
    6 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ ((5 / Real.sqrt 2) * Real.sqrt (n : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := nat_one_le_cast hn2
  have hn5 : (5 : ℝ) ≤ (5 / Real.sqrt 2) * Real.sqrt (n : ℝ) :=
    five_over_sqrt2_mul_sqrt_ge_five hn2
  calc
    6 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 5 := six_mul_sq_le_pow_five hn2
    _ = (n : ℝ) ^ ((5 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (n : ℝ) ^ ((5 / Real.sqrt 2) * Real.sqrt (n : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le hn1 hn5

/-- Quadratic bound on the two small factors: `(m+2)·(2M+1) ≤ 6n²` when
`m + 2 ≤ 2n` and `2M + 1 ≤ 3n`. -/
lemma quad_le_six_sq {n m M : ℕ} (hm : m + 2 ≤ 2 * n) (hM : 2 * M + 1 ≤ 3 * n) :
    ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) ≤ 6 * (n : ℝ) ^ 2 := by
  have hmR : ((m + 2 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hm
  have hMR : ((2 * M + 1 : ℕ) : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by exact_mod_cast hM
  have h1 : ((m + 2 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    calc
      ((m + 2 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := hmR
      _ = 2 * (n : ℝ) := by norm_num
  have h2 : ((2 * M + 1 : ℕ) : ℝ) ≤ 3 * (n : ℝ) := by
    calc
      ((2 * M + 1 : ℕ) : ℝ) ≤ ((3 * n : ℕ) : ℝ) := hMR
      _ = 3 * (n : ℝ) := by norm_num
  have hpos1 : 0 ≤ ((m + 2 : ℕ) : ℝ) := by positivity
  have hpos2 : 0 ≤ ((2 * M + 1 : ℕ) : ℝ) := by positivity
  calc
    ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) ≤ (2 * (n : ℝ)) * (3 * (n : ℝ)) := by
      exact mul_le_mul h1 h2 hpos2 (by positivity)
    _ = 6 * (n : ℝ) ^ 2 := by ring

/-- `(m+2)·(2M+1) ≤ n^{(5/√2)·√n}` for `n ≥ 2`, `m+2 ≤ 2n`, `2M+1 ≤ 3n`. -/
lemma quad_rpow_bound {n m M : ℕ} (hn2 : 2 ≤ n) (hm : m + 2 ≤ 2 * n)
    (hM : 2 * M + 1 ≤ 3 * n) :
    ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) ≤
      (n : ℝ) ^ ((5 / Real.sqrt 2) * Real.sqrt (n : ℝ)) := by
  exact le_trans (quad_le_six_sq hm hM) (six_mul_sq_le_rpow hn2)

/-- `(2n)^{CR·√n} ≤ n^{(2·CR)·√n}`, for `n ≥ 2`, `CR ≥ 0`. -/
lemma two_n_rpow_bound {n : ℕ} (hn2 : 2 ≤ n) {CR : ℝ} (hCR0 : 0 ≤ CR) :
    ((2 * n : ℕ) : ℝ) ^ (CR * Real.sqrt (n : ℝ)) ≤
      (n : ℝ) ^ ((2 * CR) * Real.sqrt (n : ℝ)) := by
  have hn0 : 0 ≤ (n : ℝ) := le_of_lt (nat_pos_cast hn2)
  have h2n_le : ((2 * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := nat_two_le_cast hn2
    have h20 : 0 ≤ (n : ℝ) := hn0
    have h2 : 2 * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
      exact mul_le_mul hn2R le_rfl h20 h20
    calc
      ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_num
      _ ≤ (n : ℝ) * (n : ℝ) := h2
      _ = (n : ℝ) ^ 2 := by ring
  have h2n0 : 0 ≤ ((2 * n : ℕ) : ℝ) := by positivity
  have hsq0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hexp0 : 0 ≤ CR * Real.sqrt (n : ℝ) := mul_nonneg hCR0 hsq0
  calc
    ((2 * n : ℕ) : ℝ) ^ (CR * Real.sqrt (n : ℝ)) ≤ ((n : ℝ) ^ 2) ^ (CR * Real.sqrt (n : ℝ)) := by
      exact Real.rpow_le_rpow h2n0 h2n_le hexp0
    _ = ((n : ℝ) ^ ((2 : ℕ) : ℝ)) ^ (CR * Real.sqrt (n : ℝ)) := by
      rw [Real.rpow_natCast]
    _ = (n : ℝ) ^ (((2 : ℕ) : ℝ) * (CR * Real.sqrt (n : ℝ))) := by
      exact (Real.rpow_mul hn0 ((2 : ℕ) : ℝ) (CR * Real.sqrt (n : ℝ))).symm
    _ = (n : ℝ) ^ ((2 * CR) * Real.sqrt (n : ℝ)) := by
      congr 1
      ring

/-- Base conversion: `B + n ≤ n^{1+ℓ}` with `ℓ = log(1+B)/log 2`, for `n ≥ 2`,
`B ≥ 0`. -/
lemma B_add_n_le_rpow {n : ℕ} (hn2 : 2 ≤ n) {B : ℝ} (hB0 : 0 ≤ B) :
    B + (n : ℝ) ≤ (n : ℝ) ^ (1 + Real.log (1 + B) / Real.log 2) := by
  have hn0 : 0 ≤ (n : ℝ) := le_of_lt (nat_pos_cast hn2)
  have hnpos : 0 < (n : ℝ) := nat_pos_cast hn2
  have h1B0 : 0 < 1 + B := by linarith
  have h1B1 : 1 ≤ 1 + B := by linarith
  have hlog2pos : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let ell : ℝ := Real.log (1 + B) / Real.log 2
  have hell0 : 0 ≤ ell := by
    dsimp [ell]
    exact div_nonneg (Real.log_nonneg h1B1) (le_of_lt hlog2pos)
  have hne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  have h2ell : (2 : ℝ) ^ ell = 1 + B := by
    dsimp [ell]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have harg : Real.log 2 * (Real.log (1 + B) / Real.log 2) = Real.log (1 + B) := by
      field_simp [hne]
    rw [harg]
    exact Real.exp_log h1B0
  have h2le_n : (2 : ℝ) ≤ (n : ℝ) := nat_two_le_cast hn2
  have hnB : 1 + B ≤ (n : ℝ) ^ ell := by
    calc
      1 + B = (2 : ℝ) ^ ell := by rw [h2ell]
      _ ≤ (n : ℝ) ^ ell := by
        exact Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) h2le_n hell0
  have hnn : (n : ℝ) * (1 + B) ≤ (n : ℝ) ^ (1 + ell) := by
    calc
      (n : ℝ) * (1 + B) ≤ (n : ℝ) * (n : ℝ) ^ ell := by
        exact mul_le_mul_of_nonneg_left hnB hn0
      _ = (n : ℝ) ^ (1 + ell) := by
        rw [Real.rpow_add hnpos (1 : ℝ) ell]
        simp
  have hle1 : B + (n : ℝ) ≤ (n : ℝ) * (1 + B) := by
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := nat_two_le_cast hn2
    have hdiff : B * ((n : ℝ) - 1) ≥ 0 := by
      exact mul_nonneg hB0 (by linarith)
    nlinarith
  exact le_trans hle1 (by simpa [ell] using hnn)

/-- `(B+n)^{n−M} ≤ n^{(1+ℓ)·√n}` when `(n−M : ℝ) ≤ √n`, `n ≥ 2`, `B ≥ 0`. -/
lemma B_add_n_pow_bound {n M : ℕ} (hn2 : 2 ≤ n) {B : ℝ} (hB0 : 0 ≤ B)
    (hsz : ((n - M : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ)) :
    (B + (n : ℝ)) ^ (n - M) ≤
      (n : ℝ) ^ ((1 + Real.log (1 + B) / Real.log 2) * Real.sqrt (n : ℝ)) := by
  have hn0 : 0 ≤ (n : ℝ) := le_of_lt (nat_pos_cast hn2)
  have hB0' : 0 ≤ B + (n : ℝ) := by linarith
  have hB1 : (1 : ℝ) ≤ B + (n : ℝ) := by
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := nat_two_le_cast hn2
    nlinarith
  have hbase := B_add_n_le_rpow hn2 (B := B) hB0
  have hsq0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  calc
    (B + (n : ℝ)) ^ (n - M) = (B + (n : ℝ)) ^ (((n - M : ℕ) : ℝ)) := by
      exact (Real.rpow_natCast (B + (n : ℝ)) (n - M)).symm
    _ ≤ (B + (n : ℝ)) ^ Real.sqrt (n : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hB1 hsz
    _ ≤ ((n : ℝ) ^ (1 + Real.log (1 + B) / Real.log 2)) ^ Real.sqrt (n : ℝ) := by
      exact Real.rpow_le_rpow hB0' hbase hsq0
    _ = (n : ℝ) ^ ((1 + Real.log (1 + B) / Real.log 2) * Real.sqrt (n : ℝ)) := by
      exact (Real.rpow_mul hn0 (1 + Real.log (1 + B) / Real.log 2) (Real.sqrt (n : ℝ))).symm

/-- Multiplying four inequalities `F_i ≤ x^{c_i}` with nonnegative `F_i` and
`x ≥ 1` gives `F1·F2·F3·F4 ≤ x^{c1+c2+c3+c4}`. -/
lemma four_bound_le_rpow {x : ℝ} (hx1 : 1 ≤ x) {c1 c2 c3 c4 : ℝ}
    {F1 F2 F3 F4 : ℝ} (hF1 : F1 ≤ x ^ c1) (hF2 : F2 ≤ x ^ c2)
    (hF3 : F3 ≤ x ^ c3) (hF4 : F4 ≤ x ^ c4) (hF10 : 0 ≤ F1) (hF20 : 0 ≤ F2)
    (hF30 : 0 ≤ F3) (hF40 : 0 ≤ F4) :
    F1 * F2 * F3 * F4 ≤ x ^ (c1 + c2 + c3 + c4) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hx0 : 0 ≤ x := le_of_lt hxpos
  have hxc (c : ℝ) : 0 ≤ x ^ c := Real.rpow_nonneg hx0 c
  have h12 : F1 * F2 ≤ x ^ c1 * x ^ c2 := by
    exact mul_le_mul hF1 hF2 hF20 (hxc c1)
  have h123 : (F1 * F2) * F3 ≤ (x ^ c1 * x ^ c2) * x ^ c3 := by
    exact mul_le_mul h12 hF3 hF30 (mul_nonneg (hxc c1) (hxc c2))
  calc
    (F1 * F2) * F3 * F4 ≤ (x ^ c1 * x ^ c2) * x ^ c3 * x ^ c4 := by
      exact mul_le_mul h123 hF4 hF40 (mul_nonneg (mul_nonneg (hxc c1) (hxc c2)) (hxc c3))
    _ = x ^ (c1 + c2 + c3 + c4) := by
      calc
        (x ^ c1 * x ^ c2) * x ^ c3 * x ^ c4 = x ^ (c1 + c2) * x ^ c3 * x ^ c4 := by
          rw [← Real.rpow_add hxpos c1 c2]
        _ = x ^ ((c1 + c2) + c3) * x ^ c4 := by
          rw [← Real.rpow_add hxpos (c1 + c2) c3]
        _ = x ^ (((c1 + c2) + c3) + c4) := by
          rw [← Real.rpow_add hxpos ((c1 + c2) + c3) c4]
        _ = x ^ (c1 + c2 + c3 + c4) := by
          rfl

/-- Comparing exponents multiplied by a common nonnegative factor: `x ≥ 1`,
`e ≥ 0`, `a ≤ b` give `x^{a·e} ≤ x^{b·e}`. -/
lemma rpow_le_rpow_of_exponent_coeff_le {x e a b : ℝ} (hx1 : 1 ≤ x) (he0 : 0 ≤ e)
    (hab : a ≤ b) : x ^ (a * e) ≤ x ^ (b * e) := by
  exact Real.rpow_le_rpow_of_exponent_le hx1 (mul_le_mul_of_nonneg_right hab he0)

end Submission.SqfAbsorb
