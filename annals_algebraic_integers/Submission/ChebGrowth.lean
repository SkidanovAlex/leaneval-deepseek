import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# One-sided polynomial growth off a bounded interval (Chebyshev-type)

GOAL (the `two-flank`/`Chebyshev-growth` engine behind the complex-root Remez
division lemma `lem:Remez` of Smith, prelim.tex):

    ∃ C > 0,  ∀ (d : ℕ), 1 ≤ d →
      ∀ (c : ℝ) (L : ℝ) (ρ : ℝ), 0 < L → 0 ≤ ρ → ρ ≤ 4·L/(d:ℝ)^2 →
        ∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
          (∀ y ∈ Set.Icc c (c + L), ‖Q.eval y‖ ≤ 1) →
            ‖Q.eval (c + L + ρ)‖ ≤ C · (d : ℝ) + 1
      ∧
      ∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
          (∀ y ∈ Set.Icc c (c + L), ‖Q.eval y‖ ≤ 1) →
            ‖Q.eval (c - ρ)‖ ≤ C · (d : ℝ) + 1

i.e. a degree-`d` complex polynomial bounded by `1` on an interval of length
`L` grows by at most a FIXED polynomial-in-`d` factor at a point within
distance `ρ ≤ 4L/d²` beyond either end.

Proof route:

1. Normalize to `[−1,1]`: for a complex polynomial `R` of degree ≤ d with
   `|R| ≤ 1` on `[−1,1]` we show a bound on `|R(x)|` for `1 ≤ x ≤ 1 + 8/d²`
   that is UNIFORM in `d`.

2. Split `R = A + iB` into real and imaginary real polynomials (`A = cRe R`,
   `B = cIm R`), both of degree ≤ d and bounded by 1 on `[−1,1]`.

3. Real Chebyshev growth (Mathlib `Chebyshev.Extremal`): for a real
   polynomial `P` with `|P| ≤ 1` on `[−1,1]`, `deg P ≤ d`, and real `x ≥ 1`,
   `|P(x)| ≤ T_d(x)`.

4. Bound `T_d(x) ≤ exp(17)` for `x ∈ [1, 1+8/d²]`, via
   `T_d(x) = cosh(d·arcosh x) ≤ exp(d·arcosh x)` and the elementary estimate
   `d·arcosh x ≤ d·(x−1+√(x²−1)) ≤ 17`.

5. Hence `‖R(x)‖ ≤ |A(x)| + |B(x)| ≤ 2·exp 17 =: C0`.

6. Rescale a general interval `[c, c+L]` to `[−1,1]` and a general target
   `c+L+ρ` to `x = 1+2ρ/L ≤ 1+8/d²`; the left end `c−ρ` follows by
   reflecting the polynomial (`y ↦ 2c+L−y`).
-/

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open Polynomial
open scoped Real BigOperators

namespace Submission.ChebGrowth

/-- For `1 ≤ d` and `x ≤ 1 + 8/d²`, `x ≤ 9`. -/
private lemma le_nine {d : ℕ} {x : ℝ} (hd : 1 ≤ d) (hx2 : x ≤ 1 + (8 : ℝ) / (d : ℝ) ^ 2) : x ≤ 9 := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have h8 : (8 : ℝ) / (d : ℝ) ^ 2 ≤ 8 := by
    rw [div_le_iff₀ (by positivity : 0 < (d:ℝ)^2)]
    have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith
    nlinarith
  linarith

/-- Real Chebyshev growth: for a real polynomial `P` with `|P| ≤ 1` on
`[−1,1]`, `degree P ≤ d`, and `x ≥ 1`: `|P(x)| ≤ T_d(x)`. -/
private lemma real_cheb_growth {d : ℕ} {P : Polynomial ℝ} {x : ℝ}
    (hdeg : P.degree ≤ d) (hbnd : ∀ y ∈ Set.Icc (-1) 1, |P.eval y| ≤ 1) (hx : 1 ≤ x) :
    |P.eval x| ≤ (Polynomial.Chebyshev.T ℝ d).eval x := by
  have hbnd' : ∀ y ∈ Set.Icc (-1) 1, |(-P).eval y| ≤ 1 := by
    intro y hy
    simpa using hbnd y hy
  have hdeg' : (-P).degree ≤ (d : WithBot ℕ) := by
    simpa using hdeg
  have h2 : -P.eval x ≤ (Polynomial.Chebyshev.T ℝ d).eval x := by
    have h := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (n := d) (P := -P) (k := 0) hx hdeg' hbnd'
    simpa using h
  have h1 : P.eval x ≤ (Polynomial.Chebyshev.T ℝ d).eval x := by
    have h := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (n := d) (P := P) (k := 0) hx hdeg hbnd
    simpa using h
  rw [abs_le]
  constructor
  · linarith
  · exact h1

/-- `cosh y ≤ exp y` for `y ≥ 0`. -/
private lemma cosh_le_exp_of_nonneg {y : ℝ} (hy : 0 ≤ y) : Real.cosh y ≤ Real.exp y := by
  rw [Real.cosh_eq]
  have hneg : Real.exp (-y) ≤ Real.exp y := (Real.exp_le_exp).2 (by linarith)
  have hp : 0 < Real.exp y := Real.exp_pos y
  nlinarith

/-- `arcosh x ≤ (x-1) + sqrt(x²-1)` for `x ≥ 1`. -/
private lemma arcosh_le {x : ℝ} (hx : 1 ≤ x) :
    Real.arcosh x ≤ (x - 1) + Real.sqrt (x ^ 2 - 1) := by
  unfold Real.arcosh
  have hpos : 0 < x + Real.sqrt (x ^ 2 - 1) := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-- For `d ≥ 1`, `1 ≤ x ≤ 1 + 8/d²`: `√(x²−1) ≤ √(10·(x−1))`. -/
private lemma sqrt_sq_sub_one_le {d : ℕ} {x : ℝ} (hd : 1 ≤ d) (hx1 : 1 ≤ x)
    (hx2 : x ≤ 1 + (8 : ℝ) / (d : ℝ) ^ 2) :
    Real.sqrt (x ^ 2 - 1) ≤ Real.sqrt (10 * (x - 1)) := by
  have hx9 : x ≤ 9 := le_nine hd hx2
  have hx1' : 0 ≤ x - 1 := by linarith
  have hxadd : x + 1 ≤ 10 := by linarith
  have hfac : x ^ 2 - 1 ≤ 10 * (x - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hxadd hx1']
  exact Real.sqrt_le_sqrt hfac

/-- For `d ≥ 1`, `1 ≤ x ≤ 1 + 8/d²`: `d·arcosh x ≤ 17`. -/
private lemma theta_d_bound {d : ℕ} {x : ℝ} (hd : 1 ≤ d) (hx1 : 1 ≤ x)
    (hx2 : x ≤ 1 + (8 : ℝ) / (d : ℝ) ^ 2) :
    (d : ℝ) * Real.arcosh x ≤ 17 := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hx1' : 0 ≤ x - 1 := by linarith
  have ht8 : x - 1 ≤ (8 : ℝ) / (d : ℝ) ^ 2 := by linarith
  have hx9 : x ≤ 9 := le_nine hd hx2
  have hdt : (d : ℝ) * (x - 1) ≤ 8 := by
    calc
      (d : ℝ) * (x - 1) ≤ (d : ℝ) * ((8 : ℝ) / (d : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left ht8 (by positivity)
      _ = (8 : ℝ) / (d : ℝ) := by field_simp [ne_of_gt hdpos]
      _ ≤ 8 := by
        rw [div_le_iff₀ hdpos]
        nlinarith
  have hnon : 0 ≤ x ^ 2 - 1 := by nlinarith
  have hdsq : (d : ℝ) * Real.sqrt (x ^ 2 - 1) ≤ Real.sqrt 80 := by
    rw [Real.le_sqrt (by positivity : 0 ≤ (d : ℝ) * Real.sqrt (x ^ 2 - 1))
      (by norm_num : (0 : ℝ) ≤ 80)]
    have hxadd : x + 1 ≤ 10 := by linarith
    have hfac : x ^ 2 - 1 ≤ 10 * (x - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hxadd (by linarith)]
    calc
      ((d : ℝ) * Real.sqrt (x ^ 2 - 1)) ^ 2
          = (d : ℝ) ^ 2 * (x ^ 2 - 1) := by rw [mul_pow, Real.sq_sqrt hnon]
      _ ≤ (d : ℝ) ^ 2 * (10 * (x - 1)) := mul_le_mul_of_nonneg_left hfac (sq_nonneg _)
      _ ≤ (d : ℝ) ^ 2 * (10 * ((8 : ℝ) / (d : ℝ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht8 (by norm_num)) (sq_nonneg _)
      _ = 80 := by field_simp [ne_of_gt hdpos] <;> norm_num
  have hsq80 : Real.sqrt 80 ≤ 9 := by
    have hle : Real.sqrt 80 ≤ Real.sqrt (9 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 9)] at hle
  have hθ := arcosh_le hx1
  calc
    (d : ℝ) * Real.arcosh x ≤ (d : ℝ) * ((x - 1) + Real.sqrt (x ^ 2 - 1)) := by
      exact mul_le_mul_of_nonneg_left hθ (by positivity)
    _ ≤ 8 + Real.sqrt 80 := by
      have h1 : (d : ℝ) * (x - 1) + (d : ℝ) * Real.sqrt (x ^ 2 - 1) ≤ 8 + Real.sqrt 80 := by
        linarith
      nlinarith
    _ ≤ 17 := by nlinarith

/-- For `d ≥ 1`, `1 ≤ x ≤ 1 + 8/d²`: `T_d(x) ≤ exp 17`. -/
private lemma T_eval_le_exp17 {d : ℕ} {x : ℝ} (hd : 1 ≤ d) (hx1 : 1 ≤ x)
    (hx2 : x ≤ 1 + (8 : ℝ) / (d : ℝ) ^ 2) :
    (Polynomial.Chebyshev.T ℝ d).eval x ≤ Real.exp 17 := by
  have hcosh : (Polynomial.Chebyshev.T ℝ d).eval x =
      Real.cosh ((d : ℝ) * Real.arcosh x) := by
    have hcast : ((d : ℤ) : ℝ) = (d : ℝ) := by norm_num
    have h1 := Polynomial.Chebyshev.T_real_cosh (Real.arcosh x) (d : ℤ)
    rw [Real.cosh_arcosh hx1] at h1
    rw [hcast] at h1
    rw [← h1]
  have hnon : 0 ≤ (d : ℝ) * Real.arcosh x :=
    mul_nonneg (by positivity : 0 ≤ (d : ℝ)) (Real.arcosh_nonneg hx1)
  calc
    (Polynomial.Chebyshev.T ℝ d).eval x ≤ Real.exp ((d : ℝ) * Real.arcosh x) := by
      rw [hcosh]
      exact cosh_le_exp_of_nonneg hnon
    _ ≤ Real.exp 17 := (Real.exp_le_exp).2 (theta_d_bound hd hx1 hx2)

/-- `‖z‖ ≤ |z.re| + |z.im|` for complex `z`. -/
private lemma norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  have h1 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← RCLike.normSq_eq_def']
    rw [RCLike.normSq_apply]
    congr 1 <;> simp
  have h2 : z.re * z.re + z.im * z.im ≤ (|z.re| + |z.im|) ^ 2 := by
    nlinarith [sq_abs (z.re), sq_abs (z.im), abs_nonneg (z.re), abs_nonneg (z.im)]
  have h3 : ‖z‖ ^ 2 ≤ (|z.re| + |z.im|) ^ 2 := by linarith
  exact (sq_le_sq₀ (norm_nonneg z) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp h3

/-- `(c * (x : ℂ)^k).re = c.re * x^k` for real `x`. -/
private lemma re_mul_pow_ofReal (c : ℂ) (x : ℝ) (k : ℕ) : (c * (x : ℂ) ^ k).re = c.re * x ^ k := by
  rw [← Complex.ofReal_pow]
  rw [Complex.re_mul_ofReal]

/-- `(c * (x : ℂ)^k).im = c.im * x^k` for real `x`. -/
private lemma im_mul_pow_ofReal (c : ℂ) (x : ℝ) (k : ℕ) : (c * (x : ℂ) ^ k).im = c.im * x ^ k := by
  rw [← Complex.ofReal_pow]
  rw [Complex.im_mul_ofReal]

/-- real part commutes with finite sums. -/
private lemma re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  exact map_sum Complex.reAddGroupHom f s

/-- imaginary part commutes with finite sums. -/
private lemma im_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) : (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  exact map_sum Complex.imAddGroupHom f s

/-- real-part polynomial of `p`: the real polynomial with coefficients
`(p.coeff k).re`.  Satisfies `(cRe p).eval x = (p.eval (x:ℂ)).re` for real `x`. -/
private noncomputable def cRe (p : Polynomial ℂ) : Polynomial ℝ :=
  p.sum (fun (k : ℕ) (a : ℂ) => C a.re * (X : ℝ[X]) ^ k)

/-- imaginary-part polynomial of `p`. -/
private noncomputable def cIm (p : Polynomial ℂ) : Polynomial ℝ :=
  p.sum (fun (k : ℕ) (a : ℂ) => C a.im * (X : ℝ[X]) ^ k)

private lemma cRe_eval (p : Polynomial ℂ) (x : ℝ) : (cRe p).eval x = (p.eval (x : ℂ)).re := by
  unfold cRe
  rw [Polynomial.sum_def]
  rw [Polynomial.eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [Polynomial.eval_eq_sum]
  rw [Polynomial.sum_def]
  rw [re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact (re_mul_pow_ofReal (p.coeff n) x n).symm

private lemma cIm_eval (p : Polynomial ℂ) (x : ℝ) : (cIm p).eval x = (p.eval (x : ℂ)).im := by
  unfold cIm
  rw [Polynomial.sum_def]
  rw [Polynomial.eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [Polynomial.eval_eq_sum]
  rw [Polynomial.sum_def]
  rw [im_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact (im_mul_pow_ofReal (p.coeff n) x n).symm

private lemma cRe_natDegree_le (p : Polynomial ℂ) : (cRe p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  unfold cRe
  rw [Polynomial.coeff_sum]
  rw [Polynomial.sum_def]
  apply Finset.sum_eq_zero
  intro n hn
  have hn' : p.coeff n ≠ 0 := (Polynomial.mem_support_iff).mp hn
  have hnle : n ≤ p.natDegree := by
    by_contra h
    have : p.natDegree < n := Nat.lt_of_not_ge h
    exact hn' (Polynomial.coeff_eq_zero_of_natDegree_lt this)
  have hnne : N ≠ n := by omega
  rw [coeff_C_mul_X_pow]
  simp [hnne]

private lemma cIm_natDegree_le (p : Polynomial ℂ) : (cIm p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  unfold cIm
  rw [Polynomial.coeff_sum]
  rw [Polynomial.sum_def]
  apply Finset.sum_eq_zero
  intro n hn
  have hn' : p.coeff n ≠ 0 := (Polynomial.mem_support_iff).mp hn
  have hnle : n ≤ p.natDegree := by
    by_contra h
    have : p.natDegree < n := Nat.lt_of_not_ge h
    exact hn' (Polynomial.coeff_eq_zero_of_natDegree_lt this)
  have hnne : N ≠ n := by omega
  rw [coeff_C_mul_X_pow]
  simp [hnne]

/-- from `‖p.eval y‖ ≤ 1` get `|(cRe p).eval y| ≤ 1`. -/
private lemma abs_eval_cRe_le_one {p : Polynomial ℂ} {y : ℝ}
    (h : ‖p.eval (y : ℂ)‖ ≤ 1) : |(cRe p).eval y| ≤ 1 := by
  rw [cRe_eval]
  exact le_trans (RCLike.abs_re_le_norm (p.eval (y : ℂ))) h

/-- from `‖p.eval y‖ ≤ 1` get `|(cIm p).eval y| ≤ 1`. -/
private lemma abs_eval_cIm_le_one {p : Polynomial ℂ} {y : ℝ}
    (h : ‖p.eval (y : ℂ)‖ ≤ 1) : |(cIm p).eval y| ≤ 1 := by
  rw [cIm_eval]
  exact le_trans (RCLike.abs_im_le_norm (p.eval (y : ℂ))) h

/-- `‖p.eval x‖ ≤ |(cRe p).eval x| + |(cIm p).eval x|`. -/
private lemma norm_eval_le_abs_cRe_add_abs_cIm (p : Polynomial ℂ) (x : ℝ) :
    ‖p.eval (x : ℂ)‖ ≤ |(cRe p).eval x| + |(cIm p).eval x| := by
  rw [cRe_eval, cIm_eval]
  exact norm_le_abs_re_add_abs_im (p.eval (x : ℂ))

/-- Normalized (unit-interval) growth: a degree-`d` complex polynomial bounded
by `1` on `[−1,1]` is bounded by the constant `2·exp 17` on
`[1, 1 + 8/d²]`.  (The constant is uniform in `d`.) -/
private lemma unit_complex_growth : ∃ C0 : ℝ, 0 < C0 ∧
    ∀ (d : ℕ), 1 ≤ d →
      ∀ (R : Polynomial ℂ), R.natDegree ≤ d →
        (∀ y : ℝ, y ∈ Set.Icc (-1) 1 → ‖R.eval (y : ℂ)‖ ≤ 1) →
          ∀ x : ℝ, 1 ≤ x → x ≤ 1 + (8 : ℝ) / (d : ℝ) ^ 2 →
            ‖R.eval (x : ℂ)‖ ≤ C0 := by
  let C0 : ℝ := 2 * Real.exp 17
  refine ⟨C0, mul_pos (by norm_num) (Real.exp_pos 17), ?_⟩
  intro d hd R hdeg hbnd x hx1 hx2
  let A : Polynomial ℝ := cRe R
  let B : Polynomial ℝ := cIm R
  have hAdeg : A.degree ≤ (d : WithBot ℕ) := by
    exact (Polynomial.natDegree_le_iff_degree_le).mp (le_trans (cRe_natDegree_le R) hdeg)
  have hBdeg : B.degree ≤ (d : WithBot ℕ) := by
    exact (Polynomial.natDegree_le_iff_degree_le).mp (le_trans (cIm_natDegree_le R) hdeg)
  have hAbnd : ∀ y ∈ Set.Icc (-1) 1, |A.eval y| ≤ 1 := fun y hy => abs_eval_cRe_le_one (hbnd y hy)
  have hBbnd : ∀ y ∈ Set.Icc (-1) 1, |B.eval y| ≤ 1 := fun y hy => abs_eval_cIm_le_one (hbnd y hy)
  have hAcheb : |A.eval x| ≤ (Polynomial.Chebyshev.T ℝ d).eval x := real_cheb_growth hAdeg hAbnd hx1
  have hBcheb : |B.eval x| ≤ (Polynomial.Chebyshev.T ℝ d).eval x := real_cheb_growth hBdeg hBbnd hx1
  have hT : (Polynomial.Chebyshev.T ℝ d).eval x ≤ Real.exp 17 := T_eval_le_exp17 hd hx1 hx2
  have hTnonneg : 0 ≤ (Polynomial.Chebyshev.T ℝ d).eval x := le_trans (abs_nonneg _) hAcheb
  have hnorm : ‖R.eval (x : ℂ)‖ ≤ |A.eval x| + |B.eval x| := norm_eval_le_abs_cRe_add_abs_cIm R x
  calc
    ‖R.eval (x : ℂ)‖ ≤ |A.eval x| + |B.eval x| := hnorm
    _ ≤ 2 * (Polynomial.Chebyshev.T ℝ d).eval x := by linarith
    _ ≤ 2 * Real.exp 17 := by
      exact mul_le_mul_of_nonneg_left hT (by norm_num)
    _ = C0 := rfl

/-- Right-end clause: bound `‖Q.eval (c+L+ρ)‖` by the uniform constant times
`d` plus one, via rescaling to the unit interval. -/
private lemma right_growth_const {C0 : ℝ} (hC0 : 0 < C0)
    (hunit : ∀ (d : ℕ), 1 ≤ d → ∀ (R : Polynomial ℂ), R.natDegree ≤ d →
      (∀ y : ℝ, y ∈ Set.Icc (-1) 1 → ‖R.eval (y : ℂ)‖ ≤ 1) →
        ∀ x : ℝ, 1 ≤ x → x ≤ 1 + (8 : ℝ) / (d : ℝ) ^ 2 → ‖R.eval (x : ℂ)‖ ≤ C0)
    {d : ℕ} (hd : 1 ≤ d) (c L ρ : ℝ) (hL : 0 < L) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ (4 : ℝ) * L / (d : ℝ) ^ 2)
    (Q : Polynomial ℂ) (hQdeg : Q.natDegree ≤ d)
    (hQbnd : ∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ 1) :
    ‖Q.eval ((c + L + ρ : ℝ) : ℂ)‖ ≤ C0 * (d : ℝ) + 1 := by
  let xR : ℝ := 1 + 2 * ρ / L
  let lin : Polynomial ℂ := C ((L / 2 : ℝ) : ℂ) * X + C ((c + L / 2 : ℝ) : ℂ)
  let R : Polynomial ℂ := Q.comp lin
  have hLne : L ≠ 0 := ne_of_gt hL
  have hx1 : 1 ≤ xR := by
    unfold xR
    have hρL : 0 ≤ 2 * ρ / L := div_nonneg (mul_nonneg (by norm_num) hρ0) (le_of_lt hL)
    linarith
  have hx2 : xR ≤ 1 + (8 : ℝ) / (d : ℝ) ^ 2 := by
    unfold xR
    have hd2pos : 0 < (d : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast (ne_of_gt hd))
    have hA : 2 * ρ / L ≤ (8 : ℝ) / (d : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity : 0 < L) hd2pos]
      calc
        2 * ρ * (d : ℝ) ^ 2 = (2 * (d : ℝ) ^ 2) * ρ := by ring
        _ ≤ (2 * (d : ℝ) ^ 2) * ((4 : ℝ) * L / (d : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hρ (by positivity)
        _ = 8 * L := by field_simp [ne_of_gt hd2pos] <;> ring
    linarith
  have hRdeg : R.natDegree ≤ d := by
    unfold R
    have hc : (Q.comp lin).natDegree ≤ Q.natDegree * lin.natDegree :=
      Polynomial.natDegree_comp_le
    have hl : lin.natDegree ≤ 1 := by
      unfold lin
      have h1 : (C ((L / 2 : ℝ) : ℂ) * (X : ℂ[X])).natDegree ≤ 1 := by
        exact (Polynomial.natDegree_C_mul_le ((L / 2 : ℝ) : ℂ) (X : ℂ[X])).trans (by simp)
      have h2 : (C ((c + L / 2 : ℝ) : ℂ)).natDegree ≤ 1 := by simp
      exact (Polynomial.natDegree_add_le _ _).trans (max_le h1 h2)
    have hq : Q.natDegree * lin.natDegree ≤ d := by
      exact (Nat.mul_le_mul hQdeg hl).trans (by simp)
    exact le_trans hc hq
  have hlin_eval : ∀ t : ℝ, lin.eval (t : ℂ) = ((c + L * (t + 1) / 2 : ℝ) : ℂ) := by
    intro t
    unfold lin
    simp <;> ring_nf
  have hRbnd : ∀ y : ℝ, y ∈ Set.Icc (-1) 1 → ‖R.eval (y : ℂ)‖ ≤ 1 := by
    intro y hy
    have hy1 : -1 ≤ y := hy.1
    have hy2 : y ≤ 1 := hy.2
    have hz : c + L * (y + 1) / 2 ∈ Set.Icc c (c + L) := by
      constructor
      · have h0 : 0 ≤ L * (y + 1) / 2 :=
          div_nonneg (mul_nonneg (le_of_lt hL) (by linarith)) (by norm_num)
        nlinarith
      · have h1 : L * (y + 1) / 2 ≤ L := by
          have hd : (y + 1) / 2 ≤ 1 := by linarith
          calc
            L * (y + 1) / 2 = L * ((y + 1) / 2) := by ring
            _ ≤ L * 1 := mul_le_mul_of_nonneg_left hd (le_of_lt hL)
            _ = L := by ring
        nlinarith
    have hev : R.eval (y : ℂ) = Q.eval ((c + L * (y + 1) / 2 : ℝ) : ℂ) := by
      unfold R
      rw [eval_comp, hlin_eval y]
    rw [hev]
    exact hQbnd (c + L * (y + 1) / 2) hz
  have hunitR := hunit d hd R hRdeg hRbnd xR hx1 hx2
  have harg : c + L * (xR + 1) / 2 = c + L + ρ := by
    unfold xR
    field_simp [hLne] <;> ring
  have hval : R.eval (xR : ℂ) = Q.eval ((c + L + ρ : ℝ) : ℂ) := by
    unfold R
    rw [eval_comp, hlin_eval xR]
    rw [harg]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  calc
    ‖Q.eval ((c + L + ρ : ℝ) : ℂ)‖ ≤ C0 := by
      rw [← hval]
      exact hunitR
    _ ≤ C0 * (d : ℝ) + 1 := by nlinarith

/-- One-sided Chebyshev-type growth: a degree-`d` complex polynomial bounded
by `1` on an interval of length `L` stays bounded by `C·d + 1` at a point
within distance `ρ ≤ 4L/d²` beyond either end of the interval. -/
theorem cheb_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ (c : ℝ) (L : ℝ) (ρ : ℝ),
      0 < L → 0 ≤ ρ → ρ ≤ (4 : ℝ) * L / (d : ℝ) ^ 2 →
      (∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
        (∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ 1) →
          ‖Q.eval ((c + L + ρ) : ℂ)‖ ≤ C * (d : ℝ) + 1) ∧
      (∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
        (∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ 1) →
          ‖Q.eval ((c - ρ) : ℂ)‖ ≤ C * (d : ℝ) + 1) := by
  obtain ⟨C0, hC0, hunit⟩ := unit_complex_growth
  refine ⟨C0, hC0, ?_⟩
  intro d hd c L ρ hL hρ0 hρ
  constructor
  · intro Q hQdeg hQbnd
    have hb := right_growth_const hC0 hunit hd c L ρ hL hρ0 hρ Q hQdeg hQbnd
    have hEq : Q.eval ((c : ℂ) + (L : ℂ) + (ρ : ℂ)) = Q.eval ((c + L + ρ : ℝ) : ℂ) := by
      congr 1
      simp
    rw [hEq]
    exact hb
  · intro Q hQdeg hQbnd
    let Qr : Polynomial ℂ := Q.comp (C ((2 * c + L : ℝ) : ℂ) - X)
    have hQrdeg : Qr.natDegree ≤ d := by
      unfold Qr
      have hc : (Q.comp (C ((2 * c + L : ℝ) : ℂ) - X)).natDegree ≤
          Q.natDegree * (C ((2 * c + L : ℝ) : ℂ) - X).natDegree :=
        Polynomial.natDegree_comp_le
      have hl : (C ((2 * c + L : ℝ) : ℂ) - (X : ℂ[X])).natDegree ≤ 1 := by
        have h1 : (C ((2 * c + L : ℝ) : ℂ)).natDegree ≤ 1 := by
          rw [Polynomial.natDegree_C]
          norm_num
        have h2 : (-(X : ℂ[X])).natDegree ≤ 1 := by simp
        exact (Polynomial.natDegree_add_le (C ((2 * c + L : ℝ) : ℂ)) (-(X : ℂ[X]))).trans (max_le h1 h2)
      have hq : Q.natDegree * (C ((2 * c + L : ℝ) : ℂ) - (X : ℂ[X])).natDegree ≤ d := by
        exact (Nat.mul_le_mul hQdeg hl).trans (by simp)
      exact le_trans hc hq
    have hQrbnd : ∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Qr.eval (y : ℂ)‖ ≤ 1 := by
      intro y hy
      have hy1 : c ≤ y := hy.1
      have hy2 : y ≤ c + L := hy.2
      have hz : 2 * c + L - y ∈ Set.Icc c (c + L) := by
        constructor <;> nlinarith
      have hev : Qr.eval (y : ℂ) = Q.eval ((2 * c + L - y : ℝ) : ℂ) := by
        unfold Qr
        rw [eval_comp]
        congr 1
        simp <;> ring_nf
      rw [hev]
      exact hQbnd (2 * c + L - y) hz
    have hb := right_growth_const hC0 hunit hd c L ρ hL hρ0 hρ Qr hQrdeg hQrbnd
    -- hb : ‖Qr.eval (c+L+ρ)‖ ≤ C0·d+1, convert to Q(c-ρ)
    have hval : Qr.eval ((c + L + ρ : ℝ) : ℂ) = Q.eval ((c - ρ : ℝ) : ℂ) := by
      unfold Qr
      rw [eval_comp]
      congr 1
      simp <;> ring_nf
    rw [hval] at hb
    have hEq : Q.eval ((c : ℂ) - (ρ : ℂ)) = Q.eval ((c - ρ : ℝ) : ℂ) := by
      congr 1
      simp
    rw [hEq]
    exact hb
