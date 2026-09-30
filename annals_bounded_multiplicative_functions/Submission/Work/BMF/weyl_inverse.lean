import Mathlib
import Submission.Work.BMF.Defs
import Submission.Commons.Analysis.ExponentialSums.iterated_differencing_step
import Submission.Work.BMF.SD.fiber_card_ge
import Submission.Work.BMF.SD.taylor_sub_coeff
import Submission.Work.BMF.SD.descent_coeff
import Submission.Work.BMF.SD.a_one_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # N2 `weyl_inverse`: inverse Weyl inequality  (Tao, HOF analysis, Lemma 1.1.16) -/

open Polynomial Finset Real Complex
open scoped ComplexConjugate

namespace Work.BMF

set_option maxHeartbeats 0

/-! ## 1. The additive character `eC t = exp (2 π i t)` -/

lemma eC_eq_exp (x : ℝ) : eC x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
  unfold eC
  congr 1
  push_cast
  ring

lemma eC_re (x : ℝ) : (eC x).re = Real.cos (2 * Real.pi * x) := by
  rw [eC_eq_exp, Complex.exp_ofReal_mul_I_re]

lemma eC_im (x : ℝ) : (eC x).im = Real.sin (2 * Real.pi * x) := by
  rw [eC_eq_exp, Complex.exp_ofReal_mul_I_im]

lemma eC_norm (x : ℝ) : ‖eC x‖ = 1 := by
  have h2 : ‖eC x‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, eC_re, eC_im]
    nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * x)]
  have hnn : 0 ≤ ‖eC x‖ := norm_nonneg _
  nlinarith [h2, hnn]

lemma eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [Complex.ofReal_add]
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ((x : ℂ) + (y : ℂ))
      = 2 * ↑Real.pi * Complex.I * (x : ℂ) + 2 * ↑Real.pi * Complex.I * (y : ℂ) from by ring]
  exact Complex.exp_add _ _

lemma eC_zero : eC 0 = 1 := by simp [eC]

lemma eC_neg (x : ℝ) : eC (-x) = (eC x)⁻¹ := by
  have h : eC (-x) * eC x = 1 := by rw [← eC_add, neg_add_cancel, eC_zero]
  exact eq_inv_of_mul_eq_one_left h

lemma eC_intCast (m : ℤ) : eC (m : ℝ) = 1 := by
  rw [eC_eq_exp]
  have h : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I
      = (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

lemma eC_natCast (n : ℕ) : eC (n : ℝ) = 1 := by
  rw [show ((n : ℕ) : ℝ) = ((n : ℤ) : ℝ) by push_cast; ring, eC_intCast]

private lemma star_eC (x : ℝ) : star (eC x) = eC (-x) := by
  rw [eC_neg, Complex.star_def]
  have hns : Complex.normSq (eC x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, eC_norm]; norm_num
  apply Complex.ext
  · rw [Complex.conj_re, Complex.inv_re, eC_re, hns]
    ring
  · rw [Complex.conj_im, Complex.inv_im, eC_im, hns]
    ring

private lemma norm_ofReal_eq_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h2 : ‖((r : ℝ) : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    rw [sq_abs]
    ring
  have hnn : 0 ≤ ‖((r : ℝ) : ℂ)‖ := norm_nonneg _
  nlinarith [h2, hnn, abs_nonneg r]

lemma norm_eC_sub_one_le (t : ℝ) : ‖eC t - 1‖ ≤ 4 * Real.pi * |t| := by
  rw [eC_eq_exp]
  by_cases h : 2 * Real.pi * |t| ≤ 1
  · have hx : ‖((2 * Real.pi * t : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_ofReal_eq_abs]
      rw [show |2 * Real.pi * t| = 2 * Real.pi * |t| by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
          abs_of_pos Real.pi_pos]]
      exact h
    have hle := Complex.norm_exp_sub_one_le hx
    calc ‖Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ 2 * ‖((2 * Real.pi * t : ℝ) : ℂ) * Complex.I‖ := hle
      _ = 2 * (2 * Real.pi * |t|) := by
          rw [norm_mul, Complex.norm_I, mul_one, norm_ofReal_eq_abs]
          rw [show |2 * Real.pi * t| = 2 * Real.pi * |t| by
            rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
              abs_of_pos Real.pi_pos]]
      _ = 4 * Real.pi * |t| := by ring
  · push Not at h
    have h1 : ‖eC t‖ = 1 := eC_norm t
    have heq : ‖Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) - 1‖ = ‖eC t - 1‖ := by
      rw [eC_eq_exp]
    rw [heq]
    have h2 : ‖eC t - 1‖ ≤ 2 := by
      calc ‖eC t - 1‖ ≤ ‖eC t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [h1]; norm_num
    have h3 : (2 : ℝ) ≤ 4 * Real.pi * |t| := by nlinarith [Real.pi_pos]
    linarith

/-- Lower bound: `4 |t - round t| ≤ ‖eC t - 1‖`. -/
lemma le_norm_eC_sub_one (t : ℝ) : 4 * |t - (round t : ℝ)| ≤ ‖eC t - 1‖ := by
  set u : ℝ := t - (round t : ℝ) with hu
  have hut : t = u + (round t : ℝ) := by rw [hu]; ring
  have hc : eC t - 1 = eC u - 1 := by rw [hut, eC_add, eC_intCast, mul_one]
  rw [hc]
  have hu1 : |u| ≤ 1 / 2 := by rw [hu]; exact abs_sub_round t
  have hsq : ‖eC u - 1‖ ^ 2 = 4 * Real.sin (Real.pi * u) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, eC_re, eC_im,
      Complex.one_re, Complex.one_im]
    have hcos : Real.cos (2 * Real.pi * u) = 1 - 2 * Real.sin (Real.pi * u) ^ 2 := by
      have h := Real.cos_two_mul' (Real.pi * u)
      rw [show 2 * (Real.pi * u) = 2 * Real.pi * u by ring] at h
      rw [h]; nlinarith [Real.cos_sq_add_sin_sq (Real.pi * u)]
    have hsin : Real.sin (2 * Real.pi * u)
        = 2 * Real.sin (Real.pi * u) * Real.cos (Real.pi * u) := by
      have h := Real.sin_two_mul (Real.pi * u)
      rw [show 2 * (Real.pi * u) = 2 * Real.pi * u by ring] at h
      exact h
    rw [hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * u)]
  have hsin2 : 4 * u ^ 2 ≤ Real.sin (Real.pi * u) ^ 2 := by
    have h1 : Real.pi * |u| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hu1]
    have h2 : 0 ≤ Real.pi * |u| := by positivity
    have h3 := Real.mul_le_sin h2 h1
    rw [show 2 / Real.pi * (Real.pi * |u|) = 2 * |u| by field_simp] at h3
    have h4 : Real.sin (Real.pi * |u|) ^ 2 = Real.sin (Real.pi * u) ^ 2 := by
      rcases le_or_gt 0 u with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h]
        rw [show Real.pi * -u = -(Real.pi * u) by ring, Real.sin_neg]
        ring
    have h5 : (2 * |u|) ^ 2 ≤ Real.sin (Real.pi * |u|) ^ 2 := by
      have hsnn : 0 ≤ Real.sin (Real.pi * |u|) :=
        Real.sin_nonneg_of_mem_Icc (by constructor <;> nlinarith [Real.pi_pos, hu1])
      nlinarith [h3, hsnn, abs_nonneg u]
    rw [h4, mul_pow] at h5
    nlinarith [h5, sq_abs u]
  have hA : (4 * |u|) ^ 2 ≤ ‖eC u - 1‖ ^ 2 := by
    rw [mul_pow, sq_abs, hsq]
    nlinarith [hsin2]
  nlinarith [hA, norm_nonneg (eC u - 1), abs_nonneg u]

/-! ## 2. The phase polynomial `PE` -/

/-- `PE k a n = ∑_{j ≤ k} a j * n^j`. -/
noncomputable def PE (k : ℕ) (a : ℕ → ℝ) (n : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), a j * n ^ j

lemma PE_succ_eq (k : ℕ) (c : ℕ → ℝ) (hc : c (k + 1) = 0) (x : ℝ) :
    PE (k + 1) c x = PE k c x := by
  unfold PE
  rw [Finset.sum_range_succ, hc, zero_mul, add_zero]

/-- Binomial expansion of `PE` along a shift: `PE k a (y+t)` as a polynomial in `t`. -/
lemma PE_shift (k : ℕ) (a : ℕ → ℝ) (y t : ℝ) :
    PE k a (y + t)
      = PE k (fun i => ∑ j ∈ Finset.Icc i k, a j * ((j.choose i : ℝ) * y ^ (j - i))) t := by
  unfold PE
  have hterm : ∀ j, a j * (y + t) ^ j
      = ∑ i ∈ Finset.range (j + 1), a j * (y ^ (j - i) * t ^ i * (j.choose i : ℝ)) := by
    intro j
    rw [add_comm y t, add_pow, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  trans ∑ j ∈ Finset.range (k + 1),
      ∑ i ∈ Finset.range (j + 1), a j * (y ^ (j - i) * t ^ i * (j.choose i : ℝ))
  · apply Finset.sum_congr rfl; intro j _; exact hterm j
  have hstep : ∀ j ≤ k, ∑ i ∈ Finset.range (j + 1),
        a j * (y ^ (j - i) * t ^ i * (j.choose i : ℝ))
      = ∑ i ∈ Finset.range (k + 1),
          (if i ≤ j then a j * (y ^ (j - i) * t ^ i * (j.choose i : ℝ)) else 0) := by
    intro j hj
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [Finset.sum_congr rfl (fun j hj => hstep j (by have := Finset.mem_range.mp hj; omega))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  have hset : (Finset.range (k + 1)).filter (fun j => i ≤ j) = Finset.Icc i k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [← Finset.sum_filter, hset]
  show (∑ j ∈ Finset.Icc i k, a j * (y ^ (j - i) * t ^ i * (j.choose i : ℝ)))
      = (∑ j ∈ Finset.Icc i k, a j * ((j.choose i : ℝ) * y ^ (j - i))) * t ^ i
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Rescaling `PE` in the variable. -/
lemma PE_rescale (k : ℕ) (c : ℕ → ℝ) (Q m : ℝ) :
    PE k c (Q * m) = PE k (fun i => c i * Q ^ i) m := by
  unfold PE
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow]; ring

/-- The finite difference of `PE` along `h`, expanded in the variable `x`. -/
lemma PE_diff (k : ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    PE k a (x + h) - PE k a x
      = PE k (fun i => ∑ j ∈ Finset.Icc (i + 1) k, a j * ((j.choose i : ℝ) * h ^ (j - i))) x := by
  have hshift := PE_shift k a h x
  have h1 : PE k a (x + h)
      = PE k (fun i => ∑ j ∈ Finset.Icc i k, a j * ((j.choose i : ℝ) * h ^ (j - i))) x := by
    rw [add_comm]; exact hshift
  have h2 : PE k (fun i => ∑ j ∈ Finset.Icc i k, a j * ((j.choose i : ℝ) * h ^ (j - i))) x - PE k a x
      = PE k (fun i =>
          (∑ j ∈ Finset.Icc i k, a j * ((j.choose i : ℝ) * h ^ (j - i))) - a i) x := by
    unfold PE
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  have hkey : (∑ j ∈ Finset.Icc i k, a j * ((j.choose i : ℝ) * h ^ (j - i))) - a i
      = ∑ j ∈ Finset.Icc (i + 1) k, a j * ((j.choose i : ℝ) * h ^ (j - i)) := by
    have hIcc : Finset.Icc i k = insert i (Finset.Icc (i + 1) k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hni : i ∉ Finset.Icc (i + 1) k := by simp only [Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_insert hni]
    have hone : a i * ((i.choose i : ℝ) * h ^ (i - i)) = a i := by
      rw [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one, mul_one]
    rw [hone]; ring
  show ((∑ j ∈ Finset.Icc i k, a j * ((j.choose i : ℝ) * h ^ (j - i))) - a i) * x ^ i
      = (∑ j ∈ Finset.Icc (i + 1) k, a j * ((j.choose i : ℝ) * h ^ (j - i))) * x ^ i
  rw [hkey]

lemma norm_sum_eC_le (k : ℕ) (a : ℕ → ℝ) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, eC (PE k a n)‖ ≤ L := by
  calc ‖∑ n ∈ Finset.range L, eC (PE k a n)‖
      ≤ ∑ n ∈ Finset.range L, ‖eC (PE k a n)‖ := norm_sum_le _ _
    _ = ∑ _n ∈ Finset.range L, (1 : ℝ) := by
        apply Finset.sum_congr rfl; intro n _
        simp only [eC_norm]
    _ = L := by simp

/-! ## 3. The linear case -/

lemma linear_exp_sum_approx (θ : ℝ) (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ)
    (h : δ * N ≤ ‖∑ n ∈ Finset.range N, eC (θ * n)‖) :
    ∃ m : ℤ, |θ - m| ≤ 2 / (δ * N) := by
  set z : ℂ := eC θ with hz
  set S : ℂ := ∑ n ∈ Finset.range N, eC (θ * n) with hS
  have hpow : ∀ n : ℕ, eC (θ * n) = z ^ n := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero, eC_zero, pow_zero]
    | succ m ih =>
        rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring]
        rw [show θ * ((m : ℝ) + 1) = θ * m + θ by ring, eC_add, ih, ← hz, pow_succ]
  have hSN : S = ∑ n ∈ Finset.range N, z ^ n := by
    rw [hS]; exact Finset.sum_congr rfl (fun n _ => hpow n)
  have hmul : (z - 1) * S = z ^ N - 1 := by
    rw [hSN, Finset.mul_sum]
    have : ∀ n ∈ Finset.range N, (z - 1) * z ^ n = z ^ (n + 1) - z ^ n := by
      intro n _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_range_sub, pow_zero]
  have hbound : ‖S‖ * ‖z - 1‖ ≤ 2 := by
    have h2 : ‖(z - 1) * S‖ ≤ 2 := by
      rw [hmul]
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz, eC_norm]; norm_num
    rw [norm_mul, mul_comm] at h2
    exact h2
  have hz1 : δ * N * ‖z - 1‖ ≤ 2 := by
    have h1 : δ * N * ‖z - 1‖ ≤ ‖S‖ * ‖z - 1‖ :=
      mul_le_mul_of_nonneg_right h (norm_nonneg _)
    linarith
  have hge : 4 * |θ - (round θ : ℝ)| ≤ ‖z - 1‖ := by
    have h := le_norm_eC_sub_one θ
    rwa [← hz] at h
  refine ⟨round θ, ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < δ * N := mul_pos hδ hNpos
  have h1 : 4 * |θ - (round θ : ℝ)| * (δ * N) ≤ 2 := by nlinarith [hge, hz1, hpos]
  have h2 : |θ - (round θ : ℝ)| * (δ * N) ≤ (1 : ℝ) / 2 := by linarith
  have hgoal : |θ - (round θ : ℝ)| ≤ 2 * (δ * N)⁻¹ := by
    have hc : δ * N * (δ * N)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    nlinarith [h2, hc, hpos]
  rwa [div_eq_mul_inv]


/-! ## 4. The inverse Weyl inequality

Route (Weyl differencing, then a coefficient descent at the top, then a residue-class
argument for the linear coefficient).  The route is realised as an induction on the degree:

* `diff_shift_exists` (van der Corput / Weyl differencing): a large phase sum produces a
  bounded-below-density set `D` of shifts `d` for which the differenced phase
  `P(·+d) - P` still has a large exponential sum;
* the induction hypothesis applied to `P(·+d) - P` (a polynomial of degree `≤ k`) gives a
  denominator `qd ≤ Ck`, and pigeonholing over `[1, Ck]` (`fiber_card_ge`) produces a common
  `q` working on a positive proportion `δ₄ L` of the shifts;
* `descent_coeff` converts the resulting conditions on the shifted coefficients
  `Σ_j C(j,i) d^{j-i} a_j` (`i ≤ k`) into bounds for `a_j`, `2 ≤ j ≤ k+1`;
* `a_one_bound` pins the linear coefficient `a 1` by a residue-class / Abel argument.

The four arithmetic lemmas `fiber_card_ge`, `taylor_sub_coeff`, `descent_coeff`, `a_one_bound`
are proved by colleagues in `Submission/Work/BMF/SD/` and are imported here; the differencing
step, the induction and the assembly are below. -/

/-- `WeylInvP k`: the inverse Weyl inequality for polynomials of degree `≤ k`. -/
def WeylInvP (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ), 1 ≤ L → ∀ (P : Polynomial ℝ),
    P.natDegree ≤ k →
    δ * (L : ℝ) ≤ ‖∑ n ∈ Finset.range L, eC (P.eval (n : ℝ))‖ →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C ∧
      ∀ j ∈ Finset.Icc 1 k, ∃ m : ℤ, |(q : ℝ) * P.coeff j - m| ≤ C / (L : ℝ) ^ j

lemma norm_sum_eC_le' (M : ℕ) (g : ℕ → ℝ) :
    ‖∑ x ∈ Finset.range M, eC (g x)‖ ≤ (M : ℝ) := by
  calc ‖∑ x ∈ Finset.range M, eC (g x)‖ ≤ ∑ x ∈ Finset.range M, ‖eC (g x)‖ := norm_sum_le _ _
    _ = ∑ _x ∈ Finset.range M, (1 : ℝ) := by
        apply Finset.sum_congr rfl; intro x _; rw [eC_norm]
    _ = (M : ℝ) := by simp

lemma eC_mul_star (A B : ℝ) : eC A * star (eC B) = eC (A - B) := by
  rw [star_eC, ← eC_add, sub_eq_add_neg]

lemma eval_eq_sum_range_of_natDegree_le (P : Polynomial ℝ) (K : ℕ) (hP : P.natDegree ≤ K)
    (x : ℝ) : P.eval x = ∑ j ∈ Finset.range (K + 1), P.coeff j * x ^ j :=
  Polynomial.eval_eq_sum_range' (by omega) x

lemma taylor_sub_eval (P : Polynomial ℝ) (d n : ℕ) :
    (Polynomial.taylor (d : ℝ) P - P).eval (n : ℝ) = P.eval ((n + d : ℕ) : ℝ) - P.eval (n : ℝ) := by
  rw [Polynomial.eval_sub, Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  congr 2
  push_cast
  ring

theorem weylInvP_zero : WeylInvP 0 := by
  intro δ hδ
  refine ⟨1, one_pos, ?_⟩
  intro L hL P hP hbig
  refine ⟨1, le_refl 1, by norm_num, ?_⟩
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact absurd hj.2 (by omega)

theorem weylInvP_one : WeylInvP 1 := by
  intro δ hδ
  refine ⟨max (2 / δ) 1 + 1, by positivity, ?_⟩
  intro L hL P hP hbig
  have hPeval : ∀ x : ℝ, P.eval x = P.coeff 0 + P.coeff 1 * x := by
    intro x
    rw [eval_eq_sum_range_of_natDegree_le P 1 hP x, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  have hsum_eq : (∑ n ∈ Finset.range L, eC (P.eval (n : ℝ)))
      = eC (P.coeff 0) * ∑ n ∈ Finset.range L, eC (P.coeff 1 * (n : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [hPeval n, eC_add]
  have hbc : δ * (L : ℝ) ≤ ‖∑ n ∈ Finset.range L, eC (P.coeff 1 * (n : ℝ))‖ := by
    have h := hbig
    rw [hsum_eq, norm_mul, eC_norm, one_mul] at h
    exact h
  obtain ⟨m, hm⟩ := linear_exp_sum_approx (P.coeff 1) L hL δ hδ hbc
  refine ⟨1, le_refl 1, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max (2 / δ) 1 := le_max_right _ _
    linarith
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hj1 : j = 1 := by omega
  subst hj1
  refine ⟨m, ?_⟩
  rw [Nat.cast_one, one_mul, pow_one]
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hCδ : (2 : ℝ) ≤ (max (2 / δ) 1 + 1) * δ := by
    have h2 : (2 : ℝ) / δ ≤ max (2 / δ) 1 := le_max_left _ _
    have h3 : (2 / δ) * δ = 2 := by field_simp
    have h4 : (2 / δ) * δ ≤ (max (2 / δ) 1 + 1) * δ := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hδ)
      linarith
    linarith [h3, h4]
  refine le_trans hm ?_
  rw [div_le_iff₀ (mul_pos hδ hLpos)]
  have hstep : ((max (2 / δ) 1 + 1) / (L : ℝ)) * (δ * (L : ℝ))
      = (max (2 / δ) 1 + 1) * δ := by
    field_simp
  rw [hstep]
  exact hCδ

lemma diff_shift_exists (δ : ℝ) (hδ : 0 < δ) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 2 ∧ ∀ (L : ℕ) (f : ℕ → ℝ),
      (16 : ℝ) / δ ^ 2 ≤ (L : ℝ) →
      δ * (L : ℝ) ≤ ‖∑ n ∈ Finset.range L, eC (f n)‖ →
      ∃ D : Finset ℕ, D ⊆ Finset.Icc 1 (L - 1) ∧ δ₁ * (L : ℝ) ≤ (D.card : ℝ) ∧
        ∀ d ∈ D, δ₁ * (L : ℝ) ≤ ((L - d : ℕ) : ℝ) ∧
          δ₁ * ((L - d : ℕ) : ℝ) ≤
            ‖∑ x ∈ Finset.range (L - d), eC (f (x + d) - f x)‖ := by
  refine ⟨min (δ ^ 2 / 8) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro L f hL hbig
  classical
  have hδ₁le : min (δ ^ 2 / 8) (1 / 2) ≤ δ ^ 2 / 8 := min_le_left _ _
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : (0 : ℝ) < 16 / δ ^ 2 := by positivity
    linarith
  have hL1 : 1 ≤ L := by
    by_contra h; push Not at h; interval_cases L; simp at hLpos
  set G : ℕ → ℂ := fun h => ∑ x ∈ Finset.range (L - h), eC (f (x + h) - f x) with hG
  set τ : ℝ := δ ^ 2 / 8 * (L : ℝ) with hτ
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have key : δ ^ 2 * (L : ℝ) ^ 2 ≤ 2 * ∑ h ∈ Finset.range L, ‖G h‖ := by
    have h1 := Commons.Analysis.ExponentialSums.iterated_differencing_step L (fun n => eC (f n))
    have h2 : ∀ h : ℕ, ‖∑ x ∈ Finset.range (L - h), eC (f (x + h)) * star (eC (f x))‖ = ‖G h‖ := by
      intro h; congr 1
      apply Finset.sum_congr rfl; intro x _; rw [eC_mul_star]
    have h4 : (δ * (L : ℝ)) ^ 2 ≤ ‖∑ n ∈ Finset.range L, eC (f n)‖ ^ 2 := by
      apply sq_le_sq'
      · nlinarith [norm_nonneg (∑ n ∈ Finset.range L, eC (f n))]
      · exact hbig
    calc δ ^ 2 * (L : ℝ) ^ 2 = (δ * (L : ℝ)) ^ 2 := by ring
      _ ≤ ‖∑ n ∈ Finset.range L, eC (f n)‖ ^ 2 := h4
      _ ≤ 2 * ∑ h ∈ Finset.range L,
            ‖∑ x ∈ Finset.range (L - h), eC (f (x + h)) * star (eC (f x))‖ := h1
      _ = 2 * ∑ h ∈ Finset.range L, ‖G h‖ := by
          congr 1; exact Finset.sum_congr rfl (fun h _ => h2 h)
  have hnorm_le : ∀ h : ℕ, ‖G h‖ ≤ ((L - h : ℕ) : ℝ) := fun h =>
    norm_sum_eC_le' (L - h) (fun x => f (x + h) - f x)
  have hG0 : ‖G 0‖ = (L : ℝ) := by
    have : G 0 = (L : ℂ) := by
      simp only [hG, Nat.sub_zero, Nat.add_zero]
      rw [show (∑ x ∈ Finset.range L, eC (f x - f x)) = ∑ _x ∈ Finset.range L, (1 : ℂ) from
        Finset.sum_congr rfl (fun x _ => by rw [sub_self]; simp)]
      simp
    rw [this]; simp
  have hsplit : ∑ h ∈ Finset.range L, ‖G h‖
      = ‖G 0‖ + ∑ h ∈ (Finset.range L).filter (fun h => 1 ≤ h), ‖G h‖ := by
    have hnot : (Finset.range L).filter (fun h => ¬ (1 ≤ h)) = {0} := by
      ext h; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    have hs := Finset.sum_filter_add_sum_filter_not (Finset.range L) (fun h => 1 ≤ h)
      (fun h => ‖G h‖)
    rw [hnot] at hs
    simp only [Finset.sum_singleton] at hs
    linarith
  have htail : δ ^ 2 * (L : ℝ) ^ 2 / 4 ≤
      ∑ h ∈ (Finset.range L).filter (fun h => 1 ≤ h), ‖G h‖ := by
    have hLge : (L : ℝ) ≤ δ ^ 2 * (L : ℝ) ^ 2 / 4 := by
      have h16 : (16 : ℝ) ≤ δ ^ 2 * (L : ℝ) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)] at hL; linarith
      nlinarith [hLpos, h16]
    have := key; rw [hsplit, hG0] at this; linarith
  refine ⟨((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖), ?_, ?_, ?_⟩
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hh ⊢; omega
  · by_contra hlt
    push Not at hlt
    have hbound : ∑ h ∈ (Finset.range L).filter (fun h => 1 ≤ h), ‖G h‖
        ≤ ((((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖)).card : ℝ)
            * (L : ℝ) + (L : ℝ) * τ := by
      rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range L).filter (fun h => 1 ≤ h))
              (fun h => τ ≤ ‖G h‖) (fun h => ‖G h‖)]
      apply add_le_add
      · calc _ ≤ ∑ _h ∈ ((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖),
                (L : ℝ) := Finset.sum_le_sum (fun h hh =>
                  le_trans (hnorm_le h) (by exact_mod_cast Nat.sub_le L h))
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      · calc _ ≤ ∑ _h ∈ ((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => ¬ τ ≤ ‖G h‖), τ :=
              Finset.sum_le_sum (fun h hh => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hh).2))
          _ = ((((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => ¬ τ ≤ ‖G h‖)).card : ℝ) * τ := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (((Finset.range L).filter (fun h => 1 ≤ h)).card : ℝ) * τ := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hτpos)
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ (L : ℝ) * τ := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hτpos)
              have h2 := Finset.card_le_card (Finset.filter_subset (fun h => 1 ≤ h) (Finset.range L))
              simp only [Finset.card_range] at h2
              exact_mod_cast h2
    have h1 : δ ^ 2 * (L : ℝ) ^ 2 / 4 ≤
        ((((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖)).card : ℝ)
          * (L : ℝ) + (L : ℝ) * τ := le_trans htail hbound
    have h2 : ((((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖)).card : ℝ)
          * (L : ℝ) + (L : ℝ) * τ < δ ^ 2 * (L : ℝ) ^ 2 / 4 := by
      rw [hτ] at hlt ⊢; nlinarith [hlt, hLpos]
    linarith
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨⟨hdL, hd1⟩, hdτ⟩ := hd
    have hnorm : ‖G d‖ ≤ ((L - d : ℕ) : ℝ) := hnorm_le d
    have hτd : τ ≤ ((L - d : ℕ) : ℝ) := le_trans hdτ hnorm
    refine ⟨?_, ?_⟩
    · have h1 : min (δ ^ 2 / 8) (1 / 2) * (L : ℝ) ≤ δ ^ 2 / 8 * (L : ℝ) :=
        mul_le_mul_of_nonneg_right hδ₁le (le_of_lt hLpos)
      rw [hτ] at hτd; linarith
    · calc min (δ ^ 2 / 8) (1 / 2) * ((L - d : ℕ) : ℝ)
          ≤ δ ^ 2 / 8 * ((L - d : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hδ₁le (by positivity)
        _ ≤ δ ^ 2 / 8 * (L : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le L d) (by positivity)
        _ = τ := by rw [hτ]
        _ ≤ ‖G d‖ := hdτ
        _ = ‖∑ x ∈ Finset.range (L - d), eC (f (x + d) - f x)‖ := rfl

theorem weylInvP_succ (k : ℕ) (hk : 1 ≤ k) (H : WeylInvP k) : WeylInvP (k + 1) := by
  intro δ hδ
  obtain ⟨δ₁, hδ₁pos, hδ₁half, hshift⟩ := diff_shift_exists δ hδ
  obtain ⟨Ck, hCkpos, hCk⟩ := H δ₁ hδ₁pos
  set B : ℕ := ⌈Ck⌉₊ + 1 with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; omega
  have hBCk : (Ck : ℝ) ≤ (B : ℝ) := by
    have h1 : (Ck : ℝ) ≤ (⌈Ck⌉₊ : ℝ) := Nat.le_ceil Ck
    have h2 : ((⌈Ck⌉₊ : ℕ) : ℝ) ≤ (B : ℝ) := by rw [hBdef]; push_cast; linarith
    linarith
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
  set δ₄ : ℝ := δ₁ / (2 * (B : ℝ)) with hδ₄def
  have hδ₄pos : 0 < δ₄ := by rw [hδ₄def]; positivity
  have hδ₄half : δ₄ ≤ 1 / 2 := by
    have hB1' : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
    rw [hδ₄def, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (B : ℝ))]
    nlinarith [hδ₁half, hB1']
  obtain ⟨C₁, hC₁pos, hdesc⟩ := Work.BMF.SD.descent_coeff k Ck (B : ℝ) δ₁ δ₄ hCkpos
    (by exact_mod_cast hB1) hδ₁pos hδ₄pos hδ₄half
  obtain ⟨C₂, hC₂pos, ha1⟩ :=
    Work.BMF.SD.a_one_bound (k + 1) (by omega) δ hδ (max C₁ 1) (le_max_right _ _)
  set L₀ : ℝ := max (16 / δ ^ 2) (max (1 / δ₁) (max (100 * Ck / (δ₄ ^ 2 * δ₁))
    (max 2 (max C₁ 1)))) with hL₀def
  have hL₀2 : (2 : ℝ) ≤ L₀ := by
    rw [hL₀def]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hL₀1 : (1 : ℝ) ≤ L₀ := le_trans (by norm_num) hL₀2
  have hL₀16 : (16 : ℝ) / δ ^ 2 ≤ L₀ := by rw [hL₀def]; exact le_max_left _ _
  have hL₀1δ : (1 : ℝ) / δ₁ ≤ L₀ := by
    rw [hL₀def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hL₀100 : 100 * Ck / (δ₄ ^ 2 * δ₁) ≤ L₀ := by
    rw [hL₀def]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hL₀C₁ : C₁ ≤ L₀ := by
    rw [hL₀def]
    exact le_trans (le_max_left C₁ 1) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hL₀max : max C₁ 1 ≤ L₀ := by
    rw [hL₀def]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  set C : ℝ := max (max C₁ (C₂ * (C₁ + 1) + 1) + 1) (L₀ ^ (k + 1) / 2 + 1) with hCdef
  have hCC₁ : C₁ ≤ C := by
    rw [hCdef]
    have h1 : C₁ ≤ max C₁ (C₂ * (C₁ + 1) + 1) := le_max_left _ _
    have h2 : max C₁ (C₂ * (C₁ + 1) + 1) ≤ max C₁ (C₂ * (C₁ + 1) + 1) + 1 := by linarith
    have h3 : max C₁ (C₂ * (C₁ + 1) + 1) + 1 ≤
        max (max C₁ (C₂ * (C₁ + 1) + 1) + 1) (L₀ ^ (k + 1) / 2 + 1) := le_max_left _ _
    linarith
  have hCC₂ : C₂ * (C₁ + 1) ≤ C := by
    rw [hCdef]
    have h1 : C₂ * (C₁ + 1) ≤ max C₁ (C₂ * (C₁ + 1) + 1) := by
      have h := le_max_right C₁ (C₂ * (C₁ + 1) + 1); linarith
    have h2 : max C₁ (C₂ * (C₁ + 1) + 1) ≤ max C₁ (C₂ * (C₁ + 1) + 1) + 1 := by linarith
    have h3 : max C₁ (C₂ * (C₁ + 1) + 1) + 1 ≤
        max (max C₁ (C₂ * (C₁ + 1) + 1) + 1) (L₀ ^ (k + 1) / 2 + 1) := le_max_left _ _
    linarith
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCdef]
    refine le_trans ?_ (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ max C₁ (C₂ * (C₁ + 1) + 1) :=
      le_trans (le_of_lt hC₁pos) (le_max_left _ _)
    linarith
  have hCL₀ : L₀ ^ (k + 1) / 2 + 1 ≤ C := by rw [hCdef]; exact le_max_right _ _
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC1, ?_⟩
  intro L hL1 P hPnat hbig
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  by_cases hcase : L₀ < (L : ℝ)
  · have hL16 : (16 : ℝ) / δ ^ 2 ≤ (L : ℝ) := le_trans hL₀16 (le_of_lt hcase)
    have hL2 : 2 ≤ L := by
      have h : (2 : ℝ) ≤ (L : ℝ) := le_trans hL₀2 (le_of_lt hcase)
      exact_mod_cast h
    have hLδ₁ : 1 ≤ δ₁ * (L : ℝ) := by
      have h1 : 1 / δ₁ ≤ (L : ℝ) := le_trans hL₀1δ (le_of_lt hcase)
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hδ₁pos)
      rw [mul_one_div, div_self (ne_of_gt hδ₁pos)] at h2
      exact h2
    have hCkL : Ck ≤ δ₄ ^ 2 * (δ₁ * (L : ℝ)) / 100 := by
      have h1 : 100 * Ck / (δ₄ ^ 2 * δ₁) ≤ (L : ℝ) := le_trans hL₀100 (le_of_lt hcase)
      have h2 : 0 < δ₄ ^ 2 * δ₁ := by positivity
      rw [div_le_iff₀ h2] at h1
      have h3 : Ck * 100 ≤ δ₄ ^ 2 * δ₁ * (L : ℝ) := by linarith
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100)]
      linarith
    have hC₁L : C₁ ≤ (L : ℝ) := le_trans hL₀C₁ (le_of_lt hcase)
    obtain ⟨D, hDsub, hDcard, hDprop⟩ := hshift L (fun n => P.eval (n : ℝ)) hL16 hbig
    have hex : ∀ d : ℕ, d ∈ D → ∃ qd : ℕ, 1 ≤ qd ∧ (qd : ℝ) ≤ Ck ∧ (∀ i ∈ Finset.Icc 1 k,
        ∃ m : ℤ, |(qd : ℝ) * (∑ j ∈ Finset.Icc (i + 1) (k + 1),
            P.coeff j * (d : ℝ) ^ (j - i) * ((j.choose i : ℕ) : ℝ)) - m|
          ≤ Ck / (((L - d : ℕ)) : ℝ) ^ i) := by
      intro d hd
      obtain ⟨hdd1, hdLd⟩ := hDprop d hd
      have hdd : d < L := by
        have h := hDsub hd; rw [Finset.mem_Icc] at h; omega
      have hLd1 : 1 ≤ L - d := by omega
      have hdeg : (Polynomial.taylor (d : ℝ) P - P).natDegree ≤ k :=
        (Work.BMF.SD.taylor_sub_coeff k d P hPnat).1
      have hNN : δ₁ * ((L - d : ℕ) : ℝ) ≤
          ‖∑ x ∈ Finset.range (L - d), eC (P.eval ((x + d : ℕ) : ℝ) - P.eval (x : ℝ))‖ := hdLd
      have hsum : δ₁ * ((L - d : ℕ) : ℝ) ≤
          ‖∑ n ∈ Finset.range (L - d), eC ((Polynomial.taylor (d : ℝ) P - P).eval (n : ℝ))‖ := by
        rw [show (∑ n ∈ Finset.range (L - d),
              eC ((Polynomial.taylor (d : ℝ) P - P).eval (n : ℝ)))
            = ∑ n ∈ Finset.range (L - d),
              eC (P.eval ((n + d : ℕ) : ℝ) - P.eval (n : ℝ)) from
          Finset.sum_congr rfl (fun n _ => by rw [taylor_sub_eval])]
        exact hNN
      obtain ⟨qd, hqd1, hqd2, hqd3⟩ := hCk (L - d) hLd1 (Polynomial.taylor (d : ℝ) P - P) hdeg hsum
      refine ⟨qd, hqd1, hqd2, ?_⟩
      intro i hi
      obtain ⟨m, hm⟩ := hqd3 i hi
      exact ⟨m, by rwa [(Work.BMF.SD.taylor_sub_coeff k d P hPnat).2 i] at hm⟩
    classical
    let qd : ℕ → ℕ := fun d => if h : d ∈ D then Classical.choose (hex d h) else 1
    have hqd_spec : ∀ d (hd : d ∈ D), 1 ≤ qd d ∧ (qd d : ℝ) ≤ Ck ∧ (∀ i ∈ Finset.Icc 1 k,
        ∃ m : ℤ, |(qd d : ℝ) * (∑ j ∈ Finset.Icc (i + 1) (k + 1),
            P.coeff j * (d : ℝ) ^ (j - i) * ((j.choose i : ℕ) : ℝ)) - m|
          ≤ Ck / (((L - d : ℕ)) : ℝ) ^ i) := by
      intro d hd
      have hh := Classical.choose_spec (hex d hd)
      simpa only [qd, dif_pos hd] using hh
    have hqd_lo : ∀ d ∈ D, 1 ≤ qd d := fun d hd => (hqd_spec d hd).1
    have hqd_hi : ∀ d ∈ D, qd d ≤ B := by
      intro d hd
      have h := (hqd_spec d hd).2.1
      exact_mod_cast (le_trans h hBCk)
    obtain ⟨q, hq1, hqB, hqcard⟩ := Work.BMF.SD.fiber_card_ge D B qd hB1 hqd_lo hqd_hi
    set D' : Finset ℕ := D.filter (fun d => qd d = q) with hD'def
    have hD'card : δ₄ * (L : ℝ) ≤ (D'.card : ℝ) := by
      have hb : δ₄ * (L : ℝ) ≤ (D.card : ℝ) / (B : ℝ) := by
        rw [hδ₄def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hBpos]
        nlinarith [hBpos, hδ₁pos, hDcard]
      linarith [hb, hqcard]
    have hD'sub : ∀ d ∈ D', 1 ≤ d ∧ δ₁ * (L : ℝ) ≤ ((L - d : ℕ) : ℝ) := by
      intro d hd
      have hdD : d ∈ D := (Finset.mem_filter.mp hd).1
      obtain ⟨h1, h2⟩ := hDprop d hdD
      exact ⟨(Finset.mem_Icc.mp (hDsub hdD)).1, h1⟩
    have hD'cond : ∀ d ∈ D', ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ,
        |(q : ℝ) * (∑ j ∈ Finset.Icc (i + 1) (k + 1),
            P.coeff j * (d : ℝ) ^ (j - i) * ((j.choose i : ℕ) : ℝ)) - m|
          ≤ Ck / (((L - d : ℕ)) : ℝ) ^ i := by
      intro d hd i hi
      have hdD : d ∈ D := (Finset.mem_filter.mp hd).1
      have heq : qd d = q := (Finset.mem_filter.mp hd).2
      have := (hqd_spec d hdD).2.2 i hi
      rwa [heq] at this
    obtain ⟨Q, hQ1, hQle, hQcond⟩ := hdesc L q D' (fun j => P.coeff j) hL2 hq1
      (by exact_mod_cast hqB) hLδ₁ hCkL hD'card hD'sub hD'cond
    have hQle2 : (Q : ℝ) ≤ max C₁ 1 := le_trans hQle (le_max_left _ _)
    have hsumP : (∑ n ∈ Finset.range L, eC (∑ j ∈ Finset.range ((k + 1) + 1),
          P.coeff j * (n : ℝ) ^ j)) = ∑ n ∈ Finset.range L, eC (P.eval (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      exact (eval_eq_sum_range_of_natDegree_le P (k + 1) hPnat (n : ℝ)).symm
    have hmaxL : max C₁ 1 ≤ (L : ℝ) := le_trans hL₀max (le_of_lt hcase)
    obtain ⟨m₁, hm₁⟩ := ha1 L Q (fun j => P.coeff j) C₁ hL2 hmaxL hQ1 hQle2 (le_of_lt hC₁pos)
      hQcond (by rw [hsumP]; exact hbig)
    refine ⟨Q, hQ1, le_trans hQle hCC₁, ?_⟩
    intro j hj
    have hjle : j ≤ k + 1 := (Finset.mem_Icc.mp hj).2
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    by_cases hje : j = 1
    · subst hje
      refine ⟨m₁, ?_⟩
      calc |(Q : ℝ) * P.coeff 1 - (m₁ : ℝ)| ≤ C₂ * (C₁ + 1) / (L : ℝ) := hm₁
        _ ≤ C / (L : ℝ) ^ 1 := by
            rw [pow_one, div_le_div_iff₀ hLpos hLpos]
            nlinarith [hCC₂, hLpos]
    · have hj2 : 2 ≤ j := by omega
      obtain ⟨m, hm⟩ := hQcond j (by rw [Finset.mem_Icc]; exact ⟨hj2, hjle⟩)
      refine ⟨m, ?_⟩
      calc |(Q : ℝ) * P.coeff j - (m : ℝ)| ≤ C₁ / (L : ℝ) ^ j := hm
        _ ≤ C / (L : ℝ) ^ j := by
            rw [div_le_div_iff₀ (pow_pos hLpos j) (pow_pos hLpos j)]
            nlinarith [hCC₁, pow_pos hLpos j]
  · -- small `L`
    have hLle : (L : ℝ) ≤ L₀ := not_lt.mp hcase
    refine ⟨1, le_refl 1, by simpa using hC1, ?_⟩
    intro j hj
    refine ⟨round (P.coeff j), ?_⟩
    rw [Nat.cast_one, one_mul]
    have hjle : j ≤ k + 1 := (Finset.mem_Icc.mp hj).2
    have hLj : (L : ℝ) ^ j ≤ L₀ ^ (k + 1) := by
      calc (L : ℝ) ^ j ≤ L₀ ^ j := pow_le_pow_left₀ (le_of_lt hLpos) hLle j
        _ ≤ L₀ ^ (k + 1) := pow_le_pow_right₀ hL₀1 hjle
    have hCL : (L : ℝ) ^ j ≤ 2 * C := by
      have h2 : L₀ ^ (k + 1) / 2 + 1 ≤ C := hCL₀
      nlinarith [hLj, h2, pow_pos (lt_of_lt_of_le zero_lt_one hL₀1) (k + 1)]
    calc |P.coeff j - (round (P.coeff j) : ℝ)| ≤ 1 / 2 := abs_sub_round _
      _ ≤ C / (L : ℝ) ^ j := by
          rw [div_le_div_iff₀ (by norm_num) (pow_pos hLpos j)]
          nlinarith [hCL]

theorem weylInvP_all : ∀ k : ℕ, WeylInvP k
  | 0 => weylInvP_zero
  | 1 => weylInvP_one
  | (k + 2) => weylInvP_succ (k + 1) (by omega) (weylInvP_all (k + 1))

theorem weyl_inverse (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → ℝ),
      δ * L ≤ ‖∑ n ∈ Finset.range L, eC (∑ j ∈ Finset.range (k + 1), a j * (n : ℝ) ^ j)‖ →
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C ∧
        ∀ j ∈ Finset.Icc 1 k, ∃ m : ℤ, |(q : ℝ) * a j - m| ≤ C / (L : ℝ) ^ j := by
  obtain ⟨C, hCpos, hC⟩ := weylInvP_all k δ hδ
  refine ⟨C, hCpos, ?_⟩
  intro L hL a hbig
  set P : Polynomial ℝ := ∑ j ∈ Finset.range (k + 1), Polynomial.monomial j (a j) with hPdef
  have hPcoeff : ∀ i ≤ k, P.coeff i = a i := by
    intro i hi
    rw [hPdef, Polynomial.finset_sum_coeff, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b hb hbne
      rw [Polynomial.coeff_monomial, if_neg (by omega : ¬ (b = i))]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  have hPeval : ∀ x : ℝ, P.eval x = ∑ j ∈ Finset.range (k + 1), a j * x ^ j := by
    intro x
    rw [hPdef, Polynomial.eval_finset_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [Polynomial.eval_monomial])
  have hPdeg : P.natDegree ≤ k := by
    rw [hPdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    refine le_trans (Polynomial.natDegree_monomial_le (a j)) ?_
    rw [Finset.mem_range] at hj; omega
  have hbridge : (∑ n ∈ Finset.range L, eC (P.eval (n : ℝ)))
      = ∑ n ∈ Finset.range L, eC (∑ j ∈ Finset.range (k + 1), a j * (n : ℝ) ^ j) :=
    Finset.sum_congr rfl (fun n _ => by rw [hPeval])
  obtain ⟨q, hq1, hqle, hq⟩ := hC L hL P hPdeg (by rw [hbridge]; exact hbig)
  refine ⟨q, hq1, hqle, ?_⟩
  intro j hj
  obtain ⟨m, hm⟩ := hq j hj
  exact ⟨m, by rwa [hPcoeff j (Finset.mem_Icc.mp hj).2] at hm⟩

end Work.BMF
