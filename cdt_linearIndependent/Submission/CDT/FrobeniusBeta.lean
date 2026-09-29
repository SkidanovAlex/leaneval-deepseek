import Submission.CDT.FrobeniusApply

/-!
# The Frobenius analysis at a root of the cubic `144y³ − 122y² + 118y − 1`

The eliminated operator at a root `β` of the cubic is Frobenius-regular, but the
factor `D1 = y(y−4)(72y+1)·cub` decomposes at `β` as `D1 = (X − Cβ)·Qmβ` where
`Qmβ = y(y−4)(72y+1)·(cub /ₘ (X − Cβ))`; at `β` the value of `Qmβ` is the
derivative `D1'(β)`, which is nonzero (the cubic is squarefree).

Writing `d = D1'(β)`, the four "leading coefficient" congruences
`2P_j ≡ a_j·(D1')^{4−j} (mod cub)` with `(a_0,a_1,a_2,a_3) = (6,−6,3,−1)`
(proved here by `ring`, using the explicit quotients `H_j`) give, after
evaluation at `β`,

`σ_β(N) = Σ_j (N)_j B_j(β)/d^4 = 6 − 6(N)_1 + 3(N)_2 − (N)_3 − (N)_4
        = −(N−3)(N−2)(N−1)(N+1)`,

so `σ_β(N) ≠ 0` for every integer `N ≤ −2` (the roots are `1,2,3,−1`).
This yields the local pole bound `ord_β b3 ≥ −1`.
-/

open Classical

noncomputable section

namespace Submission.CDT

open Polynomial

namespace FrobeniusApply

open Submission.CDT.Elim14C
open Submission.CDT.ElimOpC

set_option maxHeartbeats 1600000

/-! ## The explicit derivative polynomials -/

/-- `D1'`, as an explicit polynomial. -/
def dP : Polynomial ℂ :=
  4 - 370 * y - 100350 * y ^ 2 + 171736 * y ^ 3 - 250560 * y ^ 4 + 62208 * y ^ 5

/-- `cub'`, as an explicit polynomial. -/
def cubP : Polynomial ℂ := 118 - 244 * y + 432 * y ^ 2

/-- The polynomial `y(y−4)(72y+1)`. -/
def w : Polynomial ℂ := y * (y - 4) * (72 * y + 1)

/-- The derivative of `w`. -/
def wder : Polynomial ℂ := 216 * y ^ 2 - 574 * y - 4

lemma D1_factor : D1 = w * cub := by unfold D1 w cub y; ring

lemma dP_factor : dP = wder * cub + w * cubP := by unfold dP wder w cubP cub y; ring

lemma dP_wder : dP = 4 - 370 * y - 100350 * y ^ 2 + 171736 * y ^ 3 - 250560 * y ^ 4
    + 62208 * y ^ 5 := rfl

/-- `cubP` is the derivative of the cubic. -/
lemma cubP_eq_derivative : cubP = cub.derivative := by
  unfold cubP cub y
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_pow, Polynomial.derivative_intCast, mul_zero, zero_mul, add_zero,
    zero_add, mul_one, one_mul, map_ofNat Polynomial.C, Polynomial.C_eq_natCast]
  ring_nf

/-- `dP` is the derivative of `D1`. -/
lemma dP_eq_derivative : dP = D1.derivative := by
  unfold dP D1 y
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_pow, Polynomial.derivative_intCast, mul_zero, zero_mul, add_zero,
    zero_add, mul_one, one_mul, map_ofNat Polynomial.C, Polynomial.C_eq_natCast]
  ring_nf

/-! ## The Bezout identity making the cubic squarefree -/

/-- `cub` and `cub'` are coprime: the displayed Bezout identity. -/
lemma bezout : ((2909012 : Polynomial ℂ) - 3897936 * y) * cub
    + (1299312 * y ^ 2 - 1336606 * y + 776401) * cubP = 88706306 := by
  unfold cubP cub y; ring

/-! ## The values of the cubic at the excluded points -/

lemma cub_eval_zero_pt : cub.eval (0 : ℂ) = -1 := by unfold cub y; norm_num

lemma cub_eval_four : cub.eval (4 : ℂ) = 7735 := by unfold cub y; norm_num

lemma cub_eval_a72 : cub.eval a72 = -(3451 / 1296) := by unfold cub y a72; norm_num

lemma cubP_eval_ne_zero (β : ℂ) (hβ : cub.eval β = 0) : cubP.eval β ≠ 0 := by
  intro h
  have hb := congrArg (fun p : Polynomial ℂ => p.eval β) bezout
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_ofNat, h, hβ, mul_zero, add_zero,
    Polynomial.eval_intCast] at hb
  exact absurd hb (by norm_num)

lemma w_eval_eq (β : ℂ) : w.eval β = β * (β - 4) * (72 * β + 1) := by
  unfold w
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_intCast]

lemma w_eval_ne_zero (β : ℂ) (hβ : cub.eval β = 0) : w.eval β ≠ 0 := by
  rw [w_eval_eq]
  intro h
  rcases mul_eq_zero.mp h with h1 | h3
  · rcases mul_eq_zero.mp h1 with h0 | h4
    · rw [h0, cub_eval_zero_pt] at hβ
      norm_num at hβ
    · have h4' : β = 4 := sub_eq_zero.mp h4
      rw [h4', cub_eval_four] at hβ
      norm_num at hβ
  · have hb : β = a72 := by
      have h72 : (72 : ℂ) * β = -1 := by linear_combination h3
      have h' : β = -1 / 72 := by
        rw [eq_div_iff (by norm_num : (72 : ℂ) ≠ 0), mul_comm]
        exact h72
      rw [h']; unfold a72; norm_num
    rw [hb, cub_eval_a72] at hβ
    norm_num at hβ

lemma dP_eval_eq (β : ℂ) (hβ : cub.eval β = 0) : dP.eval β = w.eval β * cubP.eval β := by
  rw [dP_factor]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_intCast,
    hβ, mul_zero, zero_add]

lemma D1_derivative_eval (β : ℂ) (hβ : cub.eval β = 0) : (D1.derivative).eval β = dP.eval β := by
  have hdiff : D1.derivative = w.derivative * cub + w * cub.derivative := by
    rw [D1_factor, Polynomial.derivative_mul]
  rw [hdiff, dP_eval_eq β hβ, cubP_eq_derivative]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_ofNat, hβ, mul_zero, add_zero,
    zero_add]

lemma dP_eval_ne_zero (β : ℂ) (hβ : cub.eval β = 0) : dP.eval β ≠ 0 := by
  rw [dP_eval_eq β hβ]
  exact mul_ne_zero (w_eval_ne_zero β hβ) (cubP_eval_ne_zero β hβ)

/-! ## The four leading-coefficient congruences modulo the cubic -/

/-- The quotient of `2P_3 - (-1)dP` by `cub`. -/
def H3 : Polynomial ℂ :=
  (1008 : Polynomial ℂ) * y ^ 2 - 2870 * y - 24

/-- The quotient of `2P_2 - 3 dP^2` by `cub`. -/
def H2 : Polynomial ℂ :=
  (-108988416 : Polynomial ℂ) * y ^ 7 + 752364288 * y ^ 6 - 1626867360 * y ^ 5
    + 1068247452 * y ^ 4 - 551237926 * y ^ 3 - 5566802 * y ^ 2 + 20506 * y + 356

/-- The quotient of `2P_1 + 6 dP^3` by `cub`. -/
def H1 : Polynomial ℂ :=
  (10866497421312 : Polynomial ℂ) * y ^ 12 - 120622335197184 * y ^ 11
    + 504175754280960 * y ^ 10 - 981191292715008 * y ^ 9 + 991773386673408 * y ^ 8
    - 696954400149216 * y ^ 7 + 283121344925840 * y ^ 6 - 76034926158872 * y ^ 5
    - 1094319023576 * y ^ 4 + 1746298180 * y ^ 3 + 93595934 * y ^ 2 - 25780 * y - 3408

/-- The quotient of `2P_0 - 6 dP^4` by `cub`. -/
def H0 : Polynomial ℂ :=
  (-635539639951687680 : Polynomial ℂ) * y ^ 17 + 9673558845737140224 * y ^ 16
    - 60042861469463740416 * y ^ 15 + 196632484509797056512 * y ^ 14
    - 376281145898475945984 * y ^ 13 + 462059281957072785408 * y ^ 12
    - 406035842445674044416 * y ^ 11 + 253219799291264211072 * y ^ 10
    - 114934380748249055840 * y ^ 9 + 33433259535840911360 * y ^ 8
    - 5825993239029703680 * y ^ 7 - 120911797782806032 * y ^ 6 - 237383389410644 * y ^ 5
    + 9850352640540 * y ^ 4 + 17315561838 * y ^ 3 - 579604668 * y ^ 2 - 660576 * y + 15936

lemma cong_three : 2 * P3 - (-1) * dP ^ 1 = cub * H3 := by
  unfold H3 P3 dP cub y; ring

lemma cong_two : 2 * P2 - 3 * dP ^ 2 = cub * H2 := by
  unfold H2 P2 dP cub y; ring

lemma cong_one : 2 * P1 - (-6) * dP ^ 3 = cub * H1 := by
  unfold H1 P1 dP cub y; ring

lemma cong_zero : 2 * P0 - 6 * dP ^ 4 = cub * H0 := by
  unfold H0 P0 dP cub y; ring

/-- Evaluation of a congruence at a root `β` of the cubic. -/
lemma two_P0_eval (β : ℂ) (hβ : cub.eval β = 0) : (2 * P0).eval β = 6 * (dP.eval β) ^ 4 := by
  have h := congrArg (fun q : Polynomial ℂ => q.eval β) cong_zero
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_ofNat, Polynomial.eval_intCast, Polynomial.eval_C, Polynomial.eval_one, pow_one,
    hβ, Polynomial.eval_zero, zero_mul] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
  linear_combination h

lemma two_P1_eval (β : ℂ) (hβ : cub.eval β = 0) : (2 * P1).eval β = -6 * (dP.eval β) ^ 3 := by
  have h := congrArg (fun q : Polynomial ℂ => q.eval β) cong_one
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_ofNat, Polynomial.eval_intCast, Polynomial.eval_C, Polynomial.eval_one, pow_one,
    hβ, Polynomial.eval_zero, zero_mul] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
  linear_combination h

lemma two_P2_eval (β : ℂ) (hβ : cub.eval β = 0) : (2 * P2).eval β = 3 * (dP.eval β) ^ 2 := by
  have h := congrArg (fun q : Polynomial ℂ => q.eval β) cong_two
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_ofNat, Polynomial.eval_intCast, Polynomial.eval_C, Polynomial.eval_one, pow_one,
    hβ, Polynomial.eval_zero, zero_mul] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
  linear_combination h

lemma two_P3_eval (β : ℂ) (hβ : cub.eval β = 0) : (2 * P3).eval β = -(dP.eval β) := by
  have h := congrArg (fun q : Polynomial ℂ => q.eval β) cong_three
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_ofNat, Polynomial.eval_intCast, Polynomial.eval_C, Polynomial.eval_one, pow_one,
    hβ, Polynomial.eval_zero, zero_mul] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
  linear_combination h

/-- `cub /ₘ (X - C β)`, so that `cub = (X - C β)·qb β` at a root `β`. -/
def qb (β : ℂ) : Polynomial ℂ := cub /ₘ (Polynomial.X - Polynomial.C β)

/-- `Qmb β := y(y−4)(72y+1)·qb β`, so that `D1 = (X - C β)·Qmb β` at a root `β`. -/
def Qmb (β : ℂ) : Polynomial ℂ := w * qb β

lemma cub_eq_mul_qb (β : ℂ) (hβ : cub.eval β = 0) :
    cub = (Polynomial.X - Polynomial.C β) * qb β := by
  rw [qb]
  exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hβ).symm

/-- At a root `β` of the cubic, `D1 = (X − Cβ)·Qmb β`. -/
lemma D1_eq_mul_Qmb (β : ℂ) (hβ : cub.eval β = 0) :
    D1 = (Polynomial.X - Polynomial.C β) * Qmb β := by
  rw [D1_factor, Qmb, cub_eq_mul_qb β hβ]
  ring

/-- The value `(qb β)(β) = cub'(β) = cubP(β)`. -/
lemma qb_eval (β : ℂ) : (qb β).eval β = cubP.eval β := by
  have h := Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative cub β
  rw [qb, cubP_eq_derivative, ← h]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_mul, add_zero]

/-- `(Qmb β)(β) = D1'(β)`. -/
lemma Qmb_eval (β : ℂ) (hβ : cub.eval β = 0) : (Qmb β).eval β = dP.eval β := by
  rw [Qmb, Polynomial.eval_mul, qb_eval β, dP_eval_eq β hβ]

/-- The Frobenius coefficients at a root `β` of the cubic. -/
def Bfunb (β : ℂ) : ℕ → Polynomial ℂ
  | 0 => 2 * P0
  | 1 => 2 * P1 * Qmb β
  | 2 => 2 * P2 * Qmb β ^ 2
  | 3 => 2 * P3 * Qmb β ^ 3
  | _ => -(Qmb β ^ 4)

lemma Bfunb_eq_zero (β : ℂ) : Bfunb β 0 = 2 * P0 := rfl
lemma Bfunb_eq_one (β : ℂ) : Bfunb β 1 = 2 * P1 * Qmb β := rfl
lemma Bfunb_eq_two (β : ℂ) : Bfunb β 2 = 2 * P2 * Qmb β ^ 2 := rfl
lemma Bfunb_eq_three (β : ℂ) : Bfunb β 3 = 2 * P3 * Qmb β ^ 3 := rfl
lemma Bfunb_eq_four (β : ℂ) : Bfunb β 4 = -(Qmb β ^ 4) := rfl

lemma A_split_beta (β : ℂ) (hβ : cub.eval β = 0) :
    ∀ j ∈ Finset.range 5, Afun j = (Polynomial.X - Polynomial.C β) ^ j * Bfunb β j := by
  intro j hj
  simp only [Finset.mem_range] at hj
  interval_cases j <;>
    simp only [Afun_eq_zero, Afun_eq_one, Afun_eq_two, Afun_eq_three, Afun_eq_four,
      Bfunb_eq_zero, Bfunb_eq_one, Bfunb_eq_two, Bfunb_eq_three, Bfunb_eq_four,
      D1_eq_mul_Qmb β hβ] <;> ring

lemma Bfunb_eval0 (β : ℂ) (hβ : cub.eval β = 0) :
    (Bfunb β 0).eval β = 6 * (dP.eval β) ^ 4 := by
  rw [Bfunb_eq_zero]
  exact two_P0_eval β hβ

lemma Bfunb_eval1 (β : ℂ) (hβ : cub.eval β = 0) :
    (Bfunb β 1).eval β = -6 * (dP.eval β) ^ 4 := by
  rw [Bfunb_eq_one, Polynomial.eval_mul, two_P1_eval β hβ, Qmb_eval β hβ]
  ring

lemma Bfunb_eval2 (β : ℂ) (hβ : cub.eval β = 0) :
    (Bfunb β 2).eval β = 3 * (dP.eval β) ^ 4 := by
  rw [Bfunb_eq_two, Polynomial.eval_mul, Polynomial.eval_pow, two_P2_eval β hβ, Qmb_eval β hβ]
  ring

lemma Bfunb_eval3 (β : ℂ) (hβ : cub.eval β = 0) :
    (Bfunb β 3).eval β = -(dP.eval β) ^ 4 := by
  rw [Bfunb_eq_three, Polynomial.eval_mul, Polynomial.eval_pow, two_P3_eval β hβ, Qmb_eval β hβ]
  ring

lemma Bfunb_eval4 (β : ℂ) (hβ : cub.eval β = 0) :
    (Bfunb β 4).eval β = -(dP.eval β) ^ 4 := by
  rw [Bfunb_eq_four, Polynomial.eval_neg, Polynomial.eval_pow, Qmb_eval β hβ]

/-- The indicial value at a root `β` of the cubic. -/
lemma sigma_beta_val (β : ℂ) (hβ : cub.eval β = 0) (N : ℤ) :
    (∑ j ∈ Finset.range 5, (fallFact N j : ℂ) * (Bfunb β j).eval β)
      = -((dP.eval β) ^ 4 * (((N : ℂ) - 3) * ((N : ℂ) - 2) * ((N : ℂ) - 1)
          * ((N : ℂ) + 1))) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [Bfunb_eval0 β hβ, Bfunb_eval1 β hβ, Bfunb_eval2 β hβ, Bfunb_eval3 β hβ,
    Bfunb_eval4 β hβ]
  rw [fallFact_zero, fallFact1 N, fallFact2 N, fallFact3 N, fallFact4 N]
  push_cast
  ring

lemma beta_prod_ne_zero (N : ℤ) (hN : N ≤ -2) :
    ((N : ℂ) - 3) * ((N : ℂ) - 2) * ((N : ℂ) - 1) * ((N : ℂ) + 1) ≠ 0 := by
  have h3 : (N : ℂ) - 3 ≠ 0 := by
    intro h
    have : N = 3 := by exact_mod_cast (sub_eq_zero.mp h)
    omega
  have h2 : (N : ℂ) - 2 ≠ 0 := by
    intro h
    have : N = 2 := by exact_mod_cast (sub_eq_zero.mp h)
    omega
  have h1 : (N : ℂ) - 1 ≠ 0 := by
    intro h
    have : N = 1 := by exact_mod_cast (sub_eq_zero.mp h)
    omega
  have hm : (N : ℂ) + 1 ≠ 0 := by
    intro h
    have h' : (N : ℂ) = -1 := by linear_combination h
    have : N = -1 := by exact_mod_cast h'
    omega
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h3 h2) h1) hm

/-- **The local bound at a root `β` of the cubic.**  `ord_β b3 ≥ −1`. -/
theorem beta_local (β : ℂ) (hβ : cub.eval β = 0) (b0 b1 b2 b3 R : RF) (hb : b3 ≠ 0)
    (hR : R ≠ 0) (hRlow : (0 : ℤ) ≤ ordAt β R)
    (h1 : dRat b3 + b2 - Ww * b3 = 0) (h2 : dRat b2 + b1 - Vv * b3 = 0)
    (h3 : dRat b1 + b0 - Uu * b3 = 0) (h4 : dRat b0 - Zz * b3 = R) :
    (-1 : ℤ) ≤ ordAt β b3 := by
  have hd : dP.eval β ≠ 0 := dP_eval_ne_zero β hβ
  have hQmb : Qmb β ≠ 0 := by
    intro h
    exact hd (by rw [← Qmb_eval β hβ, h]; simp)
  have hsplit : D1 = (Polynomial.X - Polynomial.C β) * Qmb β := D1_eq_mul_Qmb β hβ
  have hEq : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3)) = am (D1 ^ 4) * R := by
    rw [sum5_expand]
    exact elim_equation_cleared b0 b1 b2 b3 R h1 h2 h3 h4
  have hrm : Polynomial.rootMultiplicity β D1 = 1 := by
    rw [hsplit, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (Polynomial.X_sub_C_ne_zero β) hQmb),
      Polynomial.rootMultiplicity_X_sub_C_self]
    have hq : Polynomial.rootMultiplicity β (Qmb β) = 0 := by
      rw [Polynomial.rootMultiplicity_eq_zero]
      intro hroot
      rw [Polynomial.IsRoot] at hroot
      exact hd (by rw [← Qmb_eval β hβ]; exact hroot)
    rw [hq, add_zero]
  have hσ : ∀ N : ℤ, N ≤ (-2 : ℤ) → (∑ j ∈ Finset.range 5,
      (fallFact N j : ℂ) * (Bfunb β j).eval β) ≠ 0 := by
    intro N hN hzero
    rw [sigma_beta_val β hβ N] at hzero
    exact (mul_ne_zero (pow_ne_zero 4 hd) (beta_prod_ne_zero N hN)) (neg_eq_zero.mp hzero)
  have hK : (-2 : ℤ) < (4 * (Polynomial.rootMultiplicity β D1 : ℤ)) + ordAt β R := by
    rw [hrm]; omega
  have h := tie_bound β (-2) (Polynomial.X - Polynomial.C β) (Bfunb β) b3 R hb hR rfl hEq
    (A_split_beta β hβ) hσ hK
  omega

end FrobeniusApply

end Submission.CDT
