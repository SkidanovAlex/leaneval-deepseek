import Submission.CDT.DnumDegree
import Submission.CDT.DivisorBound
import Submission.CDT.ElimReductionC
import Submission.Commons.Analysis.Arithmetic.indicial_infty_ne_zero

open Classical
noncomputable section
namespace Submission.CDT
open Polynomial
namespace FrobeniusApply
open Submission.CDT.Elim14C
open Submission.CDT.ElimOpC
set_option maxHeartbeats 4000000

/-- The ansatz factor `y²(y−4)²(y + 1/72)`. -/
def Pz : Polynomial ℂ :=
  (Polynomial.X - Polynomial.C (0 : ℂ)) ^ 2 * (Polynomial.X - Polynomial.C (4 : ℂ)) ^ 2
    * (Polynomial.X - Polynomial.C a72)

lemma Pz_natDegree : Pz.natDegree = 5 := by
  unfold Pz
  compute_degree!

lemma Pz_leadingCoeff : Pz.leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, Pz_natDegree]
  unfold Pz
  compute_degree!

lemma D1_natDegree : D1.natDegree = 6 := by unfold D1 y; compute_degree!

lemma D1_leadingCoeff : D1.leadingCoeff = 10368 := by
  rw [Polynomial.leadingCoeff, D1_natDegree]; unfold D1 y; compute_degree!

lemma w_natDegree : w.natDegree = 3 := by unfold w y; compute_degree!

lemma w_leadingCoeff : w.leadingCoeff = 72 := by
  rw [Polynomial.leadingCoeff, w_natDegree]; unfold w y; compute_degree!

lemma cub_natDegree : cub.natDegree = 3 := by unfold cub y; compute_degree!

lemma cub_leadingCoeff : cub.leadingCoeff = 144 := by
  rw [Polynomial.leadingCoeff, cub_natDegree]; unfold cub y; compute_degree!

lemma P0_natDegree : P0.natDegree = 20 := by unfold P0 y; compute_degree!
lemma P1_natDegree : P1.natDegree = 15 := by unfold P1 y; compute_degree!
lemma P2_natDegree : P2.natDegree = 10 := by unfold P2 y; compute_degree!
lemma P3_natDegree : P3.natDegree = 5 := by unfold P3 y; compute_degree!

lemma two_P0_leadingCoeff : (2 * P0).leadingCoeff = (-1663958330055327744 : ℂ) := by
  rw [Polynomial.leadingCoeff, show (2 * P0).natDegree = 20 from by
    rw [Polynomial.natDegree_mul (by norm_num) P0_ne_zero, P0_natDegree]; norm_num]
  unfold P0 y; compute_degree!

/-! ## The leading behaviour at infinity -/

/-- The coefficient of `b₃^{(j)}` in the *cleared* ∞-chart operator, i.e.
`Afun j / cub^j` (the factor `cub^j` being cancelled). -/
def Acoef : ℕ → Polynomial ℂ
  | 0 => 2 * P0
  | 1 => 2 * P1 * w
  | 2 => 2 * P2 * w ^ 2
  | 3 => 2 * P3 * w ^ 3
  | _ => -(w ^ 4)

lemma Acoef_eq_zero : Acoef 0 = 2 * P0 := rfl
lemma Acoef_eq_one : Acoef 1 = 2 * P1 * w := rfl
lemma Acoef_eq_two : Acoef 2 = 2 * P2 * w ^ 2 := rfl
lemma Acoef_eq_three : Acoef 3 = 2 * P3 * w ^ 3 := rfl
lemma Acoef_eq_four : Acoef 4 = -(w ^ 4) := rfl

/-- The numerator of the eliminated operator applied to the ansatz
`b₃ = (y²(y−4)²(y+1/72)·Q)/cub`, after cancelling `cub⁴`. -/
def POLYq (Q : Polynomial ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range 5, Acoef j * dnum (Pz * Q) cub j

lemma POLYq_expand (Q : Polynomial ℂ) :
    POLYq Q = Acoef 0 * dnum (Pz * Q) cub 0 + Acoef 1 * dnum (Pz * Q) cub 1
      + Acoef 2 * dnum (Pz * Q) cub 2 + Acoef 3 * dnum (Pz * Q) cub 3
      + Acoef 4 * dnum (Pz * Q) cub 4 := by
  simp only [POLYq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

lemma dnum_zero' (p q : Polynomial ℂ) : dnum p q 0 = p := rfl

/-- `cub⁴·POLYq Q` is the numerator of the cleared equation. -/
lemma mul_POLYq (Q : Polynomial ℂ) :
    cub ^ 4 * POLYq Q
      = ∑ j ∈ Finset.range 5, Afun j * dnum (Pz * Q) cub j * cub ^ (4 - j) := by
  rw [POLYq_expand]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Afun_eq_zero, Afun_eq_one, Afun_eq_two, Afun_eq_three, Afun_eq_four,
    Acoef_eq_zero, Acoef_eq_one, Acoef_eq_two, Acoef_eq_three, Acoef_eq_four, dnum_zero',
    D1_factor]
  ring

lemma two_P1_leadingCoeff : (2 * P1).leadingCoeff = (120367356051456 : ℂ) := by
  rw [Polynomial.leadingCoeff, show (2 * P1).natDegree = 15 from by
    rw [Polynomial.natDegree_mul (by norm_num) P1_ne_zero, P1_natDegree]; norm_num]
  unfold P1 y; compute_degree!

lemma two_P2_leadingCoeff : (2 * P2).leadingCoeff = (-4084826112 : ℂ) := by
  rw [Polynomial.leadingCoeff, show (2 * P2).natDegree = 10 from by
    rw [Polynomial.natDegree_mul (by norm_num) P2_ne_zero, P2_natDegree]; norm_num]
  unfold P2 y; compute_degree!

lemma two_P3_leadingCoeff : (2 * P3).leadingCoeff = (82944 : ℂ) := by
  rw [Polynomial.leadingCoeff, show (2 * P3).natDegree = 5 from by
    rw [Polynomial.natDegree_mul (by norm_num) P3_ne_zero, P3_natDegree]; norm_num]
  unfold P3 y; compute_degree!

/-! ## The degrees and leading coefficients of the `Afun j` -/

lemma Afun_natDegree_zero : (Afun 0).natDegree = 20 := by
  rw [Afun_eq_zero]
  rw [Polynomial.natDegree_mul (by norm_num) P0_ne_zero, P0_natDegree]
  norm_num

lemma Afun_natDegree_one : (Afun 1).natDegree = 21 := by
  rw [Afun_eq_one]
  rw [Polynomial.natDegree_mul (mul_ne_zero (by norm_num) P1_ne_zero) D1_ne_zero,
    Polynomial.natDegree_mul (by norm_num) P1_ne_zero, P1_natDegree, D1_natDegree]
  norm_num

lemma Afun_natDegree_two : (Afun 2).natDegree = 22 := by
  rw [Afun_eq_two]
  rw [Polynomial.natDegree_mul (mul_ne_zero (by norm_num) P2_ne_zero) (pow_ne_zero 2 D1_ne_zero),
    Polynomial.natDegree_mul (by norm_num) P2_ne_zero, P2_natDegree,
    Polynomial.natDegree_pow, D1_natDegree]
  norm_num

lemma Afun_natDegree_three : (Afun 3).natDegree = 23 := by
  rw [Afun_eq_three]
  rw [Polynomial.natDegree_mul (mul_ne_zero (by norm_num) P3_ne_zero) (pow_ne_zero 3 D1_ne_zero),
    Polynomial.natDegree_mul (by norm_num) P3_ne_zero, P3_natDegree,
    Polynomial.natDegree_pow, D1_natDegree]
  norm_num

lemma Afun_natDegree_four : (Afun 4).natDegree = 24 := by
  rw [Afun_eq_four, Polynomial.natDegree_neg, Polynomial.natDegree_pow, D1_natDegree]


lemma Afun_lc_zero : (Afun 0).leadingCoeff = (-1663958330055327744 : ℂ) := by
  rw [Afun_eq_zero]; exact two_P0_leadingCoeff

lemma Afun_lc_one : (Afun 1).leadingCoeff = (1247968747541495808 : ℂ) := by
  rw [Afun_eq_one, Polynomial.leadingCoeff_mul, two_P1_leadingCoeff, D1_leadingCoeff]
  norm_num

lemma Afun_lc_two : (Afun 2).leadingCoeff = (-439100114875711488 : ℂ) := by
  rw [Afun_eq_two, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow,
    two_P2_leadingCoeff, D1_leadingCoeff]
  norm_num

lemma Afun_lc_three : (Afun 3).leadingCoeff = (92442129447518208 : ℂ) := by
  rw [Afun_eq_three, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow,
    two_P3_leadingCoeff, D1_leadingCoeff]
  norm_num

lemma Afun_lc_four : (Afun 4).leadingCoeff = (-11555266180939776 : ℂ) := by
  rw [Afun_eq_four, Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_pow, D1_leadingCoeff]
  norm_num

/-! ## The indicial value at infinity -/

/-- The indicial value at `∞` in terms of the rational indicial polynomial
`−144 + 108N − 38N(N−1) + 8N(N−1)(N−2) − N(N−1)(N−2)(N−3)`. -/
lemma sigma_infty_val (N : ℤ) :
    (∑ j ∈ Finset.range 5, (fallFact N j : ℂ) * (Afun j).leadingCoeff)
      = ((10368 : ℂ) ^ 4) * (((-144 : ℚ) + 108 * (N : ℚ)
          + (-38) * ((N : ℚ) * ((N : ℚ) - 1))
          + 8 * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2))
          + (-1) * ((N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) * ((N : ℚ) - 3)) : ℚ) : ℂ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, fallFact_zero,
    Int.cast_one, one_mul, fallFact1, fallFact2, fallFact3, fallFact4, Afun_lc_zero,
    Afun_lc_one, Afun_lc_two, Afun_lc_three, Afun_lc_four]
  push_cast
  ring

/-! ## The main bound at infinity -/

lemma Pz_ne_zero : Pz ≠ 0 := by
  intro h
  have h1 : Pz.natDegree = 0 := by rw [h]; simp
  rw [Pz_natDegree] at h1
  norm_num at h1

lemma w_ne_zero : w ≠ 0 := by
  intro h
  have h1 : w.eval (1 : ℂ) = 0 := by rw [h]; simp
  unfold w y at h1
  norm_num at h1

lemma Afun_eq_Acoef_mul (j : ℕ) (hj : j ∈ Finset.range 5) : Afun j = Acoef j * cub ^ j := by
  simp only [Finset.mem_range] at hj
  interval_cases j <;>
    simp only [Afun_eq_zero, Afun_eq_one, Afun_eq_two, Afun_eq_three, Afun_eq_four,
      Acoef_eq_zero, Acoef_eq_one, Acoef_eq_two, Acoef_eq_three, Acoef_eq_four, D1_factor]
      <;> ring

lemma Acoef_ne_zero (j : ℕ) (hj : j ∈ Finset.range 5) : Acoef j ≠ 0 := by
  have h := Afun_eq_Acoef_mul j hj
  intro h0
  rw [h0, zero_mul] at h
  exact Afun_ne_zero j hj h

lemma Acoef_natDegree_zero : (Acoef 0).natDegree = 20 := by
  rw [Acoef_eq_zero, Polynomial.natDegree_mul (by norm_num : (2 : Polynomial ℂ) ≠ 0) P0_ne_zero,
    Polynomial.natDegree_ofNat (R := ℂ), P0_natDegree]

lemma Acoef_natDegree_one : (Acoef 1).natDegree = 18 := by
  rw [Acoef_eq_one,
    Polynomial.natDegree_mul (mul_ne_zero (by norm_num : (2 : Polynomial ℂ) ≠ 0) P1_ne_zero)
      w_ne_zero,
    Polynomial.natDegree_mul (by norm_num : (2 : Polynomial ℂ) ≠ 0) P1_ne_zero,
    Polynomial.natDegree_ofNat (R := ℂ), P1_natDegree, w_natDegree]

lemma Acoef_natDegree_two : (Acoef 2).natDegree = 16 := by
  rw [Acoef_eq_two,
    Polynomial.natDegree_mul (mul_ne_zero (by norm_num : (2 : Polynomial ℂ) ≠ 0) P2_ne_zero)
      (pow_ne_zero 2 w_ne_zero),
    Polynomial.natDegree_mul (by norm_num : (2 : Polynomial ℂ) ≠ 0) P2_ne_zero,
    Polynomial.natDegree_ofNat (R := ℂ), P2_natDegree, Polynomial.natDegree_pow, w_natDegree]

lemma Acoef_natDegree_three : (Acoef 3).natDegree = 14 := by
  rw [Acoef_eq_three,
    Polynomial.natDegree_mul (mul_ne_zero (by norm_num : (2 : Polynomial ℂ) ≠ 0) P3_ne_zero)
      (pow_ne_zero 3 w_ne_zero),
    Polynomial.natDegree_mul (by norm_num : (2 : Polynomial ℂ) ≠ 0) P3_ne_zero,
    Polynomial.natDegree_ofNat (R := ℂ), P3_natDegree, Polynomial.natDegree_pow, w_natDegree]

lemma Acoef_natDegree_four : (Acoef 4).natDegree = 12 := by
  rw [Acoef_eq_four, Polynomial.natDegree_neg, Polynomial.natDegree_pow, w_natDegree]

lemma Acoef_natDegree (j : ℕ) (hj : j ∈ Finset.range 5) :
    (Acoef j).natDegree = (if j < 4 then 20 - 2 * j else 12) := by
  simp only [Finset.mem_range] at hj
  interval_cases j
  · simpa using Acoef_natDegree_zero
  · simpa using Acoef_natDegree_one
  · simpa using Acoef_natDegree_two
  · simpa using Acoef_natDegree_three
  · simpa using Acoef_natDegree_four



/-! ## The cleared equation in the `∞` chart -/

/-- **The cleared identity.**  The ansatz `b₃ = y²(y−4)²(y+1/72)Q/cub` turns the
eliminated equation into the polynomial identity
`POLYq Q · y² = w⁴·cub⁵·Rnum` (after cancelling `cub⁴`). -/
lemma POLYq_mul_X2 (Q Rnum : Polynomial ℂ) (b3 : RF)
    (hb3 : b3 = am (Pz * Q) / am cub)
    (hEq : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3))
        = am (D1 ^ 4) * (am Rnum / am (Polynomial.X ^ 2))) :
    POLYq Q * Polynomial.X ^ 2 = w ^ 4 * cub ^ 5 * Rnum := by
  have hc0 : am cub ≠ 0 := RatFunc.algebraMap_ne_zero cub_ne_zero
  have hX0 : am (Polynomial.X ^ 2) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero)
  have hb3j : ∀ j : ℕ, dRat^[j] b3 = am (dnum (Pz * Q) cub j) / am cub ^ (j + 1) := by
    intro j
    rw [hb3]
    exact dRat_iterate_dnum (Pz * Q) cub cub_ne_zero j
  have hterm : ∀ j ∈ Finset.range 5,
      am (Afun j) * (dRat^[j] b3) * (am cub ^ 5 * am (Polynomial.X ^ 2))
        = am (Afun j * dnum (Pz * Q) cub j * cub ^ (4 - j) * Polynomial.X ^ 2) := by
    intro j hj
    have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hj; omega
    rw [hb3j j]
    have hexp : (j + 1) + (4 - j) = 5 := by omega
    have hdiv : am cub ^ (5 : ℕ) / am cub ^ (j + 1) = am cub ^ (4 - j) := by
      rw [show (5 : ℕ) = (j + 1) + (4 - j) from hexp.symm, pow_add,
        mul_div_cancel_left₀ _ (pow_ne_zero _ hc0)]
    calc am (Afun j) * (am (dnum (Pz * Q) cub j) / am cub ^ (j + 1))
          * (am cub ^ 5 * am (Polynomial.X ^ 2))
        = am (Afun j) * am (dnum (Pz * Q) cub j) * (am cub ^ (5 : ℕ) / am cub ^ (j + 1))
            * am (Polynomial.X ^ 2) := by ring
      _ = am (Afun j) * am (dnum (Pz * Q) cub j) * am cub ^ (4 - j)
            * am (Polynomial.X ^ 2) := by rw [hdiv]
      _ = am (Afun j * dnum (Pz * Q) cub j * cub ^ (4 - j) * Polynomial.X ^ 2) := by
            rw [← map_pow, ← map_mul, ← map_mul, ← map_mul]
  have hL : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3))
      * (am cub ^ 5 * am (Polynomial.X ^ 2)) = am (POLYq Q * cub ^ 4 * Polynomial.X ^ 2) := by
    rw [Finset.sum_mul]
    refine (Finset.sum_congr rfl hterm).trans ?_
    rw [← map_sum]
    congr 1
    rw [show (∑ j ∈ Finset.range 5, Afun j * dnum (Pz * Q) cub j * cub ^ (4 - j) * Polynomial.X ^ 2)
        = (∑ j ∈ Finset.range 5, Afun j * dnum (Pz * Q) cub j * cub ^ (4 - j)) * Polynomial.X ^ 2
        from by rw [Finset.sum_mul]]
    rw [← mul_POLYq Q]
    ring
  have hR1 : am (D1 ^ 4) * (am Rnum / am (Polynomial.X ^ 2))
      * (am cub ^ 5 * am (Polynomial.X ^ 2)) = am (D1 ^ 4) * am Rnum * am cub ^ 5 := by
    field_simp
  have hR2 : am (D1 ^ 4) * am Rnum * am cub ^ 5 = am (w ^ 4 * cub ^ 9 * Rnum) := by
    have hD : (D1 : Polynomial ℂ) ^ 4 = w ^ 4 * cub ^ 4 := by rw [D1_factor]; ring
    rw [← map_mul, ← map_pow, ← map_mul, hD]
    apply congrArg (algebraMap (Polynomial ℂ) (RatFunc ℂ))
    ring
  have hR : am (D1 ^ 4) * (am Rnum / am (Polynomial.X ^ 2))
      * (am cub ^ 5 * am (Polynomial.X ^ 2)) = am (w ^ 4 * cub ^ 9 * Rnum) := by
    rw [hR1, hR2]
  have hbig : am (POLYq Q * cub ^ 4 * Polynomial.X ^ 2) = am (w ^ 4 * cub ^ 9 * Rnum) := by
    rw [← hL, ← hR]
    exact congrArg (fun x : RF => x * (am cub ^ 5 * am (Polynomial.X ^ 2))) hEq
  have hpoly := RatFunc.algebraMap_injective (K := ℂ) hbig
  have hpoly' : (POLYq Q * Polynomial.X ^ 2) * cub ^ 4 = (w ^ 4 * cub ^ 5 * Rnum) * cub ^ 4 := by
    calc (POLYq Q * Polynomial.X ^ 2) * cub ^ 4
        = POLYq Q * cub ^ 4 * Polynomial.X ^ 2 := by ring
      _ = w ^ 4 * cub ^ 9 * Rnum := hpoly
      _ = (w ^ 4 * cub ^ 5 * Rnum) * cub ^ 4 := by ring
  exact mul_right_cancel₀ (pow_ne_zero 4 cub_ne_zero) hpoly'

/-! ## The main bound at infinity -/

/-- **The bound at `∞`.**  If `b₃ = y²(y−4)²(y + 1/72)·Q/cub` satisfies the
eliminated equation with right-hand side `Rnum/y²`, and `Rnum` has degree at
most `2`, then `Q` has degree at most `2`.  This is the paper's bound
`N_∞ ≤ 4`. -/
theorem infty_bound (Q Rnum : Polynomial ℂ) (hQ : Q ≠ 0) (hRnum : Rnum ≠ 0)
    (hRdeg : Rnum.natDegree ≤ 2) (b3 : RF) (hb3 : b3 = am (Pz * Q) / am cub)
    (hEq : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3))
        = am (D1 ^ 4) * (am Rnum / am (Polynomial.X ^ 2))) :
    Q.natDegree ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  have hQlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hPzQdeg : (Pz * Q).natDegree = 5 + Q.natDegree := by
    rw [Polynomial.natDegree_mul Pz_ne_zero hQ, Pz_natDegree]
  have hPzQne : (Pz * Q) ≠ 0 := mul_ne_zero Pz_ne_zero hQ
  have hPzQlc : (Pz * Q).leadingCoeff = Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Pz_leadingCoeff, one_mul]
  have hN : ((Pz * Q).natDegree : ℤ) - 3 = (Q.natDegree : ℤ) + 2 := by
    rw [hPzQdeg]; push_cast; ring
  have hN5 : (5 : ℤ) ≤ ((Pz * Q).natDegree : ℤ) - 3 := by rw [hN]; omega
  have hNk : ∀ k : ℕ, k < 5 → ((Pz * Q).natDegree : ℤ) - 3 - (k : ℤ) ≠ 0 := by
    intro k hk; rw [hN]; omega
  have hpq : (Pz * Q).natDegree ≠ 0 := by rw [hPzQdeg]; omega
  have hC : ∀ j : ℕ, j ≤ 4 →
      (dnum (Pz * Q) cub j).natDegree = (Pz * Q).natDegree + 2 * j ∧
      (dnum (Pz * Q) cub j).leadingCoeff
        = (144 : ℂ) ^ j * ((fallFact (((Pz * Q).natDegree : ℤ) - 3) j : ℤ) : ℂ)
          * (Pz * Q).leadingCoeff := by
    intro j hj
    have h := dnum_natDegree_leadingCoeff (Pz * Q) cub cub_natDegree hpq j
      (fun k hk => hNk k (by omega))
    rwa [cub_leadingCoeff] at h
  have hfall : ∀ j : ℕ, j ≤ 4 → ((fallFact (((Pz * Q).natDegree : ℤ) - 3) j : ℤ) : ℂ) ≠ 0 := by
    intro j hj
    exact fallFact_cast_ne_zero (fun k hk => hNk k (by omega))
  have hCne : ∀ j : ℕ, j ≤ 4 → dnum (Pz * Q) cub j ≠ 0 := by
    intro j hj
    rw [← Polynomial.leadingCoeff_ne_zero, (hC j hj).2]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hfall j hj))
      (by rw [hPzQlc]; exact hQlc)
  have hTdeg : ∀ j ∈ Finset.range 5,
      (Acoef j * dnum (Pz * Q) cub j).natDegree = Q.natDegree + 25 := by
    intro j hj
    have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hj; omega
    rw [Polynomial.natDegree_mul (Acoef_ne_zero j hj) (hCne j hj4), (hC j hj4).1,
      Acoef_natDegree j hj, hPzQdeg]
    split_ifs <;> omega
  have hTlc : ∀ j ∈ Finset.range 5, (Acoef j * dnum (Pz * Q) cub j).leadingCoeff
      = ((fallFact (((Pz * Q).natDegree : ℤ) - 3) j : ℤ) : ℂ) * (Afun j).leadingCoeff
        * (Pz * Q).leadingCoeff := by
    intro j hj
    have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hj; omega
    have hAf : (Afun j).leadingCoeff = (Acoef j).leadingCoeff * (144 : ℂ) ^ j := by
      rw [Afun_eq_Acoef_mul j hj, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow,
        cub_leadingCoeff]
    rw [Polynomial.leadingCoeff_mul, (hC j hj4).2, hAf]
    ring
  have hsum : (∑ j ∈ Finset.range 5, (Acoef j * dnum (Pz * Q) cub j).leadingCoeff)
      = (Pz * Q).leadingCoeff * (∑ j ∈ Finset.range 5,
          ((fallFact (((Pz * Q).natDegree : ℤ) - 3) j : ℤ) : ℂ) * (Afun j).leadingCoeff) := by
    rw [Finset.sum_congr rfl hTlc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    ring
  have hsig : (∑ j ∈ Finset.range 5,
      ((fallFact (((Pz * Q).natDegree : ℤ) - 3) j : ℤ) : ℂ) * (Afun j).leadingCoeff) ≠ 0 := by
    rw [sigma_infty_val]
    refine mul_ne_zero (pow_ne_zero 4 (by norm_num)) ?_
    exact_mod_cast (Commons.Analysis.Arithmetic.indicial_infty_ne_zero _ hN5)
  have hsumne : (∑ j ∈ Finset.range 5, (Acoef j * dnum (Pz * Q) cub j).leadingCoeff) ≠ 0 := by
    rw [hsum]
    exact mul_ne_zero (by rw [hPzQlc]; exact hQlc) hsig
  have hdegall : ∀ j ∈ Finset.range 5,
      (Acoef j * dnum (Pz * Q) cub j).degree = ((Q.natDegree + 25 : ℕ) : WithBot ℕ) := by
    intro j hj
    have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hj; omega
    rw [Polynomial.degree_eq_natDegree (mul_ne_zero (Acoef_ne_zero j hj) (hCne j hj4)),
      hTdeg j hj]
  have hPOLYlc : (POLYq Q).leadingCoeff
      = (Pz * Q).leadingCoeff * (∑ j ∈ Finset.range 5,
          ((fallFact (((Pz * Q).natDegree : ℤ) - 3) j : ℤ) : ℂ) * (Afun j).leadingCoeff) := by
    rw [POLYq]
    rw [Polynomial.leadingCoeff_sum_of_degree_eq hdegall hsumne]
    exact hsum
  have hPOLYne : POLYq Q ≠ 0 := by
    intro h
    have h1 : (POLYq Q).leadingCoeff = 0 := by rw [h]; simp
    rw [hPOLYlc] at h1
    exact mul_ne_zero (by rw [hPzQlc]; exact hQlc) hsig h1
  have hPOLYdeg_le : (POLYq Q).natDegree ≤ Q.natDegree + 25 := by
    rw [POLYq]
    exact Polynomial.natDegree_sum_le_of_forall_le (s := Finset.range 5)
      (f := fun j => Acoef j * dnum (Pz * Q) cub j) (fun j hj => le_of_eq (hTdeg j hj))
  have hcoeff_ne : (POLYq Q).coeff (Q.natDegree + 25) ≠ 0 := by
    rw [POLYq, Polynomial.finsetSum_coeff]
    have hstep : ∀ j ∈ Finset.range 5, (Acoef j * dnum (Pz * Q) cub j).coeff (Q.natDegree + 25)
        = (Acoef j * dnum (Pz * Q) cub j).leadingCoeff := by
      intro j hj
      rw [show Q.natDegree + 25 = (Acoef j * dnum (Pz * Q) cub j).natDegree from
        (hTdeg j hj).symm]
      rfl
    rw [Finset.sum_congr rfl hstep, hsum]
    exact mul_ne_zero (by rw [hPzQlc]; exact hQlc) hsig
  have hPOLYdeg : (POLYq Q).natDegree = Q.natDegree + 25 :=
    natDegree_eq_of_le_of_coeff_ne_zero hPOLYdeg_le hcoeff_ne
  have hpoly := POLYq_mul_X2 Q Rnum b3 hb3 hEq
  have hnd := congrArg Polynomial.natDegree hpoly
  have hLdeg : (POLYq Q * Polynomial.X ^ 2).natDegree = Q.natDegree + 27 := by
    rw [Polynomial.natDegree_mul hPOLYne (pow_ne_zero 2 Polynomial.X_ne_zero), hPOLYdeg,
      Polynomial.natDegree_pow, Polynomial.natDegree_X]
  have hRdeg' : (w ^ 4 * cub ^ 5 * Rnum).natDegree = 27 + Rnum.natDegree := by
    rw [Polynomial.natDegree_mul
        (mul_ne_zero (pow_ne_zero 4 w_ne_zero) (pow_ne_zero 5 cub_ne_zero)) hRnum,
      Polynomial.natDegree_mul (pow_ne_zero 4 w_ne_zero) (pow_ne_zero 5 cub_ne_zero),
      Polynomial.natDegree_pow, Polynomial.natDegree_pow, w_natDegree, cub_natDegree]
  rw [hLdeg, hRdeg'] at hnd
  omega

end FrobeniusApply
end Submission.CDT
