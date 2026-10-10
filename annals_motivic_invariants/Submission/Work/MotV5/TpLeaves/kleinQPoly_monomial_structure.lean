import Mathlib
import Submission.Work.MotV5.WtDefs
import Submission.Work.MotV5.Wt_kleinQPoly_le
import Submission.Work.MotV5.coeff_kleinQPoly_top
import Submission.Work.MotV5.natDegree_kleinQPoly_le
import Submission.Work.MotV5.topPart_asPolyF_mul_gen
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted monomial structure of the Klein polynomial of a monomial

For `P = C u * X ^ n` with `n ≤ 4`, the Klein polynomial
`kleinQPoly a b P = -ab P(T)² + a² P(T+2)P(T+3) - b² P(T+1)P(T+4)` (see
`Submission/Work/MotV5/WtDefs.lean`) has the following weighted structure with respect to
`wt v g c l = (v g)^l * (v c)^5`:

* the coefficient of `T^m` has weight at most `(wt v g u n)²`;
* for `m ≠ 2n` the inequality is strict;
* the coefficient of `T^{2n}` has weight exactly `(wt v g u n)²`.

The proof combines three ingredients:

* the general bound `Wt v g (kleinQPoly a b P) ≤ (Wt v g P)²` of
  `Submission/Work/MotV5/Wt_kleinQPoly_le.lean` together with the computation
  `Wt v g (C u * X^n) = wt v g u n` (the first conjunct);
* the pointwise value bound `v ((kleinQPoly a b (C u * X^n)).coeff m) ≤ (v u)²`, obtained from
  the crude ultrametric estimate on the three summands, together with monotonicity of
  exponents for `m < 2n`, and `natDegree_kleinQPoly_le` for `m > 2n`;
* the exact top coefficient `coeff_kleinQPoly_top` at `m = 2n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.MotV5.TpLeaves

open Polynomial

/-! ## Value bounds for the coefficients -/

/-- The coefficients of `(X + C c)^n` have value at most `1`, provided `v c ≤ 1`. -/
lemma val_coeff_X_add_C_pow_le {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {c : F} (hc : v c ≤ 1) (n k : ℕ) :
    v (((X + C c) ^ n).coeff k) ≤ 1 := by
  rw [Polynomial.coeff_X_add_C_pow, Valuation.map_mul, Valuation.map_pow]
  refine le_trans (mul_le_mul_of_nonneg_right (pow_le_one₀ zero_le hc) zero_le) ?_
  rw [one_mul]
  exact WtKL_natCast_le_one v _

/-- The coefficients of `(X + C c)^n * (X + C d)^n` have value at most `1`, provided
`v c ≤ 1` and `v d ≤ 1`. -/
lemma val_coeff_mul_pow_le {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {c d : F} (hc : v c ≤ 1)
    (hd : v d ≤ 1) (n m : ℕ) : v (((X + C c) ^ n * (X + C d) ^ n).coeff m) ≤ 1 := by
  rw [Polynomial.coeff_mul]
  refine Valuation.map_sum_le v (fun x _ => ?_)
  rw [Valuation.map_mul]
  refine le_trans (mul_le_mul_of_nonneg_right (val_coeff_X_add_C_pow_le v hc n x.1) zero_le) ?_
  rw [one_mul]
  exact val_coeff_X_add_C_pow_le v hd n x.2

/-- The coefficients of `(C u * X^n).comp (X + C c) * (C u * X^n).comp (X + C d)` have value
at most `(v u)²`, provided `v c ≤ 1` and `v d ≤ 1`. -/
lemma val_comp_prod_le {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {u c d : F}
    (hc : v c ≤ 1) (hd : v d ≤ 1) (n m : ℕ) :
    v (((C u * X ^ n).comp (X + C c) * (C u * X ^ n).comp (X + C d)).coeff m)
      ≤ (v u) ^ 2 := by
  have hc' : (C u * X ^ n : Polynomial F).comp (X + C c) = C u * (X + C c) ^ n := by
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp]
  have hd' : (C u * X ^ n : Polynomial F).comp (X + C d) = C u * (X + C d) ^ n := by
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp]
  rw [hc', hd']
  have hprod : C u * (X + C c) ^ n * (C u * (X + C d) ^ n)
      = C (u ^ 2) * ((X + C c) ^ n * (X + C d) ^ n) := by
    have h : C u * (X + C c) ^ n * (C u * (X + C d) ^ n)
        = (C u * C u) * ((X + C c) ^ n * (X + C d) ^ n) := by ring
    rw [h, ← Polynomial.C_mul, ← sq]
  rw [hprod, Polynomial.coeff_C_mul, Valuation.map_mul, Valuation.map_pow]
  refine le_trans (mul_le_mul_of_nonneg_left (val_coeff_mul_pow_le v hc hd n m) zero_le) ?_
  rw [mul_one]

/-- Every coefficient of `kleinQPoly a b (C u * X^n)` has value at most `(v u)²`. -/
lemma val_kleinQPoly_monomial_le {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {a b u : F}
    (ha : v a = 1) (hb : v b = 1) (n m : ℕ) :
    v ((kleinQPoly a b (C u * X ^ n)).coeff m) ≤ (v u) ^ 2 := by
  have hK : kleinQPoly a b (C u * X ^ n)
      = C (-(a * b)) * (C u * X ^ n) ^ 2
        + C (a ^ 2) * ((C u * X ^ n).comp (X + C 2) * (C u * X ^ n).comp (X + C 3))
        - C (b ^ 2) * ((C u * X ^ n).comp (X + C 1) * (C u * X ^ n).comp (X + C 4)) := by
    simp only [kleinQPoly, C_neg]
    first | refl_ring1 | ring
  have hsq : v (((C u * X ^ n) ^ 2).coeff m) ≤ (v u) ^ 2 := by
    have hsq' : (C u * X ^ n : Polynomial F) ^ 2 = C (u ^ 2) * X ^ (2 * n) := by
      have h1 : (C u * X ^ n : Polynomial F) ^ 2 = (C u * C u) * (X ^ n * X ^ n) := by ring
      rw [h1, ← Polynomial.C_mul, ← pow_add, ← sq, show n + n = 2 * n from by ring]
    rw [hsq', Polynomial.coeff_C_mul]
    by_cases hm : m = 2 * n
    · rw [Polynomial.coeff_X_pow, ite_eq_left hm, mul_one, Valuation.map_pow]
    · rw [Polynomial.coeff_X_pow, ite_eq_right hm, mul_zero, Valuation.map_zero]
      exact zero_le
  have hA : v ((C (-(a * b)) * (C u * X ^ n) ^ 2).coeff m) ≤ (v u) ^ 2 := by
    rw [Polynomial.coeff_C_mul, Valuation.map_mul]
    have h1 : v (-(a * b)) = 1 := by rw [Valuation.map_neg, Valuation.map_mul, ha, hb, mul_one]
    rw [h1, one_mul]
    exact hsq
  have hvc2 : v (2 : F) ≤ 1 := by simpa using WtKL_natCast_le_one v 2
  have hvc3 : v (3 : F) ≤ 1 := by simpa using WtKL_natCast_le_one v 3
  have hvc1 : v (1 : F) ≤ 1 := by simpa using WtKL_natCast_le_one v 1
  have hvc4 : v (4 : F) ≤ 1 := by simpa using WtKL_natCast_le_one v 4
  have hB : v ((C (a ^ 2) * ((C u * X ^ n).comp (X + C 2)
      * (C u * X ^ n).comp (X + C 3))).coeff m) ≤ (v u) ^ 2 := by
    rw [Polynomial.coeff_C_mul, Valuation.map_mul]
    have h2' : v (a ^ 2) = 1 := by rw [Valuation.map_pow, ha, one_pow]
    rw [h2', one_mul]
    exact val_comp_prod_le v hvc2 hvc3 n m
  have hC : v ((C (b ^ 2) * ((C u * X ^ n).comp (X + C 1)
      * (C u * X ^ n).comp (X + C 4))).coeff m) ≤ (v u) ^ 2 := by
    rw [Polynomial.coeff_C_mul, Valuation.map_mul]
    have hb2 : v (b ^ 2) = 1 := by rw [Valuation.map_pow, hb, one_pow]
    rw [hb2, one_mul]
    exact val_comp_prod_le v hvc1 hvc4 n m
  rw [hK, Polynomial.coeff_sub, Polynomial.coeff_add]
  exact Valuation.map_sub_le v (Valuation.map_add_le v hA hB) hC

/-- `Wt` of the monomial `C u * X^n` is `wt v g u n`. -/
lemma WtKL_C_mul_X_pow {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (g : F) (u : F) (n : ℕ) :
    Wt v g (C u * X ^ n) = wt v g u n := by
  refine le_antisymm ?_ ?_
  · rw [WtKL_Wt_le_iff]
    intro m
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : m = n
    · rw [ite_eq_left h, mul_one, h]
    · rw [ite_eq_right h, mul_zero, wt_zero v g 0 m rfl]
      exact zero_le
  · have hcoeff : (C u * X ^ n).coeff n = u := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]
    calc wt v g u n = wt v g ((C u * X ^ n).coeff n) n := by rw [hcoeff]
      _ ≤ Wt v g (C u * X ^ n) := WtKL_wt_coeff_le_Wt v g (C u * X ^ n) n

/-! ## The main statement -/

theorem kleinQPoly_monomial_structure {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {g a b u : F} (hg1 : 1 < v g)
    (ha : v a = 1) (hb : v b = 1) (hab : v (a ^ 2 - a * b - b ^ 2) = 1)
    {n : ℕ} (hn : n ≤ 4) (hu : v u ≠ 0) :
    (∀ m : ℕ, Work.MotV5.wt v g
        ((Work.MotV5.kleinQPoly a b (Polynomial.C u * Polynomial.X ^ n)).coeff m) m
        ≤ (Work.MotV5.wt v g u n) ^ 2)
    ∧ (∀ m : ℕ, m ≠ 2 * n → Work.MotV5.wt v g
        ((Work.MotV5.kleinQPoly a b (Polynomial.C u * Polynomial.X ^ n)).coeff m) m
          < (Work.MotV5.wt v g u n) ^ 2)
    ∧ Work.MotV5.wt v g
        ((Work.MotV5.kleinQPoly a b (Polynomial.C u * Polynomial.X ^ n)).coeff (2 * n)) (2 * n)
        = (Work.MotV5.wt v g u n) ^ 2 := by
  have hu0 : u ≠ 0 := fun h => hu (by rw [h]; simp)
  have hvg : 0 < v g := lt_trans zero_lt_one hg1
  have hvu : 0 < v u := zero_lt_iff.mpr hu
  have hMpos : 0 < (Work.MotV5.wt v g u n) ^ 2 :=
    pow_pos (by rw [Work.MotV5.wt]; exact mul_pos (pow_pos hvg n) (pow_pos hvu 5)) 2
  have hwt_sq : (Work.MotV5.wt v g u n) ^ 2 = (v g) ^ (2 * n) * ((v u) ^ 2) ^ 5 := by
    rw [Work.MotV5.wt, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
      show n * 2 = 2 * n from by ring, show 5 * 2 = 2 * 5 from by norm_num]
  have hP : (C u * X ^ n : Polynomial F) ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hu0) (pow_ne_zero n Polynomial.X_ne_zero)
  have hPdeg : (C u * X ^ n : Polynomial F).natDegree = n :=
    Polynomial.natDegree_C_mul_X_pow n u hu0
  refine ⟨?_, ?_, ?_⟩
  · intro m
    refine le_trans (WtKL_wt_coeff_le_Wt v g (kleinQPoly a b (C u * X ^ n)) m) ?_
    calc Work.MotV5.Wt v g (Work.MotV5.kleinQPoly a b (C u * X ^ n))
        ≤ Work.MotV5.Wt v g (C u * X ^ n) * Work.MotV5.Wt v g (C u * X ^ n) :=
          Work.MotV5.Wt_kleinQPoly_le v hg1 ha hb hab _
      _ = (Work.MotV5.wt v g u n) ^ 2 := by rw [WtKL_C_mul_X_pow, pow_two]
  · intro m hm
    rcases lt_trichotomy m (2 * n) with h | h | h
    · have hv := val_kleinQPoly_monomial_le (u := u) v ha hb n m
      calc Work.MotV5.wt v g ((Work.MotV5.kleinQPoly a b (C u * X ^ n)).coeff m) m
          = (v g) ^ m * (v ((Work.MotV5.kleinQPoly a b (C u * X ^ n)).coeff m)) ^ 5 := rfl
        _ ≤ (v g) ^ m * ((v u) ^ 2) ^ 5 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le hv 5) zero_le
        _ < (v g) ^ (2 * n) * ((v u) ^ 2) ^ 5 :=
            mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hg1 h) (pow_pos (pow_pos hvu 2) 5)
        _ = (Work.MotV5.wt v g u n) ^ 2 := hwt_sq.symm
    · exact absurd h hm
    · have hdeg : (Work.MotV5.kleinQPoly a b (C u * X ^ n)).natDegree ≤ 2 * n := by
        refine le_trans (Work.MotV5.natDegree_kleinQPoly_le a b _) ?_
        rw [hPdeg]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (show (Work.MotV5.kleinQPoly a b (C u * X ^ n)).natDegree < m from by omega),
        Work.MotV5.wt_zero v g 0 m rfl]
      exact hMpos
  · have htop := Work.MotV5.coeff_kleinQPoly_top a b hP (by rw [hPdeg]; exact hn)
    rw [hPdeg] at htop
    have hcoeff : (C u * X ^ n : Polynomial F).coeff n = u := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]
    rw [hcoeff] at htop
    have hvtop : v ((a ^ 2 - a * b - b ^ 2) * u ^ 2) = (v u) ^ 2 := by
      rw [Valuation.map_mul, Valuation.map_pow, hab, one_mul]
    rw [htop, Work.MotV5.wt, hvtop]
    exact hwt_sq.symm

end Work.MotV5.TpLeaves
