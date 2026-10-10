import Mathlib
import Submission.Work.MotV5.WtDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted-size bound for the Klein polynomial

`Work.MotV5.Wt v g f` is the "sup of the weights of the monomials" of `f`, where the monomial
`c T^l` has weight `wt v g c l = (v g)^l * (v c)^5`.  The main result of this file is

  `Wt v g (kleinQPoly a b P) ≤ Wt v g P * Wt v g P`,

i.e. the Klein polynomial `-ab P(T)² + a² P(T+2)P(T+3) - b² P(T+1)P(T+4)` (a quadratic expression
in `P` whose coefficients `-ab`, `a²`, `b²` have value `1`) has weighted size at most the square
of the weighted size of `P`.  The proof is a coefficient-wise bookkeeping argument:

* `Wt` is the sup over the support of `l ↦ wt v g (f.coeff l) l`, so `Wt f ≤ M` is equivalent to
  the pointwise bound `∀ l, wt v g (f.coeff l) l ≤ M` (`WtKL_Wt_le_iff`);
* `wt` is subadditive in the coefficient and multiplicative under multiplication (`wt_mul`),
  which gives `Wt (f + h) ≤ Wt f ⊔ Wt h` and `Wt (f * h) ≤ Wt f * Wt h`;
* a scalar factor `C λ` contributes the factor `(v λ)^5`, which is `1` for `λ = -ab`, `a²`, `b²`
  by the hypotheses;
* substituting `T ↦ T + c` preserves `Wt` as long as `v c ≤ 1`: the coefficient of `T^L` in
  `f.comp (X + C c)` is `∑_e f_e · c^{e-L} · C(e,L)`, and both the binomial coefficient (a
  natural number, hence of value at most `1`) and the powers of `c` only decrease the weight,
  while `(v g)^L ≤ (v g)^e` because `1 < v g`.

The shifts occurring in `kleinQPoly` are `2, 3` and `1, 4`, all of which satisfy `v c ≤ 1`
automatically (`c` is a natural number).

Note: the hypothesis `v (a ^ 2 - a * b - b ^ 2) = 1` is not needed for this inequality; it enters
the complementary argument showing that the top weight in `kleinQPoly a b P` does not cancel.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.MotV5

open Polynomial

section Helpers

variable {F Γ₀ : Type*} [Field F] [CharP F 5] [LinearOrderedCommGroupWithZero Γ₀]

/-- `v` of a natural number is at most `1` (it is `1` unless the number is divisible by the
characteristic). -/
lemma WtKL_natCast_le_one (v : Valuation F Γ₀) (n : ℕ) : v ((n : F)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : ((n + 1 : ℕ) : F) = (n : F) + 1 := by push_cast; ring
    rw [hn]
    refine le_trans (v.map_add _ _) ?_
    exact max_le ih (by simp)

/-- The weight functional is subadditive in the coefficient. -/
lemma WtKL_wt_add (v : Valuation F Γ₀) (g : F) (x y : F) (l : ℕ) :
    wt v g (x + y) l ≤ wt v g x l ⊔ wt v g y l := by
  unfold wt
  rw [le_max_iff]
  rcases v.map_add' x y with h | h
  · left; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le h 5) zero_le
  · right; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le h 5) zero_le

/-- The weight functional is subadditive over a finite sum of coefficients. -/
lemma WtKL_wt_sum (v : Valuation F Γ₀) (g : F) {ι : Type*} (s : Finset ι) (x : ι → F)
    (l : ℕ) : wt v g (∑ i ∈ s, x i) l ≤ s.sup (fun i => wt v g (x i) l) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sup_empty, bot_eq_zero]
    simp [wt]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    exact le_trans (WtKL_wt_add v g _ _ _)
      (max_le (le_max_left _ _) (le_trans ih (le_max_right _ _)))

/-- A single coefficient of `p` has weight at most `Wt v g p`. -/
lemma WtKL_wt_coeff_le_Wt (v : Valuation F Γ₀) (g : F) (p : Polynomial F) (l : ℕ) :
    wt v g (p.coeff l) l ≤ Wt v g p := by
  by_cases hl : p.coeff l = 0
  · rw [wt_zero v g _ l hl]; exact zero_le
  · exact Finset.le_sup (f := fun l => wt v g (p.coeff l) l) (Polynomial.mem_support_iff.mpr hl)

/-- `Wt v g f ≤ M` is a pointwise condition on the coefficients. -/
lemma WtKL_Wt_le_iff (v : Valuation F Γ₀) (g : F) (f : Polynomial F) (M : Γ₀) :
    Wt v g f ≤ M ↔ ∀ l, wt v g (f.coeff l) l ≤ M := by
  constructor
  · intro h l
    by_cases hl : f.coeff l = 0
    · rw [wt_zero v g _ l hl]; exact zero_le
    · exact le_trans (Finset.le_sup (f := fun l => wt v g (f.coeff l) l)
        (Polynomial.mem_support_iff.mpr hl)) h
  · intro h
    exact Finset.sup_le (fun l _ => h l)

/-- `Wt` is subadditive. -/
lemma WtKL_Wt_add_le (v : Valuation F Γ₀) (g : F) (p q : Polynomial F) :
    Wt v g (p + q) ≤ Wt v g p ⊔ Wt v g q := by
  rw [WtKL_Wt_le_iff]
  intro L
  rw [Polynomial.coeff_add]
  exact le_trans (WtKL_wt_add v g _ _ L)
    (max_le (le_trans (WtKL_wt_coeff_le_Wt v g p L) (le_max_left _ _))
      (le_trans (WtKL_wt_coeff_le_Wt v g q L) (le_max_right _ _)))

/-- `Wt` does not increase under negation. -/
lemma WtKL_Wt_neg_le (v : Valuation F Γ₀) (g : F) (p : Polynomial F) :
    Wt v g (-p) ≤ Wt v g p := by
  rw [WtKL_Wt_le_iff]
  intro L
  rw [Polynomial.coeff_neg]
  simpa only [wt, Valuation.map_neg] using WtKL_wt_coeff_le_Wt v g p L

/-- `Wt` is subadditive for differences. -/
lemma WtKL_Wt_sub_le (v : Valuation F Γ₀) (g : F) (p q : Polynomial F) :
    Wt v g (p - q) ≤ Wt v g p ⊔ Wt v g q := by
  rw [sub_eq_add_neg]
  exact le_trans (WtKL_Wt_add_le v g p (-q)) (sup_le_sup_left (WtKL_Wt_neg_le v g q) _)

/-- `Wt` is submultiplicative. -/
lemma WtKL_Wt_mul_le (v : Valuation F Γ₀) (g : F) (p q : Polynomial F) :
    Wt v g (p * q) ≤ Wt v g p * Wt v g q := by
  rw [WtKL_Wt_le_iff]
  intro L
  rw [Polynomial.coeff_mul]
  refine le_trans (WtKL_wt_sum v g _ _ _) (Finset.sup_le ?_)
  intro x hx
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hx, wt_mul]
  exact mul_le_mul (WtKL_wt_coeff_le_Wt v g p x.1) (WtKL_wt_coeff_le_Wt v g q x.2)
    zero_le zero_le

/-- A scalar factor `C λ` scales `Wt` by the factor `(v λ)^5`. -/
lemma WtKL_Wt_C_mul_le (v : Valuation F Γ₀) (g : F) (lam : F) (f : Polynomial F) :
    Wt v g (C lam * f) ≤ (v lam) ^ 5 * Wt v g f := by
  rw [WtKL_Wt_le_iff]
  intro L
  rw [Polynomial.coeff_C_mul]
  have key : wt v g (lam * f.coeff L) L = (v lam) ^ 5 * wt v g (f.coeff L) L := by
    simp only [wt, map_mul, mul_pow, mul_left_comm, mul_comm]
  rw [key]
  exact mul_le_mul_of_nonneg_left (WtKL_wt_coeff_le_Wt v g f L) zero_le

/-- Substituting `T ↦ T + c` does not increase `Wt`, provided `v c ≤ 1`. -/
lemma WtKL_Wt_comp_X_add_C_le (v : Valuation F Γ₀) (g : F) (hg1 : 1 < v g) (c : F)
    (hc : v c ≤ 1) (f : Polynomial F) : Wt v g (f.comp (X + C c)) ≤ Wt v g f := by
  rw [WtKL_Wt_le_iff]
  intro L
  have hcoeff : (f.comp (X + C c)).coeff L
      = ∑ e ∈ f.support, f.coeff e * (c ^ (e - L) * ((e.choose L : ℕ) : F)) := by
    rw [Polynomial.comp_eq_sum_left, Polynomial.coeff_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  rw [hcoeff]
  refine le_trans (WtKL_wt_sum v g _ _ _) (Finset.sup_le ?_)
  intro e _
  by_cases hL : L ≤ e
  · have hvg : (v g) ^ L ≤ (v g) ^ e := pow_le_pow_right₀ (le_of_lt hg1) hL
    have hB : (v (c ^ (e - L) * ((e.choose L : ℕ) : F))) ^ 5 ≤ 1 := by
      have h1 : (v c) ^ (e - L) ≤ 1 := pow_le_one₀ zero_le hc
      have h2 : v (((e.choose L : ℕ) : F)) ≤ 1 := WtKL_natCast_le_one v _
      rw [map_mul, map_pow, mul_pow]
      exact le_trans (mul_le_mul (pow_le_one₀ zero_le h1) (pow_le_one₀ zero_le h2)
        zero_le zero_le) (by norm_num)
    calc wt v g (f.coeff e * (c ^ (e - L) * ((e.choose L : ℕ) : F))) L
        = (v g) ^ L * (v (f.coeff e)) ^ 5
            * (v (c ^ (e - L) * ((e.choose L : ℕ) : F))) ^ 5 := by
          simp only [wt, map_mul, mul_pow, mul_left_comm, mul_comm]
      _ ≤ (v g) ^ L * (v (f.coeff e)) ^ 5 * 1 :=
          mul_le_mul_of_nonneg_left hB zero_le
      _ = (v g) ^ L * (v (f.coeff e)) ^ 5 := mul_one _
      _ ≤ (v g) ^ e * (v (f.coeff e)) ^ 5 :=
          mul_le_mul_of_nonneg_right hvg zero_le
      _ = wt v g (f.coeff e) e := rfl
      _ ≤ Wt v g f := WtKL_wt_coeff_le_Wt v g f e
  · have hC : ((e.choose L : ℕ) : F) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hL), Nat.cast_zero]
    rw [hC, mul_zero, mul_zero, wt_zero v g 0 L rfl]
    exact zero_le

end Helpers

theorem Wt_kleinQPoly_le {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {g a b : F} (hg1 : 1 < v g)
    (ha : v a = 1) (hb : v b = 1) (hab : v (a ^ 2 - a * b - b ^ 2) = 1)
    (P : Polynomial F) :
    Wt v g (kleinQPoly a b P) ≤ Wt v g P * Wt v g P := by
  have hPP : (0 : Γ₀) ≤ Wt v g P := zero_le
  -- the scalar factors have fifth-power value `1`
  have hva : (v (-(a * b))) ^ 5 = 1 := by
    rw [Valuation.map_neg, map_mul, ha, hb]
    simp
  have ha2 : (v (a ^ 2)) ^ 5 = 1 := by
    rw [Valuation.map_pow, ha]
    simp
  have hb2 : (v (b ^ 2)) ^ 5 = 1 := by
    rw [Valuation.map_pow, hb]
    simp
  -- the three summands of the Klein polynomial
  have h1 : Wt v g (-C (a * b) * P ^ 2) ≤ Wt v g P * Wt v g P := by
    rw [← C_neg]
    refine le_trans (WtKL_Wt_C_mul_le v g _ _) ?_
    rw [hva, one_mul, pow_two]
    exact WtKL_Wt_mul_le v g P P
  have h2 : Wt v g (C (a ^ 2) * (P.comp (X + C 2)) * (P.comp (X + C 3)))
      ≤ Wt v g P * Wt v g P := by
    rw [mul_assoc]
    refine le_trans (WtKL_Wt_C_mul_le v g _ _) ?_
    rw [ha2, one_mul]
    refine le_trans (WtKL_Wt_mul_le v g _ _) ?_
    exact mul_le_mul
      (WtKL_Wt_comp_X_add_C_le v g hg1 2 (by simpa using WtKL_natCast_le_one v 2) P)
      (WtKL_Wt_comp_X_add_C_le v g hg1 3 (by simpa using WtKL_natCast_le_one v 3) P) zero_le hPP
  have h3 : Wt v g (C (b ^ 2) * (P.comp (X + C 1)) * (P.comp (X + C 4)))
      ≤ Wt v g P * Wt v g P := by
    rw [mul_assoc]
    refine le_trans (WtKL_Wt_C_mul_le v g _ _) ?_
    rw [hb2, one_mul]
    refine le_trans (WtKL_Wt_mul_le v g _ _) ?_
    exact mul_le_mul
      (WtKL_Wt_comp_X_add_C_le v g hg1 1 (by simpa using WtKL_natCast_le_one v 1) P)
      (WtKL_Wt_comp_X_add_C_le v g hg1 4 (by simpa using WtKL_natCast_le_one v 4) P) zero_le hPP
  unfold kleinQPoly
  refine le_trans (WtKL_Wt_sub_le v g
    (-C (a * b) * P ^ 2 + C (a ^ 2) * (P.comp (X + C 2)) * (P.comp (X + C 3)))
    (C (b ^ 2) * (P.comp (X + C 1)) * (P.comp (X + C 4)))) ?_
  refine max_le (le_trans (WtKL_Wt_add_le v g
    (-C (a * b) * P ^ 2) (C (a ^ 2) * (P.comp (X + C 2)) * (P.comp (X + C 3))))
    (max_le h1 h2)) h3

end Work.MotV5
