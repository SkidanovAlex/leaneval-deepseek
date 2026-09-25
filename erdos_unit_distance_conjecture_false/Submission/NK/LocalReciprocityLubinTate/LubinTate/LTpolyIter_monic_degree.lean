import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Division

/-!
# Shape of the iterates of the standard Lubin–Tate polynomial

For the standard Lubin–Tate polynomial `f(X) = πX + X^q` the `n`-fold iterate
`f^{(n)} = f ∘ ⋯ ∘ f` is a monic polynomial of degree `q ^ n` with linear coefficient `π ^ n` and
zero constant coefficient:

`f^{(n)}(T) = T^{q ^ n} + ⋯ + π ^ n T + 0`,

(Milne, *CFT*, §I.3: `f^{(n)}` is multiplication by `π ^ n` on the Lubin–Tate group).  This file
supplies the polynomial computation only; the coefficient-ring hypotheses of the Lubin–Tate
construction are irrelevant here.

The key point is that the `n`-th iterate is obtained from the `(n-1)`-st by composition with `f`,
and composition behaves well with respect to the three invariants (monicity/degree, first
coefficient, constant coefficient) for the *specific* `f` at hand: `f(0) = 0` makes the constant
coefficient stable, and `coeff f 1 = π` makes the linear coefficient multiply by `π`.
-/

namespace NK.LocalReciprocityLubinTate

universe u

open Polynomial

/-- The standard Lubin–Tate polynomial `πX + X^q` is monic of degree `q`, for `q ≥ 2`. -/
theorem isMonicOfDegree_LTpoly {A : Type u} [CommRing A] [Nontrivial A] {π : A} {q : ℕ}
    (hq : 2 ≤ q) : IsMonicOfDegree (LTpoly π q) q := by
  rw [isMonicOfDegree_iff]
  constructor
  · rw [LTpoly]
    calc (C π * X + X ^ q : A[X]).natDegree
        ≤ max (C π * X : A[X]).natDegree (X ^ q).natDegree := natDegree_add_le _ _
      _ ≤ max 1 q := by
            apply max_le_max
            · calc (C π * X : A[X]).natDegree ≤ X.natDegree := natDegree_C_mul_le π X
                _ = 1 := natDegree_X
            · rw [natDegree_X_pow]
      _ = q := max_eq_right (by omega)
  · rw [LTpoly, coeff_add]
    have h1 : (C π * X : A[X]).coeff q = 0 := by
      rw [C_mul_X_eq_monomial, coeff_monomial, if_neg (by omega : ¬ (1 = q))]
    rw [h1, coeff_X_pow_self, zero_add]

/-- The standard Lubin–Tate polynomial vanishes at `0` (for `q ≥ 1`). -/
theorem eval_zero_LTpoly {A : Type u} [CommRing A] {π : A} {q : ℕ} (hq : 1 ≤ q) :
    (LTpoly π q).eval 0 = 0 := by
  rw [LTpoly, eval_add, eval_mul, eval_pow, eval_C, eval_X, mul_zero, zero_add,
    zero_pow (show q ≠ 0 by omega)]

/-- The coefficient of `X` in the standard Lubin–Tate polynomial is `π`, for `q ≥ 2`. -/
theorem coeff_one_LTpoly {A : Type u} [CommRing A] {π : A} {q : ℕ} (hq : 2 ≤ q) :
    (LTpoly π q).coeff 1 = π := by
  rw [LTpoly, coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_X_pow,
    if_neg (by omega : ¬ (1 = q)), add_zero]

/-- The constant coefficient of a composition `p ∘ f` is the evaluation of `p` at the constant
coefficient of `f`. -/
theorem comp_coeff_zero {A : Type u} [CommRing A] (p f : A[X]) :
    (p.comp f).coeff 0 = p.eval (f.coeff 0) := by
  rw [coeff_zero_eq_eval_zero, eval_comp, ← coeff_zero_eq_eval_zero]

/-- If `f` has zero constant coefficient, then composition with `f` preserves the constant
coefficient. -/
theorem comp_coeff_zero_of_coeff_zero {A : Type u} [CommRing A] (p f : A[X])
    (hf : f.coeff 0 = 0) : (p.comp f).coeff 0 = p.coeff 0 := by
  rw [comp_coeff_zero, hf, ← coeff_zero_eq_eval_zero]

/-- The coefficient of `X` in a composition `p ∘ f`, for `f` with `f(0) = 0`, is the product of the
coefficients of `X` in `f` and in `p`.  This is the chain rule for the formal derivative, read off
in degree `0`. -/
theorem comp_coeff_one {A : Type u} [CommRing A] (p f : A[X]) (hf : f.eval 0 = 0) :
    (p.comp f).coeff 1 = f.coeff 1 * p.coeff 1 := by
  have hfd : (derivative f).coeff 0 = f.coeff 1 := by
    rw [coeff_derivative]; norm_num
  have hpd : ((derivative p).comp f).coeff 0 = p.coeff 1 := by
    rw [coeff_zero_eq_eval_zero, eval_comp, hf, ← coeff_zero_eq_eval_zero, coeff_derivative]
    norm_num
  calc (p.comp f).coeff 1
      = (derivative (p.comp f)).coeff 0 := by rw [coeff_derivative]; norm_num
    _ = (derivative f * (derivative p).comp f).coeff 0 := by rw [derivative_comp]
    _ = (derivative f).coeff 0 * ((derivative p).comp f).coeff 0 := mul_coeff_zero _ _
    _ = f.coeff 1 * p.coeff 1 := by rw [hfd, hpd]

end NK.LocalReciprocityLubinTate

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

open Polynomial

theorem LTpolyIter_monic_degree {A : Type u} [CommRing A] [Nontrivial A] (π : A) (q n : ℕ)
    (hq : 2 ≤ q) :
    (NK.LocalReciprocityLubinTate.LTpolyIter π q n).Monic ∧
      (NK.LocalReciprocityLubinTate.LTpolyIter π q n).natDegree = q ^ n ∧
      (NK.LocalReciprocityLubinTate.LTpolyIter π q n).coeff 1 = π ^ n ∧
      (NK.LocalReciprocityLubinTate.LTpolyIter π q n).coeff 0 = 0 := by
  have hM : IsMonicOfDegree (LTpoly π q) q := isMonicOfDegree_LTpoly hq
  have hev : (LTpoly π q).eval 0 = 0 := eval_zero_LTpoly (by omega)
  have hc1 : (LTpoly π q).coeff 1 = π := coeff_one_LTpoly hq
  have hc0 : (LTpoly π q).coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero, hev]
  have key : ∀ n : ℕ, (LTpolyIter π q n).Monic ∧
      (LTpolyIter π q n).natDegree = q ^ n ∧
      (LTpolyIter π q n).coeff 1 = π ^ n ∧
      (LTpolyIter π q n).coeff 0 = 0 := by
    intro n
    induction n with
    | zero =>
      rw [LTpolyIter_zero]
      exact ⟨monic_X, by rw [natDegree_X, pow_zero], by rw [coeff_X_one, pow_zero],
        by rw [coeff_X_zero]⟩
    | succ n ih =>
      obtain ⟨ihm, ihd, ihc1, ihc0⟩ := ih
      have hIh : IsMonicOfDegree (LTpolyIter π q n) (q ^ n) := ⟨ihd, ihm⟩
      have hstep : IsMonicOfDegree (LTpolyIter π q (n + 1)) (q ^ n * q) := by
        rw [LTpolyIter_succ]
        exact hIh.comp (by omega : q ≠ 0) hM
      refine ⟨hstep.monic, ?_, ?_, ?_⟩
      · rw [hstep.natDegree_eq, pow_succ]
      · rw [LTpolyIter_succ, comp_coeff_one _ _ hev, hc1, ihc1, ← pow_succ']
      · rw [LTpolyIter_succ, comp_coeff_zero_of_coeff_zero _ _ hc0, ihc0]
  exact key n

end NK.LocalReciprocityLubinTate.LubinTate
