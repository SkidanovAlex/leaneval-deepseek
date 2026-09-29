import Mathlib
import Submission.CDT.RatFuncOrder

set_option linter.unusedSimpArgs false

/-!
# The derivative of a rational function

`dRat f` is the derivative of `f ∈ K(X)`, given on a representative `p/q` by
the quotient rule `(p'q - pq')/q²`.  Scaling invariance of that formula
(`dRatF_scale`) shows that it descends to `RatFunc K`.

API: `dRat_mk` / `dRat_div` (the value on a representative), `dRat_algebraMap`
(agreement with the polynomial derivative), additivity `dRat_add`, the Leibniz
rule `dRat_mul`, and the derived rules `dRat_neg`, `dRat_sub`, `dRat_pow`,
`dRat_poly_mul`, `dRat_pow_X_sub_C_mul`.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K]

/-- The quotient-rule formula on representatives. -/
def dRatF (p q : Polynomial K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (p.derivative * q - p * q.derivative)
    / (algebraMap (Polynomial K) (RatFunc K) q) ^ 2

lemma dRatF_zero (p : Polynomial K) : dRatF p 0 = dRatF 0 (1 : Polynomial K) := by
  simp [dRatF]

lemma dRatF_scale : ∀ {p q a : Polynomial K}, q ≠ 0 → a ≠ 0 →
    dRatF (a * p) (a * q) = dRatF p q := by
  intro p q a _hq ha
  have key : (a * p).derivative * (a * q) - (a * p) * (a * q).derivative
      = a ^ 2 * (p.derivative * q - p * q.derivative) := by
    simp only [Polynomial.derivative_mul]
    ring
  simp only [dRatF, key, map_mul, map_pow, mul_pow]
  have ha' : algebraMap (Polynomial K) (RatFunc K) a ≠ 0 := by simpa using ha
  field_simp

/-- **The derivative of a rational function**, `(p/q)' = (p'q - pq')/q²`. -/
def dRat (f : RatFunc K) : RatFunc K :=
  f.liftOn' dRatF dRatF_scale

theorem dRat_mk (p q : Polynomial K) : dRat (RatFunc.mk p q) = dRatF p q := by
  unfold dRat
  exact RatFunc.liftOn'_mk p q dRatF dRatF_zero dRatF_scale

/-- The concrete value of `dRat` on a polynomial quotient. -/
lemma dRat_div (p q : Polynomial K) :
    dRat (algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q)
      = algebraMap (Polynomial K) (RatFunc K) (p.derivative * q - p * q.derivative)
        / (algebraMap (Polynomial K) (RatFunc K) q) ^ 2 := by
  rw [← RatFunc.mk_eq_div, dRat_mk]
  rfl

/-- `dRat` extends the polynomial derivative. -/
@[simp] lemma dRat_algebraMap (p : Polynomial K) :
    dRat (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative := by
  rw [← RatFunc.mk_one, dRat_mk]
  simp [dRatF]

@[simp] lemma dRat_zero : dRat (0 : RatFunc K) = 0 := by
  rw [show (0 : RatFunc K) = algebraMap (Polynomial K) (RatFunc K) 0 from (map_zero _).symm,
    dRat_algebraMap]
  simp

@[simp] lemma dRat_one : dRat (1 : RatFunc K) = 0 := by
  rw [show (1 : RatFunc K) = algebraMap (Polynomial K) (RatFunc K) 1 from (map_one _).symm,
    dRat_algebraMap]
  simp

lemma dRat_C (c : K) : dRat (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c)) = 0 := by
  rw [dRat_algebraMap]
  simp

lemma num_denom_eq (f : RatFunc K) :
    f = algebraMap (Polynomial K) (RatFunc K) f.num / algebraMap (Polynomial K) (RatFunc K) f.denom :=
  (RatFunc.num_div_denom f).symm

/-- `dRat` in terms of the canonical `num`/`denom` representative. -/
lemma dRat_eq_dRatF (f : RatFunc K) : dRat f = dRatF f.num f.denom := by
  conv_lhs => rw [num_denom_eq f]
  rw [← RatFunc.mk_eq_div]
  exact dRat_mk _ _

/-- Additivity. -/
lemma dRat_add (f g : RatFunc K) : dRat (f + g) = dRat f + dRat g := by
  have hAq : algebraMap (Polynomial K) (RatFunc K) f.denom ≠ 0 := by
    simpa using RatFunc.denom_ne_zero f
  have hAs : algebraMap (Polynomial K) (RatFunc K) g.denom ≠ 0 := by
    simpa using RatFunc.denom_ne_zero g
  have hnum : (f.num * g.denom + g.num * f.denom).derivative * (f.denom * g.denom)
      - (f.num * g.denom + g.num * f.denom) * (f.denom * g.denom).derivative
      = (f.num.derivative * f.denom - f.num * f.denom.derivative) * g.denom ^ 2
        + (g.num.derivative * g.denom - g.num * g.denom.derivative) * f.denom ^ 2 := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add]
    ring
  have hdiv : (algebraMap (Polynomial K) (RatFunc K) f.num / algebraMap (Polynomial K) (RatFunc K) f.denom
        + algebraMap (Polynomial K) (RatFunc K) g.num / algebraMap (Polynomial K) (RatFunc K) g.denom)
      = algebraMap (Polynomial K) (RatFunc K) (f.num * g.denom + g.num * f.denom)
        / algebraMap (Polynomial K) (RatFunc K) (f.denom * g.denom) := by
    rw [div_add_div _ _ (by simpa using RatFunc.denom_ne_zero f)
        (by simpa using RatFunc.denom_ne_zero g)]
    simp only [map_add, map_mul]
    ring
  conv_rhs => rw [num_denom_eq f, num_denom_eq g]
  conv_lhs => rw [num_denom_eq f, num_denom_eq g, hdiv]
  rw [dRat_div, dRat_div, dRat_div, hnum]
  field_simp [hAq, hAs]
  simp only [map_mul, map_pow, map_add, map_sub]
  ring

/-- The Leibniz rule. -/
lemma dRat_mul (f g : RatFunc K) : dRat (f * g) = dRat f * g + f * dRat g := by
  have hAq : algebraMap (Polynomial K) (RatFunc K) f.denom ≠ 0 := by
    simpa using RatFunc.denom_ne_zero f
  have hAs : algebraMap (Polynomial K) (RatFunc K) g.denom ≠ 0 := by
    simpa using RatFunc.denom_ne_zero g
  have hnum : (f.num * g.num).derivative * (f.denom * g.denom)
      - (f.num * g.num) * (f.denom * g.denom).derivative
      = (f.num.derivative * f.denom - f.num * f.denom.derivative) * g.num * g.denom
        + (g.num.derivative * g.denom - g.num * g.denom.derivative) * f.num * f.denom := by
    simp only [Polynomial.derivative_mul]
    ring
  have hmul : (algebraMap (Polynomial K) (RatFunc K) f.num / algebraMap (Polynomial K) (RatFunc K) f.denom)
        * (algebraMap (Polynomial K) (RatFunc K) g.num / algebraMap (Polynomial K) (RatFunc K) g.denom)
      = algebraMap (Polynomial K) (RatFunc K) (f.num * g.num)
        / algebraMap (Polynomial K) (RatFunc K) (f.denom * g.denom) := by
    rw [div_mul_div_comm]
    simp only [map_mul]
  conv_rhs => rw [num_denom_eq f, num_denom_eq g]
  conv_lhs => rw [num_denom_eq f, num_denom_eq g, hmul]
  rw [dRat_div, dRat_div, dRat_div, hnum]
  field_simp [hAq, hAs]
  simp only [map_mul, map_pow, map_add, map_sub]
  ring

lemma dRat_neg (f : RatFunc K) : dRat (-f) = -dRat f := by
  have h : dRat f + dRat (-f) = 0 := by
    have hh := dRat_add f (-f)
    rw [add_neg_cancel, dRat_zero] at hh
    exact hh.symm
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h

lemma dRat_sub (f g : RatFunc K) : dRat (f - g) = dRat f - dRat g := by
  rw [sub_eq_add_neg, dRat_add, dRat_neg, sub_eq_add_neg]

lemma dRat_pow (f : RatFunc K) (n : ℕ) : dRat (f ^ n) = n * f ^ (n - 1) * dRat f := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, dRat_mul, ih, show k + 1 - 1 = k from by omega]
      by_cases hk : k = 0
      · subst hk; simp
      · have h2 : f ^ k = f ^ (k - 1) * f := by
          rw [← pow_succ f (k - 1), show k - 1 + 1 = k from by omega]
        rw [h2]
        push_cast
        ring

/-- Leibniz rule for multiplying by a polynomial. -/
lemma dRat_poly_mul (A : Polynomial K) (g : RatFunc K) :
    dRat (algebraMap (Polynomial K) (RatFunc K) A * g)
      = algebraMap (Polynomial K) (RatFunc K) A.derivative * g
        + algebraMap (Polynomial K) (RatFunc K) A * dRat g := by
  rw [dRat_mul, dRat_algebraMap]

end Submission.CDT
