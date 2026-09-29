import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

/-!
# A derivation on `RatFunc K` extending the polynomial derivative

Given a field `K`, we build the standard derivation
`dR : K(X) → K(X)`, `(p/q)' = (p'q - pq')/q²`, on the rational function
field, and show that on the image of `K[X]` it agrees with the formal
derivative `Polynomial.derivative`.  Packaged as a `Differential (RatFunc K)`
this is the instance `Commons.FieldTheory.RatFunc.exists_differential_ratFunc`.

The construction descends the quotient-rule formula to `RatFunc K` through
`RatFunc.liftOn'`, using its invariance under scaling of a representative.
-/

noncomputable section

namespace Commons.FieldTheory.RatFunc

open Polynomial

variable {K : Type*} [Field K]

/-- The quotient-rule formula on representatives. -/
private def dF (p q : Polynomial K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (p.derivative * q - p * q.derivative)
    / (algebraMap (Polynomial K) (RatFunc K) q) ^ 2

private lemma dF_zero (p : Polynomial K) : dF p 0 = dF 0 (1 : Polynomial K) := by
  simp [dF]

private lemma dF_scale : ∀ {p q a : Polynomial K}, q ≠ 0 → a ≠ 0 → dF (a * p) (a * q) = dF p q := by
  intro p q a _hq ha
  have key : (a * p).derivative * (a * q) - (a * p) * (a * q).derivative
      = a ^ 2 * (p.derivative * q - p * q.derivative) := by
    simp only [Polynomial.derivative_mul]
    ring
  simp only [dF, key, map_mul, map_pow, mul_pow]
  have ha' : algebraMap (Polynomial K) (RatFunc K) a ≠ 0 := by simpa using ha
  field_simp

/-- **The derivative of a rational function**, `(p/q)' = (p'q - pq')/q²`. -/
private def dR (f : RatFunc K) : RatFunc K :=
  f.liftOn' dF dF_scale

private theorem dR_mk (p q : Polynomial K) : dR (RatFunc.mk p q) = dF p q := by
  unfold dR
  exact RatFunc.liftOn'_mk p q dF dF_zero dF_scale

/-- The concrete value of `dR` on a polynomial quotient. -/
private lemma dR_div (p q : Polynomial K) :
    dR (algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q)
      = algebraMap (Polynomial K) (RatFunc K) (p.derivative * q - p * q.derivative)
        / (algebraMap (Polynomial K) (RatFunc K) q) ^ 2 := by
  rw [← RatFunc.mk_eq_div, dR_mk]
  rfl

/-- `dR` extends the polynomial derivative. -/
@[simp] private lemma dR_algebraMap (p : Polynomial K) :
    dR (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative := by
  rw [← RatFunc.mk_one, dR_mk]
  simp [dF]

@[simp] private lemma dR_zero : dR (0 : RatFunc K) = 0 := by
  rw [show (0 : RatFunc K) = algebraMap (Polynomial K) (RatFunc K) 0 from (map_zero _).symm,
    dR_algebraMap]
  simp

@[simp] private lemma dR_one : dR (1 : RatFunc K) = 0 := by
  rw [show (1 : RatFunc K) = algebraMap (Polynomial K) (RatFunc K) 1 from (map_one _).symm,
    dR_algebraMap]
  simp

private lemma dR_C (c : K) : dR (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c)) = 0 := by
  rw [dR_algebraMap]
  simp

private lemma num_denom_eq (f : RatFunc K) :
    f = algebraMap (Polynomial K) (RatFunc K) f.num / algebraMap (Polynomial K) (RatFunc K) f.denom :=
  (RatFunc.num_div_denom f).symm

/-- `dR` in terms of the canonical `num`/`denom` representative. -/
private lemma dR_eq_dF (f : RatFunc K) : dR f = dF f.num f.denom := by
  conv_lhs => rw [num_denom_eq f]
  rw [← RatFunc.mk_eq_div]
  exact dR_mk _ _

/-- Additivity. -/
private lemma dR_add (f g : RatFunc K) : dR (f + g) = dR f + dR g := by
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
  rw [dR_div, dR_div, dR_div, hnum]
  field_simp [hAq, hAs]
  simp only [map_mul, map_pow, map_add, map_sub]
  ring

/-- The Leibniz rule. -/
private lemma dR_mul (f g : RatFunc K) : dR (f * g) = dR f * g + f * dR g := by
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
  rw [dR_div, dR_div, dR_div, hnum]
  field_simp [hAq, hAs]
  simp only [map_mul, map_pow, map_add, map_sub]
  ring

private lemma dR_neg (f : RatFunc K) : dR (-f) = -dR f := by
  have h : dR f + dR (-f) = 0 := by
    have hh := dR_add f (-f)
    rw [add_neg_cancel, dR_zero] at hh
    exact hh.symm
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h

private lemma dR_sub (f g : RatFunc K) : dR (f - g) = dR f - dR g := by
  rw [sub_eq_add_neg, dR_add, dR_neg, sub_eq_add_neg]

private lemma dR_pow (f : RatFunc K) (n : ℕ) : dR (f ^ n) = n * f ^ (n - 1) * dR f := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, dR_mul, ih, show k + 1 - 1 = k from by omega]
      by_cases hk : k = 0
      · subst hk; simp
      · have h2 : f ^ k = f ^ (k - 1) * f := by
          rw [← pow_succ f (k - 1), show k - 1 + 1 = k from by omega]
        rw [h2]
        push_cast
        ring

/-- Leibniz rule for multiplying by a polynomial. -/
private lemma dR_poly_mul (A : Polynomial K) (g : RatFunc K) :
    dR (algebraMap (Polynomial K) (RatFunc K) A * g)
      = algebraMap (Polynomial K) (RatFunc K) A.derivative * g
        + algebraMap (Polynomial K) (RatFunc K) A * dR g := by
  rw [dR_mul, dR_algebraMap]

/-- `dR` as an additive homomorphism. -/
private def dRAddHom : RatFunc K →+ RatFunc K where
  toFun := dR
  map_zero' := dR_zero
  map_add' := dR_add

/-- `dR` as a `ℤ`-linear map. -/
private def dRLin : RatFunc K →ₗ[ℤ] RatFunc K := dRAddHom.toIntLinearMap

@[simp] private lemma dRLin_apply (x : RatFunc K) : dRLin x = dR x := rfl

/-- `dR` vanishes on the integers. -/
private lemma dR_natCast (n : ℕ) : dR (n : RatFunc K) = 0 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, dR_add, ih, dR_one, add_zero]

private lemma dR_intCast (c : ℤ) : dR (c : RatFunc K) = 0 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · simpa using dR_natCast n
  · rw [Int.cast_neg, dR_neg, Int.cast_natCast, dR_natCast n, neg_zero]

end Commons.FieldTheory.RatFunc

namespace Commons.FieldTheory.RatFunc

theorem exists_differential_ratFunc {K : Type*} [Field K] :
    ∃ d : Differential (RatFunc K), ∀ p : Polynomial K,
      d.deriv (algebraMap (Polynomial K) (RatFunc K) p)
        = algebraMap (Polynomial K) (RatFunc K) p.derivative := by
  letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra (RatFunc K)
  refine ⟨⟨?_⟩, ?_⟩
  · refine { toLinearMap := dRLin, map_one_eq_zero' := dR_one, leibniz' := ?_ }
    intro a b
    rw [dRLin_apply, dRLin_apply, dRLin_apply, dR_mul]
    show dR a * b + a * dR b = a • dR b + b • dR a
    simp only [smul_eq_mul]
    ring
  · intro p
    exact dR_algebraMap p

end Commons.FieldTheory.RatFunc