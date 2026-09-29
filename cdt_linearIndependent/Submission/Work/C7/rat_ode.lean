import Mathlib
import Submission.CDT.Residue
import Submission.Work.C7.simple_pole_ode

/-!
# `Work.C7.rat_ode` — rational-function ODEs at the branch point `X = 1`

Three statements about the derivation `dRat` on `ℚ(X)` (`Submission.CDT.dRat`,
`Submission/CDT/RatFuncDeriv.lean`), all of them about the fact that `√(X-1)` is not a rational
function:

* `dRat ε = ε / (2*(X-1))` and `dRat ε = -ε / (2*(X-1))` have no nonzero solution `ε ∈ ℚ(X)`
  (the solutions would be `const·√(X-1)` and `const·(X-1)^{-1/2}`);
* the inhomogeneous equation `dRat b = b / (2*(X-1)) + 1/X` has no solution at all.

**Homogeneous cases (residues).** For `f ≠ 0` the logarithmic derivative `(dRat f)/f` has residue
`ordAt α f ∈ ℤ` at every point `α` (`Submission.CDT.residueAt_dRat_div_self`,
`logDeriv_eq_polePart_imp` below).  Dividing the equation by `f` exhibits `(dRat f)/f` as the
elementary simple pole `(1/2)/(X-1)` (resp. `(-1/2)/(X-1)`) of residue `1/2` (resp. `-1/2`)
(`Submission.CDT.residueAt_polePart`).  Uniqueness of the residue (`Submission.CDT.ResidueAt.unique`)
then forces the *integer* `ordAt 1 f` to equal the non-integer `±1/2`, a contradiction.

**Inhomogeneous case (order of vanishing).** At `α = 0` the two summands have orders
`ordAt 0 b` and `-1`; since `dRat b` never has a simple pole and `ordAt 0 (dRat b) = ordAt 0 b - 1`
whenever `ordAt 0 b ≠ 0`, the orders of the two sides of the equation can never agree
(`Work.C7.simple_pole_ode`, at the origin).
-/

open Polynomial
open Submission.CDT

namespace Work.C7

/-- `X - 1` as an element of `ℚ(X)`, in the `Polynomial`-`algebraMap` normal form. -/
lemma ode_X_sub_one_eq : ((RatFunc.X : RatFunc ℚ) - 1)
    = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - Polynomial.C 1) := by
  rw [Polynomial.C_1, map_sub, RatFunc.algebraMap_X, map_one]

lemma ode_X_sub_one_ne_zero : ((RatFunc.X : RatFunc ℚ) - 1) ≠ 0 := by
  rw [ode_X_sub_one_eq]
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1)

lemma ode_ordAt_zero_X : ordAt (0 : ℚ) (RatFunc.X : RatFunc ℚ) = 1 := by
  rw [← RatFunc.algebraMap_X, ordAt_algebraMap]
  have h := Polynomial.rootMultiplicity_X_sub_C_self (x := (0 : ℚ))
  rw [Polynomial.C_0, sub_zero] at h
  rw [h]
  norm_num

lemma ode_ordAt_zero_X_sub_one : ordAt (0 : ℚ) ((RatFunc.X : RatFunc ℚ) - 1) = 0 := by
  rw [ode_X_sub_one_eq, ordAt_algebraMap, Polynomial.rootMultiplicity_X_sub_C]
  norm_num

lemma ode_two_mul_X_sub_one_ne_zero : (2 * ((RatFunc.X : RatFunc ℚ) - 1)) ≠ 0 := by
  have h2 : (2 : RatFunc ℚ) = RatFunc.C (2 : ℚ) := by norm_num
  rw [h2]
  exact mul_ne_zero (by rw [← h2]; norm_num) ode_X_sub_one_ne_zero

lemma ode_ordAt_zero_two : ordAt (0 : ℚ) (2 * ((RatFunc.X : RatFunc ℚ) - 1)) = 0 := by
  have h2 : (2 : RatFunc ℚ) = RatFunc.C (2 : ℚ) := by norm_num
  rw [h2, ordAt_mul (0 : ℚ) (by rw [← h2]; norm_num) ode_X_sub_one_ne_zero,
    show ordAt (0 : ℚ) (RatFunc.C (2 : ℚ)) = 0 from ordAt_const (0 : ℚ) 2,
    ode_ordAt_zero_X_sub_one, add_zero]

lemma ode_ordAt_zero_inv_X : ordAt (0 : ℚ) ((RatFunc.X : RatFunc ℚ)⁻¹) = -1 := by
  rw [ordAt_inv (0 : ℚ) RatFunc.X_ne_zero, ode_ordAt_zero_X]

lemma ode_ordAt_zero_one_div_X : ordAt (0 : ℚ) ((1 : RatFunc ℚ) / RatFunc.X) = -1 := by
  rw [div_eq_mul_inv, one_mul, ode_ordAt_zero_inv_X]

lemma ode_one_div_X_ne_zero : ((1 : RatFunc ℚ) / RatFunc.X) ≠ 0 :=
  div_ne_zero one_ne_zero RatFunc.X_ne_zero

lemma ode_lin_one : lin (1 : ℚ) = ((RatFunc.X : RatFunc ℚ) - 1) := by
  rw [lin]
  exact ode_X_sub_one_eq.symm

/-- The elementary simple pole `c/(X-1)`, in the shape used by the residue calculus. -/
lemma ode_polePart_one_eq (c : ℚ) : polePart (1 : ℚ) c
    = RatFunc.C c / ((RatFunc.X : RatFunc ℚ) - 1) := by
  rw [polePart_eq, ode_lin_one]
  rfl

lemma ode_two_mul_C_half : (2 : RatFunc ℚ) * RatFunc.C (1 / 2 : ℚ) = 1 := by
  rw [show (2 : RatFunc ℚ) = RatFunc.C (2 : ℚ) from by norm_num, ← map_mul]
  norm_num

lemma ode_two_mul_C_neg_half : (2 : RatFunc ℚ) * RatFunc.C (-(1 / 2) : ℚ) = -1 := by
  rw [show (2 : RatFunc ℚ) = RatFunc.C (2 : ℚ) from by norm_num, ← map_mul]
  norm_num

lemma ode_not_int_half (z : ℤ) : (z : ℚ) ≠ 1 / 2 := by
  intro hz
  have h2 : (2 * z : ℤ) = 1 := by
    exact_mod_cast (show (2 : ℚ) * (z : ℚ) = 1 by linarith)
  omega

lemma ode_not_int_neg_half (z : ℤ) : (z : ℚ) ≠ -(1 / 2) := by
  intro hz
  have h2 : (2 * z : ℤ) = -1 := by
    exact_mod_cast (show (2 : ℚ) * (z : ℚ) = -1 by linarith)
  omega

/-- **The residue of a logarithmic derivative is the order of vanishing.**  If `(dRat f)/f`
coincides with the elementary simple pole `c/(X - α)` then `c` is the *integer* `ordAt α f`.
Uniqueness of the residue (`Submission.CDT.ResidueAt.unique`) applied to
`Submission.CDT.residueAt_dRat_div_self` and `Submission.CDT.residueAt_polePart`. -/
theorem logDeriv_eq_polePart_imp {K : Type*} [Field K] [CharZero K] {f : RatFunc K} (hf : f ≠ 0)
    {α c : K} (h : dRat f / f = polePart α c) : c = ((ordAt α f : ℤ) : K) := by
  have h1 : ResidueAt α (dRat f / f) c := by
    rw [h]
    exact residueAt_polePart α c
  have h2 : ResidueAt α (dRat f / f) ((ordAt α f : ℤ) : K) := residueAt_dRat_div_self f hf α
  exact h1.unique h2

theorem rat_ode :
    (∀ ε : RatFunc ℚ, Submission.CDT.dRat ε = ε / (2 * (RatFunc.X - 1)) → ε = 0) ∧
    (∀ ε : RatFunc ℚ, Submission.CDT.dRat ε = -ε / (2 * (RatFunc.X - 1)) → ε = 0) ∧
    (∀ b : RatFunc ℚ, Submission.CDT.dRat b = b / (2 * (RatFunc.X - 1)) + 1 / RatFunc.X → False) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `dRat ε = ε/(2(X-1))`
    intro f hf
    by_contra hf0
    have hD : ((RatFunc.X : RatFunc ℚ) - 1) ≠ 0 := ode_X_sub_one_ne_zero
    have key : (dRat f) / f = RatFunc.C (1 / 2 : ℚ) / ((RatFunc.X : RatFunc ℚ) - 1) := by
      rw [hf]
      field_simp
      rw [ode_two_mul_C_half]
    have hres := logDeriv_eq_polePart_imp hf0
      (by rw [key, ← ode_polePart_one_eq (1 / 2)])
    exact ode_not_int_half _ hres.symm
  · -- `dRat ε = -ε/(2(X-1))`
    intro f hf
    by_contra hf0
    have hD : ((RatFunc.X : RatFunc ℚ) - 1) ≠ 0 := ode_X_sub_one_ne_zero
    have key : (dRat f) / f = RatFunc.C (-(1 / 2)) / ((RatFunc.X : RatFunc ℚ) - 1) := by
      rw [hf]
      field_simp
      rw [ode_two_mul_C_neg_half]
    have hres := logDeriv_eq_polePart_imp hf0
      (by rw [key, ← ode_polePart_one_eq (-(1 / 2))])
    exact ode_not_int_neg_half _ hres.symm
  · -- `dRat b = b/(2(X-1)) + 1/X`
    intro b hb
    have hD : (2 * ((RatFunc.X : RatFunc ℚ) - 1)) ≠ 0 := ode_two_mul_X_sub_one_ne_zero
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, dRat_zero] at hb
      have h1 : ((1 : RatFunc ℚ) / RatFunc.X) = 0 := by simpa using hb.symm
      exact ode_one_div_X_ne_zero h1
    exact simple_pole_ode (α := (0 : ℚ)) hb0 (div_ne_zero hb0 hD) ode_one_div_X_ne_zero
      (by rw [ordAt_div (0 : ℚ) hb0 hD, ode_ordAt_zero_two, sub_zero])
      ode_ordAt_zero_one_div_X hb

end Work.C7
