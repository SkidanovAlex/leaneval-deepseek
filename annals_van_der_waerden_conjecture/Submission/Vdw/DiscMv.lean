import Mathlib
import Submission.Vdw.ResidueIndex
import Submission.Commons.FieldTheory.Polynomial.discr_coeffVector_eval
import Submission.Commons.FieldTheory.Polynomial.discr_ne_zero_of_separable

/-!
# The discriminant as a polynomial in the coefficients

Glue between the fleet lemma
`Commons.FieldTheory.Polynomial.discr_coeffVector_eval` (the discriminant of
the generic monic degree-`n` polynomial is a polynomial in the non-leading
coefficients, and evaluation at a vector `v` recovers `discr` of the monic
polynomial built from `v`) and the corpus's `monicOfTrail` language
(`Submission.Vdw.ResidueIndex`).

Future use (Case III / geometric sieve, mod-`p` discriminant counting): apply
`Submission.Vdw.MvZeroCount.eval_zero_card_le` to `discrMv n` to bound the
number of monic degree-`n` polynomials over a finite field with vanishing
discriminant by a constant times `|F|^(n-1)`, once a total-degree bound for
`discrMv` is established.
-/

namespace Submission.Vdw

noncomputable section

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [DecidableEq F]

/-- The generic monic degree-`n` polynomial whose non-leading coefficients are the
variables `X i` of `MvPolynomial (Fin n) F`. -/
abbrev gMonPoly (n : ℕ) : (MvPolynomial (Fin n) F)[X] :=
  X ^ n + Polynomial.ofFn n (fun i : Fin n => MvPolynomial.X i)

/-- The discriminant of the generic monic degree-`n` polynomial, as a polynomial in the
`n` non-leading coefficients. -/
abbrev discrMv (n : ℕ) : MvPolynomial (Fin n) F :=
  Polynomial.discr (gMonPoly n)

/-- Evaluating `discrMv n` at the coefficient vector `v` gives the discriminant of the monic
polynomial `monicOfTrail n v` with those coefficients. -/
theorem discrMv_eval_monicOfTrail (n : ℕ) (v : Fin n → F) :
    (discrMv n).eval v = Polynomial.discr (monicOfTrail n v) := by
  simpa [discrMv, gMonPoly, monicOfTrail] using
    (Commons.FieldTheory.Polynomial.discr_coeffVector_eval (F := F) n v)

/-- Symmetric form: the discriminant of the monic polynomial built from `v` equals the
evaluation of the generic discriminant at `v`. -/
theorem monicOfTrail_discr_eq_discrMv_eval (n : ℕ) (v : Fin n → F) :
    Polynomial.discr (monicOfTrail n v) = (discrMv n).eval v :=
  (discrMv_eval_monicOfTrail n v).symm

/-- The generic discriminant is not the zero polynomial (for `2 ≤ n`... actually
`1 ≤ n`, any `n ≥ 1` works) over any field whose characteristic does not divide `n`:
`discrMv n` is nonzero when evaluated at the coefficient vector of `X^n − 1`, which is
monic, separable (`X_pow_sub_one_separable_iff`), hence has nonzero discriminant
(`discr_ne_zero_of_separable`). -/
theorem discrMv_ne_zero (n : ℕ) (hn : 1 ≤ n) (hchar : (n : F) ≠ 0) :
    discrMv n ≠ (0 : MvPolynomial (Fin n) F) := by
  intro hz
  let v0 : Fin n → F := fun (i : Fin n) => if (i : Fin n).val = 0 then (-1 : F) else (0 : F)
  have hof : Polynomial.ofFn n v0 = Polynomial.C (-1 : F) := by
    ext i
    by_cases hi0 : i = 0
    · subst i
      have h0n : 0 < n := by omega
      rw [Polynomial.ofFn_coeff_eq_val_of_lt (v := v0) h0n]
      simp [v0]
    · by_cases hil : i < n
      · rw [Polynomial.ofFn_coeff_eq_val_of_lt (v := v0) hil]
        have hR : (Polynomial.C (-1 : F) : F[X]).coeff i = 0 := by
          rw [Polynomial.coeff_C]
          simp [hi0]
        have hL : v0 ⟨i, hil⟩ = 0 := by
          simp [v0, hi0]
        rw [hL, hR]
      · rw [Polynomial.ofFn_coeff_eq_zero_of_ge (v := v0) (le_of_not_gt hil)]
        have hR : (Polynomial.C (-1 : F) : F[X]).coeff i = 0 := by
          rw [Polynomial.coeff_C]
          simp [hi0]
        rw [hR]
  have hv : monicOfTrail n v0 = X ^ n - 1 := by
    rw [monicOfTrail, hof]
    simp [sub_eq_add_neg]
  have hdisc : (discrMv n).eval v0 = Polynomial.discr (X ^ n - 1 : F[X]) := by
    rw [← monicOfTrail_discr_eq_discrMv_eval n v0]
    exact congrArg Polynomial.discr hv
  have hne0 : Polynomial.discr (X ^ n - 1 : F[X]) ≠ 0 := by
    exact Commons.FieldTheory.Polynomial.discr_ne_zero_of_separable (X ^ n - 1 : F[X])
      (Polynomial.monic_X_pow_sub_C (1 : F) (by omega : n ≠ 0))
      (Polynomial.X_pow_sub_one_separable_iff.mpr hchar)
  have hz0 : (discrMv n).eval v0 = 0 := by
    rw [hz]
    simp
  exact hne0 (by rw [hdisc] at hz0; exact hz0)
