import Mathlib
import Submission.CDT.RatFuncDeriv
import Submission.Commons.FieldTheory.RatFunc.differential_ratFunc_ext

/-!
# The canonical differential structure on `K(X)`

The formal derivative `dRat` of a rational function (`Submission.CDT.RatFuncDeriv`) is a
derivation, hence `K(X)` carries a canonical `Differential` structure.  This file installs it as a
global instance, so that every statement about `RatFunc K` can use `Differential.deriv` with the
usual meaning `dRat`, without carrying a hypothesis `∀ r, Differential.deriv r = dRat r`.

The explicit `Algebra ℤ (RatFunc K)` instance used by `Differential` (`Ring.toIntAlgebra`) is
distinct from the one coming from `RatFunc.instAlgebraOfPolynomial`; they are propositionally equal
(`Subsingleton (Algebra ℤ _)`) but not definitionally, and typeclass synthesis picks the *latter*
in this file, so `Ring.toIntAlgebra` is given a high local priority.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K]

attribute [local instance 2000] Ring.toIntAlgebra

lemma dRat_algebraMap_field (c : K) : dRat (algebraMap K (RatFunc K) c) = 0 := by
  rw [show algebraMap K (RatFunc K) c
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) c,
      ← Polynomial.C_eq_algebraMap]]
  exact dRat_C c

lemma dRat_intCast (n : ℤ) : dRat (n : RatFunc K) = 0 := by
  rw [← map_intCast (algebraMap K (RatFunc K)) n]
  exact dRat_algebraMap_field (n : K)

lemma dRat_algebraMap_int (n : ℤ) : dRat (algebraMap ℤ (RatFunc K) n) = 0 := by
  have h : algebraMap ℤ (RatFunc K) n = (n : RatFunc K) := by
    simpa using map_intCast (algebraMap ℤ (RatFunc K)) n
  rw [h]; exact dRat_intCast n

/-- **The canonical differential structure on `K(X)`**: the formal derivative. -/
noncomputable instance instDifferentialRatFunc : Differential (RatFunc K) where
  deriv :=
    { toFun := dRat
      map_add' := dRat_add
      map_smul' := by
        intro n f
        rw [Algebra.smul_def, Algebra.smul_def, dRat_mul, dRat_algebraMap_int, zero_mul,
          zero_add, RingHom.id_apply]
      map_one_eq_zero' := dRat_one
      leibniz' := by
        intro a b
        change dRat (a * b) = a * dRat b + b * dRat a
        rw [dRat_mul]
        ring }

theorem deriv_ratFunc_eq_dRat (f : RatFunc K) : Differential.deriv f = dRat f := rfl

/-- **Canonicity**: a `Differential` structure on `K(X)` whose derivative agrees with the formal
derivative on polynomials is the canonical one installed above. -/
theorem differential_ratFunc_unique (d : Differential (RatFunc K))
    (h : ∀ p : Polynomial K, d.deriv (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative) :
    d = instDifferentialRatFunc :=
  Commons.FieldTheory.RatFunc.differential_ratFunc_ext fun p => by
    rw [h p, deriv_ratFunc_eq_dRat, dRat_algebraMap]

end Submission.CDT
