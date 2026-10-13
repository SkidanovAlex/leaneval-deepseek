/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.Polynomial.natDegree_sub_taylor_natCast` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Work.WilE2.BzPort.P20

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.Polynomial.natDegree_sub_taylor_natCast ====
section

open Polynomial

namespace Commons.Algebra.Polynomial

/-- The coefficient of degree `P.natDegree - 1` of the Taylor expansion `taylor a P` of `P` at `a`.
Writing `n = P.natDegree`, only the terms of `P` of degree `n - 1` and `n` contribute, so
`(taylor a P).coeff (n - 1) = P.coeff (n - 1) + n * a * P.coeff n`.  (This is the `k = 1`
Hasse-derivative coefficient of the shift `X ↔ X + a`.) -/
theorem coeff_taylor_natDegree_sub_one {R : Type*} [CommSemiring R] (P : R[X]) (a : R)
    (hn : 0 < P.natDegree) :
    (taylor a P).coeff (P.natDegree - 1) =
      P.coeff (P.natDegree - 1) + (P.natDegree : R) * a * P.coeff P.natDegree := by
  have h1 : (taylor a P).coeff (P.natDegree - 1) =
      (hasseDeriv (P.natDegree - 1) P).eval a := by
    rw [taylor_coeff]
  rw [h1]
  have hnd : (hasseDeriv (P.natDegree - 1) P).natDegree < 2 := by
    have := natDegree_hasseDeriv_le P (P.natDegree - 1)
    omega
  rw [eval_eq_sum_range' hnd a]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  rw [hasseDeriv_coeff, hasseDeriv_coeff]
  simp only [zero_add, pow_zero, mul_one, pow_one]
  rw [Nat.choose_self]
  have h2 : 1 + (P.natDegree - 1) = P.natDegree := by omega
  rw [h2]
  have h3 : P.natDegree.choose (P.natDegree - 1) = P.natDegree := by
    rw [Nat.choose_symm (k := 1) (by omega : 1 ≤ P.natDegree), Nat.choose_one_right]
  rw [h3]
  ring

/-- The first-order Taylor defect `P - taylor (-e) P` of a nonzero polynomial `P` over `ℚ`
and a positive natural number `e`: it has degree one less than `P`, and its leading coefficient
is `e * P.natDegree * P.coeff P.natDegree`. -/
theorem natDegree_sub_taylor_natCast {P : Polynomial ℚ} {e : ℕ} (he : 0 < e) (hP : P ≠ 0) :
    (P - Polynomial.taylor (-(e : ℚ)) P).natDegree = P.natDegree - 1 ∧
    (P - Polynomial.taylor (-(e : ℚ)) P).coeff (P.natDegree - 1)
      = (e : ℚ) * P.natDegree * P.coeff P.natDegree := by
  by_cases hn : P.natDegree = 0
  · -- `P` is a nonzero constant, so the Taylor defect vanishes.
    have hC : P = C (P.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
    rw [hC]
    simp [taylor_C]
  · have hn' : 0 < P.natDegree := by omega
    have hcoeff : (P - taylor (-(e : ℚ)) P).coeff (P.natDegree - 1)
        = (e : ℚ) * P.natDegree * P.coeff P.natDegree := by
      rw [coeff_sub, coeff_taylor_natDegree_sub_one P (-(e : ℚ)) hn']
      ring
    constructor
    · -- The defect has degree at most `n - 1` ...
      have hle : (P - taylor (-(e : ℚ)) P).natDegree ≤ P.natDegree - 1 := by
        by_cases hQ : P - taylor (-(e : ℚ)) P = 0
        · rw [hQ, natDegree_zero]; omega
        · have hdeg : (P - taylor (-(e : ℚ)) P).degree < P.degree :=
            degree_sub_lt_left (by rw [degree_taylor]) hP (by rw [leadingCoeff_taylor])
          rw [degree_eq_natDegree hP] at hdeg
          have := (natDegree_lt_iff_degree_lt hQ).mpr hdeg
          omega
      -- ... and its `(n - 1)`-st coefficient is nonzero, so the degree is exactly `n - 1`.
      have hne : (P - taylor (-(e : ℚ)) P).coeff (P.natDegree - 1) ≠ 0 := by
        rw [hcoeff]
        have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
        have hn'' : (P.natDegree : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn'.ne'
        have hc : P.coeff P.natDegree ≠ 0 := by
          rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hP
        exact mul_ne_zero (mul_ne_zero he' hn'') hc
      exact natDegree_eq_of_le_of_coeff_ne_zero hle hne
    · rw [hcoeff]

end Commons.Algebra.Polynomial
end


