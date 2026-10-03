/-
  Companion paper, §9: the Euler-product identities (9.8) and their consequences.

      `G = ∏_p (1 − g(p²)) = ∑_ν μ(ν)·g(ν²)`      (9.8)

  Derived here from the commons' Euler-product identity
  `Commons.NumberTheory.EulerProduct.tsum_moebius_mul_eq_tprod` applied to the multiplicative
  function `ν ↦ g(ν²)`.
-/
import Mathlib
import Submission.ASP.S9g
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
import Submission.Commons.Data.Nat.squarefree_prod_primes

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- `G = ∏_p (1 − g(p²))` — the constant of the companion's (9.8). -/
def Gprod (g : ℕ → ℝ) : ℝ := ∏' p : {p : ℕ // p.Prime}, (1 - g ((p : ℕ) ^ 2))

end

end Submission.ASP
