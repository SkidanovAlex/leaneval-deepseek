/-
# `Submission.Work.FIChain.S3plusC_route_defs` — imports and vocabulary for the
`S3plusC_zavg_le` route (`NOTES_S3plusC_route.md`)

This module re-exports every module the route's lemmas need (the `S8`/`S8c` integral
representation of `λ±`, the `(1.7)` identity of `S9g`/`S10`, the density `FIgtil` of `S27`, the
`(2.4)`-lemma `mu_density_abel_le`, the `(R′)`-lemma `remainder_all_at_07`, and the two
counting-function bounds `AcountAtilC_{le,ge}_const_mul_rpow`), and fixes the vocabulary of the
route: the divisor weight `σ̃_ℓ`, the outer weight `s3OuterW`, and the *integral form* of the
`λ⁺`-inner sum.

Definitions only (no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.ASP.S8
import Submission.ASP.S8c
import Submission.ASP.S9g
import Submission.ASP.S10
import Submission.ASP.S27
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.remainder_all_at_07
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.NumberTheory.Sieve.sieve_mu_sum_coprime_powLog
import Submission.Work.FIChain.AcountAtilC_le_const_mul_rpow
import Submission.Work.FIChain.AcountAtilC_ge_const_mul_rpow

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `σ̃_ℓ = ∏_{p | ℓ} (1 + 1/√p)`, the coprimality factor of the companion's `(2.4)`. -/
def sigmaTilde (ℓ : ℕ) : ℝ := ∏ p ∈ ℓ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))

/-- The outer weight of the `λ⁺`-half: `Σ_{b | ℓ, sy < b} μ(b)` times `ρ(ℓ)`. -/
def s3OuterB (ℓ : ℕ) (sy : ℝ) : ℝ :=
  ∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)), (ArithmeticFunction.moebius b : ℝ)

/-- The **integrated** form of the `λ⁺`-inner sum: `Σ_{z<c≤sz, ℓc≤N} a(ℓc)·∫_1^{c/Cm}ρ(c;u)du/u`.

By `S3plusC_lamPlus_identity` this equals `S3plusInnerC a N ℓ z sz Cm` whenever `a` is supported
on squarefree integers and `1 ≤ Cm < z`. -/
def s3InnerInt (a : ℕ → ℝ) (N : ℕ) (ℓ Cm : ℕ) (z sz : ℝ) : ℝ :=
  ∑ c ∈ (Finset.Icc 1 N).filter
      (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
    a (ℓ * c) * ∫ u in (1 : ℝ)..(((c : ℕ) : ℝ) / (Cm : ℝ)), Submission.ASP.rhoTrunc c u / u

end

end Work.FIChain
