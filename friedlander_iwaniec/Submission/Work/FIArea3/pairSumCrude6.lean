/-
# `Submission.Work.FIArea3.pairSumCrude6` — the *crude* branch of the pair sum

## What is here

`pairSumCrude6` is obtained from `Work.FIArea3.pairSumCrude6_assembly` (the τ-weighted
*off-diagonal* pair sum over the polar box in the crude regime) by the trivial reduction
`pairSumCrude6_of_core`: `‖β z‖ ≤ τ(|z|²)` and `0 ≤ ind ≤ 1` replace the weights, and the diagonal
`z₁ = z₂` drops out because `ind z z = 0` (this is *essential*: with `ind` allowed to be `1` on the
diagonal the statement is false, `β = 1_{z₀}` giving the single term `τ(|z₀|²)²`).

`pairSumCrude6_assembly` is proved by the two-regime route described at its own docstring: the
crude regime is split at `u = θ√N = N^{1/4}`; for `u ≤ N^{1/4}` the blunt pointwise bound suffices
because the right-hand side carries the factor `(1+τ⁻¹/θ) ≥ N^{1/3}/u`, and for
`N^{1/4} ≤ u ≤ N^{3/8}` the paper's own route (Lemma 2.2 with `k = 4` splitting the three divisor
functions at *small* divisors, then the per-`z₁` joint lattice count with its gcd-weighted main
term) is used.  See `pairSumCrude6_assembly.lean`, `pairSumCrude6_smallU.lean`, `LargeU*`.

## The obstruction (analysis, session of this file)

Everything except the *average* of the divisor weights is elementary; the pointwise route is

  `LHS ≤ (#(supp β))² · max_{z₁≠z₂} τ(|z₁|²)τ(|z₂|²)(1+τ(|Δ|))`,

with `#(polar box) ≤ πu²/8 + 20u + 20` (`JointCount.box_card_le`), `u := θ√N`,
`τ(|z|²) ≤ 2^{(log N+3)/(loglog x)²}` (from `NoSmallPrimes` of `IsBoxCoeff`, `hPlo`), and
`τ(m) ≤ exp(3 log m/loglog m)` (`JointCount.tau_max_le`) together with `|Δ| ≤ 2πθ(1+θ)N`
(`FIArea4.absDelta_le_sector`).  The right-hand side is
`C(1+τ⁻¹/θ)u⁴(log N)^{2^20−1}` — because `(τ⁻¹+θ)θ³N² = (1+τ⁻¹/θ)u⁴` — and `#supp ≤ K u²`, so
the pointwise route closes iff

  `1.386(log N)/ℓ² + 2.6(log N)/loglog N ≤ (2^20−1)loglog N + max(0, A'ℓ − η log x/3)`,
  `ℓ = loglog x`,

(using `(1+τ⁻¹/θ) ≥ 1+exp(A'ℓ−η log x/3)`, `τ ≤ x^{η/3}`).  This **fails** in an admissible regime:
`Params` imposes no upper bound on `A'` (`hA' : 2A+2^20 ≤ A'`), so one may take `τ = x^{η/3}` (so
`τ⁻¹/θ ≈ 1`), `η > 3/20`, `A'ℓ ∈ [log N/8, η log x/3]` and `log N ≳ 10^9`; then the pointwise
bound overshoots by `exp(1.386 log N/ℓ² − 2^20 loglog x)`.  This is exactly the regime that
`Submission/Work/FIArea3/NOTES.md` §§8–9 records as needing the *average* of `τ` over the values of
`|z|²` and of `Δ = Im(z̄₁z₂)` (the paper's count (10.9)), i.e. the input that
`Work.FIArea3.delta_tau_joint_average` (a.k.a. `JointBound`) states with the *weaker* `(ϑ+θ)`
factor and that remains unproved.  Since `τ⁻¹ ≤ ϑ(log x)^{−124}` and `θ ≤ ϑ`, the requested
`(τ⁻¹+θ)`-form is strictly stronger than that open input in the admissible range `τ ≈ x^{η/3}`.
**The small-modulus route (added after the passage above).**  The paper's own route does *not*
need the pointwise bounds: `Work.FIArea3.lemma_2_2` (proved) with `k = 4` splits each of
`τ(|z₁|²), τ(|z₂|²), τ(|Δ|)` at divisors `d₁,d₂ ≤ (2N)^{1/4}` and `d ≤ (2πθ(1+θ)N)^{1/4} ≤ N^{7/32}`,
at the cost of the exponents `(2τ(d))^8`, and the per-`z₁` joint count
(`JointCount.card_filter_le_le_arith`) is *valid for arbitrary `z₁`* (no primitivity, hence also
for the non-primitive points of an `IsBoxCoeff` support).  Re-indexing by `(d,d₁,d₂)`, the terms of
the resulting divisor sums are `u⁴`(main), `u³`, `u²` times triple divisor sums of
`τ(d)^{O(1)}/(d d₁ d₂)`, which are polylog by `divisor_sum_seventeen`; the `u³`- and `u²`-terms are
compensated by `u ≤ N^{3/8}` and the factor `1+τ⁻¹/θ ≥ 1`.  This is the route delegated to
`Work.FIArea3.pairSumCrude6_assembly` (`JointCount.jointCount6_nonprim` provides the gcd/coprimality
bookkeeping for the non-primitive support).

The truth of the statement is *not* in doubt (the average of the weight over the pairs is
`(log N)^{O(1)}`, so the target has room `(log N)^{2^20−1}`); what is missing is the
distributional input.

`FIArea4.absDelta_le_sector`, `JointCount`, and the elementary pieces are imported above.
-/

import Mathlib
import Submission.Work.FIArea3.pairSumCrude6_assembly
import Submission.Work.FIArea3.PairDefs6
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea3.lemma_2_2
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea3.jointCount6
import Submission.Work.FIArea3.JointCount.card_filter_le_le_arith

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The reduction.**  The requested pair sum is bounded by the τ-weighted off-diagonal pair sum
over the support of `β`: by the pointwise bound `‖β z‖ ≤ τ(|z|²)` of `IsBoxCoeff`, by
`0 ≤ ind ≤ 1`, and because the diagonal `z₁ = z₂` contributes `ind z z · (…) = 0`. -/
theorem pairSumCrude6_of_core
    (hcore : ∃ C : ℝ, 0 < C ∧
      ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ),
        Work.FITop3.IsBoxCoeff Pa φ β →
        (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
        Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
        (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ z1 ≠ z2 then
              (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
                * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                    * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
            else 0))
          ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
              * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
      (ind : GaussianInt → GaussianInt → ℝ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (∀ z : GaussianInt, ind z z = 0) →
      (∀ z1 z2 : GaussianInt, 0 ≤ ind z1 z2) →
      (∀ z1 z2 : GaussianInt, ind z1 z2 ≤ 1) →
      (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
      Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ind z1 z2
            * (‖β z1‖ * ‖β z2‖
                * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))))
        ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) := by
  obtain ⟨C, hC, hcore⟩ := hcore
  refine ⟨C, hC, ?_⟩
  intro Pa φ β ind hβ hdiag hnn hle1 hu10 huN
  refine (Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => ?_))).trans
    (hcore Pa φ β hβ hu10 huN)
  by_cases hz1 : β z1 = 0
  · simp [hz1]
  by_cases hz2 : β z2 = 0
  · simp [hz2]
  by_cases heq : z1 = z2
  · subst heq
    rw [hdiag z1]
    simp
  · rw [if_pos ⟨hz1, hz2, heq⟩]
    have h1 : ‖β z1‖ ≤ (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ) := hβ.1 z1
    have h2 : ‖β z2‖ ≤ (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ) := hβ.1 z2
    have h3 : (0 : ℝ) ≤ 1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) ((Work.FIPlan.absDelta z1 z2).divisors.card)
      linarith
    have h4 : ind z1 z2 ≤ 1 := hle1 z1 z2
    have h5 : (0 : ℝ) ≤ ind z1 z2 := hnn z1 z2
    have key : ‖β z1‖ * ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
        ≤ (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
            * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))) := by
      have h2' : ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
          ≤ (((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
              * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 h3
      calc ‖β z1‖ * ‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))
          = ‖β z1‖ * (‖β z2‖ * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))) := by
            ring
        _ ≤ (((Work.FIPlan.gnorm z1).divisors.card : ℕ) : ℝ)
              * ((((Work.FIPlan.gnorm z2).divisors.card : ℕ) : ℝ)
                  * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))) :=
            mul_le_mul h1 h2' (by positivity) (Nat.cast_nonneg _)
    have h0 : (0 : ℝ) ≤ ‖β z1‖ * ‖β z2‖
        * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)) := by positivity
    calc ind z1 z2 * (‖β z1‖ * ‖β z2‖
            * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)))
        ≤ 1 * (‖β z1‖ * ‖β z2‖
            * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right h4 h0
      _ = ‖β z1‖ * ‖β z2‖
            * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ)) := by ring
      _ ≤ _ := key

lemma pairSumCrude6 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
      (ind : GaussianInt → GaussianInt → ℝ),
      Work.FITop3.IsBoxCoeff Pa φ β →
      (∀ z : GaussianInt, ind z z = 0) →
      (∀ z1 z2 : GaussianInt, 0 ≤ ind z1 z2) →
      (∀ z1 z2 : GaussianInt, ind z1 z2 ≤ 1) →
      (1 / 10 : ℝ) ≤ Pa.θ * Real.sqrt Pa.N →
      Pa.θ * Real.sqrt Pa.N ≤ Pa.N ^ ((3 : ℝ) / 8) →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ind z1 z2
            * (‖β z1‖ * ‖β z2‖
                * (1 + (((Work.FIPlan.absDelta z1 z2).divisors.card : ℕ) : ℝ))))
        ≤ C * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (3 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (((2 : ℕ) ^ (20 : ℕ)) - 1) :=
  -- The analytic input — the τ-weighted *off-diagonal* pair sum over the polar box in the crude
  -- regime — is `Work.FIArea3.pairSumCrude6_assembly`; `pairSumCrude6_of_core` above reduces the
  -- requested sum to it (pointwise `‖β z‖ ≤ τ(|z|²)`, `0 ≤ ind ≤ 1`, and `ind z z = 0` for the
  -- diagonal).
  pairSumCrude6_of_core pairSumCrude6_assembly

end

end Work.FIArea3
