import ChallengeDeps
import Submission.Work.TrialState.Basic.contDiff_trial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The trial-state upper-bound segment: the J-lever and the consumer-shaped theorem

This module wires the segment to its consumers:

* `trialE_eq_sum_integral` — `trialE` unfolded into the corpus's configuration
  integral (`kinWord`'s double sum of `∫(∂ᵢₖΦ)²` plus the diagonal
  `qLHSword` density), i.e. the precise object the energy evaluation acts on;
* **`aprioriPsi_of_secondOrder`** — the **J-lever**: from the named residual
  `SecondOrderUpperBound` with constant `C` and any `J` with `C ≤ J`, a state
  whose energy satisfies FS `eq:aprioriPsi` with that `J` (the exact `hEgc`
  shape of `APrioriSkeleton.APrioriData`);
* `exists_hEgc_of_trialFamily` — the same, but with the residual restricted to
  the *explicit product-type trial family* `trial N φ f` of `Defs.lean`
  (condensate orbital × pair correlation), so that the residual is a statement
  about a concrete variational family rather than about an abstract state.

NOTE (the direction of the `J`-monotonicity, and why the constant matters): the
threshold `−4πμ²aℓ³(1 − Jν)` is *increasing* in `J`, so a state proved with
constant `C` satisfies the hypothesis for every `J ≥ C`; conversely the chain
`Assembly.cnPlus_and_R_le` concludes with `(J + K_B³)`, so the consumer wants
`J` as small as the state allows.  Hence the deliverable shape is
"for every `J` with `C ≤ J ≤ K_B³`", i.e. the consumer must have `K_B³ ≥ C`
(the `J`-lever of the assignment).  See `NOTES.md` §3.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.TrialState

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The `H_Λ(μ)`-energy word of the trial state, unfolded into the corpus's
configuration integral: the kinetic double sum plus the diagonal potential
density of `qLHSword`. -/
theorem trialE_eq_sum_integral {N : ℕ} {ℓ μ : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (φ f : ℝ³ → ℝ) :
    trialE N ℓ μ v h φ f
      = (∑ i : Fin N, ∑ k : Fin 3,
          ∫ x in abox N ℓ, (fderiv ℝ (trial N φ f) x (kcDir N i k)) ^ 2)
        + ∫ x in abox N ℓ, (trial N φ f x) ^ 2 *
            (- μ * (∑ i : Fin N, w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
              + (1 / 2) * (∑ p ∈ pairSet N, wPairC ℓ v (x p.1) (x p.2))) := by
  rfl

/-- **The `J`-lever**: a state satisfying the second-order energy evaluation
with constant `C` satisfies FS `eq:aprioriPsi` with every `J ≥ C`
(in particular every `J` in `(C, K_B³]`).  Pure threshold monotonicity. -/
theorem aprioriPsi_of_secondOrder {N : ℕ} {ℓ μ C J : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (ha : 0 ≤ a v) (hC : 0 ≤ C) (hCJ : C ≤ J)
    (hS : SecondOrderUpperBound N ℓ μ C v h) :
    ∃ Φ : X N → ℝ, Continuous Φ ∧ (∫ x in abox N ℓ, (Φ x) ^ 2) = 1 ∧
      kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
  obtain ⟨Φ, hΦc, hΦ1, hΦE⟩ := hS
  refine ⟨Φ, hΦc, hΦ1, le_trans hΦE ?_⟩
  have hnu : 0 ≤ (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hpos : 0 ≤ 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 := by positivity
  have hmono : C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) ≤ J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right hCJ hnu
  have hkey : 1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
      ≤ 1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by linarith
  have hb := neg_le_neg (mul_le_mul_of_nonneg_left hkey hpos)
  simpa [neg_mul] using hb

/-- The same as `aprioriPsi_of_secondOrder`, but with the residual restricted
to the explicit product-type trial family of `Defs.lean`: if some `(φ, f)` in
that family gives the second-order energy evaluation, then the segment's
deliverable (the `hEgc`-shaped statement) follows. -/
theorem exists_hEgc_of_trialFamily {N : ℕ} {ℓ μ C J : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (ha : 0 ≤ a v) (hCJ : C ≤ J)
    (hEval : ∃ φ f : ℝ³ → ℝ,
      ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ f ∧
        (∫ x in abox N ℓ, (trial N φ f x) ^ 2) = 1 ∧
          trialE N ℓ μ v h φ f
            ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) :
    ∃ Φ : X N → ℝ, Continuous Φ ∧ (∫ x in abox N ℓ, (Φ x) ^ 2) = 1 ∧
      kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
  obtain ⟨φ, f, hφ, hf, hnorm, hE⟩ := hEval
  refine ⟨trial N φ f, (Basic.contDiff_trial hφ hf).continuous, hnorm, le_trans hE ?_⟩
  have hnu : 0 ≤ (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hpos : 0 ≤ 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 := by positivity
  have hmono : C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) ≤ J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right hCJ hnu
  have hkey : 1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
      ≤ 1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by linarith
  have hb := neg_le_neg (mul_le_mul_of_nonneg_left hkey hpos)
  simpa [neg_mul] using hb

end Work.TrialState
