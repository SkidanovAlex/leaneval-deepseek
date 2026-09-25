import Mathlib
import Submission.BourgainPlan.Interfaces
import Submission.Reduction
import Submission.PolynomialKernel
import Submission.Commons.Analysis.ErgodicPrinciple.ae_tendsto_of_bounded_and_maximal

/-!
# The soft half of Bourgain's polynomial ergodic theorem: shared vocabulary

This file fixes the objects that the assembly `Work.BourgainPlan.Assembly.bourgain_of_parts`
is built from.  Nothing here is specific to polynomials: `HasOsc` is the ℓ² *oscillation*
inequality of a sequence of functions, and `LacConv` is a.e. convergence of such a sequence.

The route (all of it is proved from the two hypotheses of `Submission/BourgainPlan/Interfaces`:
`MaximalStatement` `hM` and `OscillationStatement` `hO`):

* `osc_transference` : transfer `hO` from `ℓ²(ℕ)` (counting measure) to `(X, μ, T)` for the
  polynomial averaging operators, by the same Calderón/orbit argument that proves
  `Commons.Dynamics.Transference.calderon_transference_maximal`.
* `lacunary_ae_of_osc` : the transferred oscillation inequality (a *fixed* increasing sequence
  of blocks, `J` blocks, constant `o(J)`) forces a.e. convergence of the sequence — the
  "greedy oscillating blocks" argument, carried out with a *quantile* choice of the block
  endpoints so that a single block structure witnesses the oscillation on a set of
  measure at least half of the point set under consideration.
* `ae_tendsto_of_lacunary_monotone` : a monotone (in `N ↦ N · u N`) nonnegative sequence whose
  lacunary subsequences `⌊ρ^i⌋` converge a.e. for every `ρ > 1` in a family with `ρ ↓ 1`
  converges a.e.
* `Commons.Analysis.ErgodicPrinciple.ae_tendsto_of_bounded_and_maximal` : the Banach principle
  (already in the commons) upgrades a.e. convergence on the *dense class* of bounded
  functions to all of `L^p`, using the maximal inequality.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Assembly

/-- The lacunary index sequence `⌊ρ ^ i⌋` (used with `ρ > 1`). -/
noncomputable def lac (ρ : ℝ) (i : ℕ) : ℕ := ⌊ρ ^ i⌋₊

/-- **The oscillation inequality.**  For every `ε > 0` there is `J₀` such that for every
`J ≥ J₀` and every strictly increasing `k : ℕ → ℕ`, the sum over the `J` blocks
`[k j, k (j+1))` of the squared `L²` norms of the block oscillation is at most `ε * J * C`.

This is exactly the shape of `Submission.BourgainPlan.OscillationStatement`, with the counting
measure replaced by a general measure `μ` and the polynomial averages replaced by a general
sequence of functions `u`. -/
def HasOsc {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : ℕ → X → ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ k : ℕ → ℕ, StrictMono k →
    ∑ j ∈ Finset.range J,
        ∫⁻ x, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i x - u (k j) x‖ₑ) ^ (2 : ℝ) ∂μ
      ≤ ENNReal.ofReal (ε * J) * C

/-- Almost everywhere convergence of a sequence of functions. -/
def LacConv {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : ℕ → X → ℝ) : Prop :=
  ∃ F : X → ℝ, ∀ᵐ x ∂μ, Tendsto (fun i => u i x) atTop (nhds (F x))

end Work.BourgainPlan.Assembly
