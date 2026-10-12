import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.PerBoxCrudeDefs` — the vocabulary of the crude per-box bound

Shared definitions for the decomposition of `Work.BoseFixR.PerBoxWordCrude`
(the crude per-box lower bound for the sliding word `Work.BoseFixB1.sbWord`,
FS `thm:smallbox` with the positive square dropped and the FS regime supplied
by the *free* smallness threshold `ε₀` of the statement).

## The two quantities

* `occChi M ℓ d u Φ` — the `χ_{B(u)}`-weighted particle count of the state `Φ`,
  `∫_{abox n ℓ} Φ(x)² · Σᵢ χ_{B(u)}(xᵢ) dx`.  It is the exact weight that the
  *fibre* (one-body) term of the localised potential word carries: in the FS
  regime the fibre kernel is dominated pointwise by `K·(a v)·χ_{B(u)}(z)`, so
  the negative part of the word is controlled by `μ·(a v)·occChi` and nothing
  else.

* `PerBoxCrudeThreshold K M ℓ d u Φ` — the scale at which the crude mechanism
  changes: `K·(μ·chiMass + 1)·‖Φ‖²`.  Below it (`≤`) the *pointwise* fibre
  bound alone pays the fibre cost; above it (the "high occupancy" case,
  delegated as `Work.BoseFixR.PerBoxWordCrudeHigh`) the coherent (mean-field)
  and excited (kinetic-gap) mechanisms pay it.

## Why these are the right objects

`μ·chiMass(u) + 1` is the *expected* number of particles in the box `B(u)` at
density `μ` (plus the single-particle term): for a state with no more than that
many weighted particles the fibre cost is already `≤ C(μ²a·chiMass + μa)`, so
nothing else is needed.  The interest is entirely in the complementary regime,
which is where FS's per-box analysis (`lm:appinteractionestimate` at the
sliding box) is needed.

Everything in this module is `sorry`-free.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixR


open Submission.BoseGases

set_option autoImplicit false

/-- **The `χ_{B(u)}`-weighted particle count** of a state `Φ` over the centred
box `abox n ℓ`: `∫ Φ(x)²·Σᵢ χ_{B(u)}(xᵢ) dx`, where
`χ_{B(u)} = chiSmallB M ℓ d u` is the corpus's two-factor small-box cutoff. -/
noncomputable def occChi (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n, chiSmallB M ℓ d u (x i))

/-- **The threshold of the crude mechanism**: `K·(μ·chiMass(u) + 1)·‖Φ‖²`, the
scale below which the pointwise fibre bound alone controls the localised word.
`normB` is the corpus's `L²`-norm square over the centred box. -/
noncomputable def crudeThreshold (v : EuclideanSpace ℝ (Fin 3) → ℝ) (K μ : ℝ) (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  K * (μ * Work.SmallBoxSliding.chiMass M ℓ d u + 1) *
    Work.BoseBoxFix.normB v μ n Φ

end Work.BoseFixR
