import Submission.Work.EQ.DefsCore

/-! # Support definitions for the end structure of a compact regular cycle

`Submission/Work/EQ/rational_of_compact_cycle.lean` needs the local structure of the two
families of cusps of a compact component `S ⊆ H0` (Rychlik, Cor. 3 / §6.3): near `ψ₁ → 0`
and near `ψ₁ → ∞` (equivalently `ψ₂ → 0`) the component is a finite union of punctured
discs, on which `ψ₁` (resp. `ψ₂`) is an unbranched `k`-th power, all chain coordinates are
meromorphic at the centre, and the half-chain follows the principal leaf after `M` steps.

This file contains only definitions (no proofs); the lemmas about them live in
`Submission/Work/EQ/ends_of_compact_cycle.lean` and
`Submission/Work/EQ/cusp_linearity_of_compact_cycle.lean`.
-/

namespace Work.EQ

open Complex Filter _root_.Topology

/-- The numerator of the meromorphic coordinate `W(q) = y/(x - a/2)` of the point of the chain
`q` at index `-M` (the "head" of the chain when read from the cusp). -/
noncomputable def wNum (M : ℤ) (q : ChainData) : ℂ := (q.1 (-M)).2

/-- The denominator of the meromorphic coordinate `W(q) = y/(x - a/2)`. -/
noncomputable def wDen (a : ℝ) (M : ℤ) (q : ChainData) : ℂ := (q.1 (-M)).1 - ((a / 2 : ℝ) : ℂ)

/-- A chart of an end of `S` at `ψ₁ → 0`: a punctured disc in `S` on which `ψ₁ = w ^ k`, with
all chain coordinates analytic away from the centre and meromorphic at it, and on which the
forward half-chain is the principal leaf from index `M` on. -/
structure A1EndChart (a : ℝ) (h : ℂ → ℂ) (S : Set ChainData) where
  /-- the branching order of `ψ₁` at the cusp -/
  k : ℕ
  hk : 0 < k
  /-- the parametrisation of the punctured disc -/
  ζ : ℂ → ChainData
  hmem : ∀ w ∈ Metric.ball (0 : ℂ) 1 \ {0}, ζ w ∈ S
  hpsi : ∀ w ∈ Metric.ball (0 : ℂ) 1 \ {0}, (ζ w).2.1 = w ^ k
  hinj : Set.InjOn ζ (Metric.ball (0 : ℂ) 1 \ {0})
  hcont : ContinuousOn ζ (Metric.ball (0 : ℂ) 1 \ {0})
  hana₁ : ∀ m : ℤ, AnalyticOnNhd ℂ (fun w => ((ζ w).1 m).1) (Metric.ball (0 : ℂ) 1 \ {0})
  hana₂ : ∀ m : ℤ, AnalyticOnNhd ℂ (fun w => ((ζ w).1 m).2) (Metric.ball (0 : ℂ) 1 \ {0})
  hmero₁ : ∀ m : ℤ, MeromorphicAt (fun w => ((ζ w).1 m).1) 0
  hmero₂ : ∀ m : ℤ, MeromorphicAt (fun w => ((ζ w).1 m).2) 0
  hmeroψ₂ : MeromorphicAt (fun w => (ζ w).2.2) 0
  /-- the index from which the chain follows the principal leaf -/
  M : ℕ
  htail : ∀ w ∈ Metric.ball (0 : ℂ) 1 \ {0}, ∀ n : ℕ, M ≤ n →
    (ζ w).1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ (n : ℤ) * w ^ k)

/-- A chart of an end of `S` at `ψ₁ → ∞` (`ψ₂ → 0`): a punctured disc in `S` on which
`ψ₂ = w ^ k`, with all chain coordinates meromorphic at the centre, and on which the backward
half-chain is the unstable germ from index `-M` on. -/
structure A2EndChart (a : ℝ) (h : ℂ → ℂ) (S : Set ChainData) where
  /-- the branching order of `ψ₂` at the cusp -/
  k : ℕ
  hk : 0 < k
  ζ : ℂ → ChainData
  hmem : ∀ w ∈ Metric.ball (0 : ℂ) 1 \ {0}, ζ w ∈ S
  hpsi : ∀ w ∈ Metric.ball (0 : ℂ) 1 \ {0}, (ζ w).2.2 = w ^ k
  hinj : Set.InjOn ζ (Metric.ball (0 : ℂ) 1 \ {0})
  hcont : ContinuousOn ζ (Metric.ball (0 : ℂ) 1 \ {0})
  hana₁ : ∀ m : ℤ, AnalyticOnNhd ℂ (fun w => ((ζ w).1 m).1) (Metric.ball (0 : ℂ) 1 \ {0})
  hana₂ : ∀ m : ℤ, AnalyticOnNhd ℂ (fun w => ((ζ w).1 m).2) (Metric.ball (0 : ℂ) 1 \ {0})
  hmero₁ : ∀ m : ℤ, MeromorphicAt (fun w => ((ζ w).1 m).1) 0
  hmero₂ : ∀ m : ℤ, MeromorphicAt (fun w => ((ζ w).1 m).2) 0
  hmeroψ₁ : MeromorphicAt (fun w => (ζ w).2.1) 0
  /-- the index from which the chain follows the unstable leaf -/
  M : ℕ
  htail : ∀ w ∈ Metric.ball (0 : ℂ) 1 \ {0}, ∀ n : ℕ, M ≤ n →
    (ζ w).1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ (n : ℤ) * w ^ k)

/-- **The end structure of a compact component.** Near `ψ₁ → 0` (resp. `ψ₂ → 0`, i.e.
`ψ₁ → ∞`) the component `S` is exactly a finite disjoint union of the punctured discs of
`A1EndChart` (resp. `A2EndChart`). -/
structure EndsData (a : ℝ) (h : ℂ → ℂ) (S : Set ChainData) where
  m₁ : ℕ
  E₁ : Fin m₁ → A1EndChart a h S
  m₂ : ℕ
  E₂ : Fin m₂ → A2EndChart a h S
  cover₁ : S ∩ {q | 0 < ‖q.2.1‖ ∧ ‖q.2.1‖ < 1} =
    ⋃ i, (E₁ i).ζ '' (Metric.ball (0 : ℂ) 1 \ {0})
  cover₂ : S ∩ {q | 0 < ‖q.2.2‖ ∧ ‖q.2.2‖ < 1} =
    ⋃ i, (E₂ i).ζ '' (Metric.ball (0 : ℂ) 1 \ {0})
  disj₁ : ∀ i j : Fin m₁, i ≠ j → Disjoint ((E₁ i).ζ '' (Metric.ball (0 : ℂ) 1 \ {0}))
    ((E₁ j).ζ '' (Metric.ball (0 : ℂ) 1 \ {0}))
  disj₂ : ∀ i j : Fin m₂, i ≠ j → Disjoint ((E₂ i).ζ '' (Metric.ball (0 : ℂ) 1 \ {0}))
    ((E₂ j).ζ '' (Metric.ball (0 : ℂ) 1 \ {0}))

end Work.EQ
