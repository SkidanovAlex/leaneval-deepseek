/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# `{δ_g}` is a Hilbert basis of `ℓ²(G)`, and Parseval's identity

Combining orthonormality (`Submission.Work.ORVonNeumann.Rep.Orthonormal`) with density of the
closed span (`Submission.Work.ORVonNeumann.Rep.DenseSpan`) gives a Hilbert basis of `ℓ²(G)`
indexed by `G`, whose `g`-th vector is `δ_g`.  From it we obtain the expansion
`x = ∑' g, ⟪δ_g, x⟫ • δ_g` and Parseval's identity
`⟪x, y⟫ = ∑' g, ⟪x, δ_g⟫ ⟪δ_g, y⟫`.

These are the tools with which the trace `τ a = ⟪δ₁, a δ₁⟫` on `N(G)` is shown to be tracial
(`Submission.Work.ORVonNeumann.Rep.TauTracial`).

## Main results

* `Work.ORVonNeumann.Rep.deltaGHilbertBasis` — a `HilbertBasis G ℂ (l2 G)` with
  `deltaGHilbertBasis g = deltaG g`;
* `Work.ORVonNeumann.Rep.parseval` — `∑' g, ⟪x, δ_g⟫ * ⟪δ_g, y⟫ = ⟪x, y⟫`;
* `Work.ORVonNeumann.Rep.hasSum_expansion`, `Work.ORVonNeumann.Rep.tsum_expansion` —
  `x = ∑' g, ⟪δ_g, x⟫ • δ_g`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep
import Submission.Work.ORVonNeumann.Rep.DenseSpan

set_option autoImplicit false

namespace Work.ORVonNeumann.Rep

open MeasureTheory

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **The family `δ_g` is a Hilbert basis of `ℓ²(G)`.** -/
noncomputable def deltaGHilbertBasis : HilbertBasis G ℂ (l2 G) :=
  HilbertBasis.mk (orthonormal_deltaG (G := G)) (dense_span_deltaG (G := G))

/-- The Hilbert basis `deltaGHilbertBasis` is the family `δ_g`. -/
@[simp]
theorem deltaGHilbertBasis_apply (g : G) : (deltaGHilbertBasis (G := G)) g = deltaG g :=
  congrFun (HilbertBasis.coe_mk (orthonormal_deltaG (G := G)) (dense_span_deltaG (G := G))) g

/-- **Parseval's identity** for the Hilbert basis `{δ_g}`:
`⟪x, y⟫ = ∑' g, ⟪x, δ_g⟫ * ⟪δ_g, y⟫`. -/
theorem parseval (x y : l2 G) :
    (∑' g : G, inner ℂ x (deltaG g) * inner ℂ (deltaG g) y) = inner ℂ x y := by
  have h := (deltaGHilbertBasis (G := G)).tsum_inner_mul_inner x y
  simpa using h

/-- The expansion of a vector of `ℓ²(G)` in the Hilbert basis `{δ_g}`. -/
theorem hasSum_expansion (x : l2 G) :
    HasSum (fun g : G => inner ℂ (deltaG g) x • deltaG g) x := by
  have h := (deltaGHilbertBasis (G := G)).hasSum_repr x
  simpa [HilbertBasis.repr_apply_apply] using h

/-- The expansion of a vector of `ℓ²(G)` in the Hilbert basis `{δ_g}`, as an infinite sum. -/
theorem tsum_expansion (x : l2 G) :
    (∑' g : G, inner ℂ (deltaG g) x • deltaG g) = x :=
  (hasSum_expansion x).tsum_eq

end Work.ORVonNeumann.Rep
