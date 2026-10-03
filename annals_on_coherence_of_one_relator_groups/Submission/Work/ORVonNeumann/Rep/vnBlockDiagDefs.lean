/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# Block inclusions and retractions for the `ℓ²`-direct sums `HSum`

The finite direct sum `Work.ORVonNeumann.Rep.HSum n = ⊕_{i : Fin n} ℓ²(G)` carries a canonical
splitting along `Fin (a + b) ≃ Fin a ⊕ Fin b`:

* `Work.ORVonNeumann.Rep.incL a b : HSum a →L[ℂ] HSum (a + b)` — the inclusion of the left
  block, `x ↦ x ⊕ 0`;
* `Work.ORVonNeumann.Rep.incR a b : HSum b →L[ℂ] HSum (a + b)` — the inclusion of the right
  block, `y ↦ 0 ⊕ y`;
* `Work.ORVonNeumann.Rep.retL a b : HSum (a + b) →L[ℂ] HSum a` and
  `Work.ORVonNeumann.Rep.retR a b : HSum (a + b) →L[ℂ] HSum b` — the corresponding coordinate
  retractions.

These maps express the direct sum decomposition used in
`Work.ORVonNeumann.Rep.vnBlockDiagKernel`: `matOp (blockDiag A B)` is the direct sum of
`matOp A` and `matOp B`, and `hdim` of its kernel is the sum of the `hdim`s of the two kernels.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace
open scoped InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The inclusion of `HSum a` as the left block of `HSum (a + b)`. -/
noncomputable def incL (a b : ℕ) : HSum (G := G) a →L[ℂ] HSum (G := G) (a + b) :=
  ∑ j : Fin a, (hinclude (G := G) (a + b) (finSumFinEquiv (Sum.inl j))).comp
    (hcoord (G := G) a j)

/-- The inclusion of `HSum b` as the right block of `HSum (a + b)`. -/
noncomputable def incR (a b : ℕ) : HSum (G := G) b →L[ℂ] HSum (G := G) (a + b) :=
  ∑ k : Fin b, (hinclude (G := G) (a + b) (finSumFinEquiv (Sum.inr k))).comp
    (hcoord (G := G) b k)

/-- The retraction onto the left block of `HSum (a + b)`. -/
noncomputable def retL (a b : ℕ) : HSum (G := G) (a + b) →L[ℂ] HSum (G := G) a :=
  ∑ j : Fin a, (hinclude (G := G) a j).comp
    (hcoord (G := G) (a + b) (finSumFinEquiv (Sum.inl j)))

/-- The retraction onto the right block of `HSum (a + b)`. -/
noncomputable def retR (a b : ℕ) : HSum (G := G) (a + b) →L[ℂ] HSum (G := G) b :=
  ∑ k : Fin b, (hinclude (G := G) b k).comp
    (hcoord (G := G) (a + b) (finSumFinEquiv (Sum.inr k)))

end Work.ORVonNeumann.Rep
