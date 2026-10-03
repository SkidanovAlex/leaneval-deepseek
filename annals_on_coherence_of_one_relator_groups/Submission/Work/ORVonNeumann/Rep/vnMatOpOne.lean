/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The matrix operator of the identity matrix is the identity

`Work.ORVonNeumann.Rep.matOp A` (`Submission.Work.ORVonNeumann.Rep.vnCore`) associates to a
matrix `A : Mat_{n × m}(N(G))` the bounded operator `⊕_{j : Fin m} ℓ²(G) → ⊕_{i : Fin n} ℓ²(G)`
acting on the `i`-th coordinate by `(matOp A x)_i = ∑_j A_{ij} (x_j)`.

Together with `Work.ORVonNeumann.Rep.vnMatOpMul` (multiplicativity) and
`Work.ORVonNeumann.Rep.vnMatOpAdjoint` (adjoint = conjugate transpose), the unit law proved
here says that `A ↦ matOp A` is a unital `*`-representation of the matrix ring
`Matₙ(N(G))` on `⊕^n ℓ²(G)`.  This is what lets the von Neumann dimension machinery identify
`rk_G` on `N(G)`-matrices with the dimension of the kernel of a genuine operator, with the
identity matrix corresponding to the identity operator
(Jaikin-Zapirain–López-Álvarez, arXiv:1810.12135, §3.4; Lück, *L²-Invariants*).

## Main results

* `Work.ORVonNeumann.Rep.coe_one_groupVonNeumann` — the unit of `N(G)`, coerced to
  `B(ℓ²(G))`, is the identity operator;
* `Work.ORVonNeumann.Rep.vnMatOpOne` — `matOp (1 : Matₙ(N(G))) = 1`.
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

/-- The unit of the group von Neumann algebra, viewed as an operator on `ℓ²(G)`, is the
identity operator. -/
@[simp]
theorem coe_one_groupVonNeumann :
    ((1 : ↥(groupVonNeumann G)) : boundedEnd G) = 1 := by
  simp

/-- **`matOp` preserves the unit**: the operator of the identity matrix over `N(G)` is the
identity operator on the finite direct sum `⊕^k ℓ²(G)`.

The matrix operator of `1` is `∑ i, hinclude i ∘ hcoord i`, since the off-diagonal entries
vanish and the diagonal entries are the operator `1`; and `∑ i, hinclude i ∘ hcoord i = 1`
because the coordinate projections and inclusions are the structure maps of the direct sum. -/
theorem vnMatOpOne {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (k : ℕ) : Work.ORVonNeumann.Rep.matOp (G := G) (1 : Matrix (Fin k) (Fin k) (↥(Work.ORVonNeumann.groupVonNeumann G))) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro i
  -- Only the diagonal entry `(1 : Matₙ(N(G))) i i = 1` contributes to the `i`-th coordinate.
  rw [hcoord_matOp_apply]
  rw [Finset.sum_eq_single i]
  · -- the diagonal entry is the identity operator
    rw [Matrix.one_apply_eq, coe_one_groupVonNeumann]
    simp
  · -- the off-diagonal entries vanish
    intro j _ hj
    rw [Matrix.one_apply, if_neg (Ne.symm hj)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

end Work.ORVonNeumann.Rep
