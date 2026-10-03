/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The group von Neumann algebra of a countable group, unconditionally

`Work.ORVonNeumann.Rep.countableGroupVonNeumannOfOre` assembles the concrete model
`↥(groupVonNeumann G) = ρ(G)' ⊆ B(ℓ²(G))` into a `GroupVonNeumannAlgebra G`, with the Ore
condition at non-zero-divisors as its only hypothesis.  That condition is Berberian's theorem
for a finite Baer `*`-ring and is proved for `N(G)` in
`Work.Rep.oreSet_nonZeroDivisors` (via the square root of `r⋆ r + s⋆ s`).

Hence, for **every countable group** `G`, `N(G)` is a finite Baer `*`-ring with a faithful
trace whose non-zero-divisors form an Ore set, and the algebra `U(G)` of affiliated operators
exists: `Work.ORVonNeumann.Rep.countableGroupVonNeumann` below has **no hypotheses**.

## Main result

* `Work.ORVonNeumann.Rep.countableGroupVonNeumann : GroupVonNeumannAlgebra G`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.CountableVonNeumann
import Submission.Work.Rep.oreSet_nonZeroDivisors

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORVonNeumann.Rep

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **The group von Neumann algebra of a countable group, unconditionally**: the concrete
model `↥(groupVonNeumann G) = ρ(G)' ⊆ B(ℓ²(G))` with the left regular representation
`λ : G →* N(G)`, the faithful tracial vector state `τ a = ⟪δ₁, a δ₁⟫`, the Baer property and
direct finiteness — every field of `GroupVonNeumannAlgebra` is a theorem. -/
noncomputable def countableGroupVonNeumann : GroupVonNeumannAlgebra G :=
  countableGroupVonNeumannOfOre (Work.Rep.oreSet_nonZeroDivisors (G := G))

end Work.ORVonNeumann.Rep
