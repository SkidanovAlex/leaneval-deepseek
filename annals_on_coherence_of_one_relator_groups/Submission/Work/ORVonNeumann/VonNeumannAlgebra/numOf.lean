/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The structure map `N(G) →+* U(G)`

`U(G)` is the Ore localisation of `N(G)` at its non-zero-divisors, and the natural map
`N(G) →+* U(G)` is `OreLocalization.numeratorRingHom`.  That construction takes the Ore
condition as a *typeclass* argument, which makes it awkward to mention in a statement about
a *fixed* model (typeclass search cannot reconstruct the model from its carrier).

This file fixes the map as a plain definition `Work.ORVonNeumann.VonNeumannAlgebra.numOf D`,
using the Ore condition stored in `D`.  It is definitionally `OreLocalization.numeratorRingHom`
for the instance `D.oreSet`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.VonNeumannAlgebra

set_option autoImplicit false

universe u

namespace Work.ORVonNeumann.VonNeumannAlgebra

/-- The structure map `N(G) →+* U(G)` of the Ore localisation `U(G) = N(G)[(nzd)⁻¹]`. -/
noncomputable def numOf {G : Type u} [Group G] (D : Work.ORVonNeumann.GroupVonNeumannAlgebra G) :
    D.N →+* D.affiliated :=
  letI := D.oreSet
  OreLocalization.numeratorRingHom

/-- `numOf D` is the numerator map of the Ore localisation of `D.N`. -/
theorem numOf_apply {G : Type u} [Group G] (D : Work.ORVonNeumann.GroupVonNeumannAlgebra G)
    (b : D.N) :
    numOf D b = OreLocalization.numeratorHom (S := nonZeroDivisors D.N) b := rfl

end Work.ORVonNeumann.VonNeumannAlgebra
