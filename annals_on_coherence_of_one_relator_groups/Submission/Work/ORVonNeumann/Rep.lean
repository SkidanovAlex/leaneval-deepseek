/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# `ℓ²(G)`, the right regular representation and the group von Neumann algebra

The group von Neumann algebra `N(G)` is the commutant of the right regular representation
of `G` on `ℓ²(G)`.  This file provides the substrate:

* `Work.ORVonNeumann.l2 G` — the Hilbert space `ℓ²(G)` of square-summable complex functions
  on `G`, realised as `MeasureTheory.Lp ℂ 2` for the counting measure (`L2.innerProductSpace`
  supplies the inner product, `MeasureTheory.Lp.instNormedAddCommGroup` the norm);
* `Work.ORVonNeumann.boundedEnd` — `B(ℓ²(G)) = ℓ²(G) →L[ℂ] ℓ²(G)`;
* `Work.ORVonNeumann.commutant` — the commutant of a set of operators, as a
  `StarSubalgebra`, i.e. a concrete von Neumann algebra in the sense of Mathlib's
  `VonNeumannAlgebra`.

## Main results

* `Work.ORVonNeumann.Rep.exists_rightRegular` — the right regular representation exists as a
  monoid homomorphism `G →* B(ℓ²(G))` with `(ρ g)⋆ = ρ g⁻¹`, given by composition with
  `· * g`;
* `Work.ORVonNeumann.Rep.exists_leftRegular` — the left regular representation
  `λ g f = f ∘ (·⁻¹ * ·)`, unitary, and lying in the commutant of the right regular
  representation, i.e. `λ g ∈ N(G)`;
* `Work.ORVonNeumann.groupVonNeumann G` — `N(G)`, the commutant of the right regular
  representation (`Submission.Work.ORVonNeumann.Rep.GroupVonNeumann`);
* `Work.ORVonNeumann.Rep.delta1_separating` — `δ₁` is a separating vector for `N(G)`;
* `Work.ORVonNeumann.Rep.trace_vectorState` — the vector state `τ a = ⟪δ₁, a δ₁⟫` on `N(G)`.

The trace is *not* proved tracial here (that needs the matrix-coefficient computation and the
density of the span of the `δ_g`); traciality is recorded as a field of
`Work.ORVonNeumann.GroupVonNeumannAlgebra`.
-/
import Mathlib

set_option autoImplicit false

universe u

namespace Work.ORVonNeumann

/-- `ℓ²(G)`, the Hilbert space of square-summable complex functions on `G`, with the
counting measure. -/
noncomputable abbrev l2 (G : Type u) [MeasurableSpace G] : Type u :=
  MeasureTheory.Lp ℂ 2 (MeasureTheory.Measure.count : MeasureTheory.Measure G)

variable {G : Type u} [MeasurableSpace G]

/-- The bounded operators on `ℓ²(G)`. -/
abbrev boundedEnd (G : Type u) [MeasurableSpace G] : Type u := l2 G →L[ℂ] l2 G

/-- The commutant of a set of bounded operators on `ℓ²(G)`, as a `*`-subalgebra of `B(ℓ²(G))`.
For `S = Set.range ρ` with `ρ` the right regular representation this is the group von Neumann
algebra `N(G)`. -/
noncomputable def commutant (S : Set (boundedEnd G)) : StarSubalgebra ℂ (boundedEnd G) :=
  StarSubalgebra.centralizer ℂ S

/-- The unit vector `δ₁ ∈ ℓ²(G)`, the indicator function of `{1}`. -/
noncomputable def delta1 (G : Type u) [MeasurableSpace G] [MeasurableSingletonClass G] [One G] :
    l2 G :=
  MeasureTheory.indicatorConstLp 2 (MeasurableSet.singleton (1 : G))
    (by rw [MeasureTheory.Measure.count_singleton]; exact ENNReal.one_ne_top) 1

theorem norm_delta1 (G : Type u) [MeasurableSpace G] [MeasurableSingletonClass G] [One G] :
    ‖delta1 G‖ = 1 := by
  rw [delta1, MeasureTheory.norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [MeasureTheory.Measure.real, MeasureTheory.Measure.count_singleton, ENNReal.toReal_one,
    norm_one, one_mul, Real.one_rpow]

end Work.ORVonNeumann
