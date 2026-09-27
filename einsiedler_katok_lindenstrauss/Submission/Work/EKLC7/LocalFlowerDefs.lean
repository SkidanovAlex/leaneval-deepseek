import Mathlib
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLC7.LeafwiseGeom

/-!
# `Work.EKLC7.LocalFlowerDefs` — the *local* flower (Pisa §6) as a named hypothesis

The construction of leafwise measures (Pisa Theorem 6.3) in this development
(`Submission/Work/EKLC7/LeafNuDefs.lean`) takes as its only geometric input a family of
"flowers" (`Work.EKLC7.FlowerFam`, Pisa Definition 6.14 / Corollary 6.15): countably many plaque
algebras with measurable bases of unbounded radii covering almost every point.

The global family is assembled from a purely local statement, isolated here as the `Prop`
`Work.EKLC7.LocalFlower U`: at every point `x₀` with free `U`-orbit and every radius `R > 0`
there is a plaque algebra whose atoms contain the `R`-plaque of every point of an open
neighbourhood base `G` (the "deep" points of the flower of a bounded cross-section through `x₀`).

This is Pisa 6.7 + 6.9–6.15 (the cross-section construction).  `x₀ ∈ G` and the *shape* clause
`V R ∩ U ⊆ shape m U x` for `x ∈ G` are the two halves used by the consumers.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-- **The local flower through a free point** (Pisa §6).  For a free point `x₀` and a radius
`R > 0` there are a plaque algebra `(Z, m)` and open/base sets `G ⊆ Z`, `O` with `x₀ ∈ O`,
`O` open, `G` measurable, `O ∩ {free points} ⊆ G`, and at every `x ∈ G` the shape of the plaque
algebra contains the whole `R`-plaque: `V R ∩ U ⊆ shape m U x`. -/
def LocalFlowerAt (U : Subgroup SL3) (x₀ : X3) (R : ℝ) : Prop :=
  ∃ (Z : Set X3) (m : MeasurableSpace X3) (G O : Set X3),
    IsOpen O ∧ x₀ ∈ O ∧ MeasurableSet G ∧ G ⊆ Z ∧ IsPlaqueAlgebra U Z m ∧ x₀ ∈ G ∧
    (O ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1} ⊆ G) ∧
    ∀ x ∈ G, V R ∩ (U : Set SL3) ⊆ shape m U x

/-- **The local flower, uniformly in the point and the radius**:  the geometric input of the
construction of leafwise measures, Pisa 6.7 + 6.9–6.15 specialised to `X₃ = SL₃(ℝ)/SL₃(ℤ)`. -/
def LocalFlower (U : Subgroup SL3) : Prop :=
  ∀ x₀ : X3, (∀ u ∈ U, u • x₀ = x₀ → u = 1) → ∀ R : ℝ, 0 < R → LocalFlowerAt U x₀ R

end Work.EKLC7
