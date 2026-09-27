import Mathlib
import Submission.Work.EKLC7.LeafFlowerDefs
import Submission.Work.EKLC7.LocalFlowerDefs

/-!
# `Work.EKLC7.LocalFlowDefs` — the local flower family (countably many flowers near a point)

The geometric input of the construction of leafwise measures is the *local flower family*
(Pisa 6.7 + 6.9–6.15) in the following form: at a point `x₀` with trivial `U`-stabiliser, and for
every radius `R > 0`, there are

* an open neighbourhood `O` of `x₀`,
* countably many flowers `(R, E n, Z n, m n)`: measurable bases `E n ⊆ Z n` and plaque algebras
  `m n` on `Z n` such that the atom of `m n` at every `x ∈ E n` contains the `R`-plaque of `x`,

whose bases cover `O ∩ {free points}`.

This is deliberately weaker than the `Work.EKLC7.LocalFlower` of `LocalFlowerDefs.lean` (which
asks for a *single* flower whose base contains all the free points of its neighbourhood): the
construction of the flowers (a collar of a transversal section of the `U`-foliation, with
countably many translates of the section along the `U`-orbit direction) naturally produces a
*countable family*, and it is this family form which the measure-theoretic assembly of
`Work.EKLC7.FlowerFamExists` consumes.

The assembly `FlowerFam_of_localFlowerFam` (in `Work.EKLC7.FlowerFamExists`) shows that the
weaker form suffices: for every free point `y` which is not negligible, some basis element
`basis n ∋ y` lies in the neighbourhood `O` of a local flower family, and then `y` lies in one of
the bases `E k` of that family.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract
open Work.EKLComp

/-- The free locus of the `U`-action on `X₃`: the points with trivial `U`-stabiliser. -/
def FreeSet (U : Subgroup SL3) : Set X3 := {x : X3 | ∀ u ∈ U, u • x = x → u = 1}

theorem mem_FreeSet {U : Subgroup SL3} {x : X3} :
    x ∈ FreeSet U ↔ ∀ u ∈ U, u • x = x → u = 1 := Iff.rfl

/-- **The local flower family** (Pisa 6.7 + 6.9–6.15): for a point `x₀` with trivial
`U`-stabiliser and every radius `R > 0` there are countably many radius-`R` flowers, with
measurable bases, whose bases cover a neighbourhood of `x₀` intersected with the free locus. -/
def LocalFlowerFamAt (U : Subgroup SL3) (x₀ : X3) (R : ℝ) : Prop :=
  ∃ (E Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (O : Set X3),
    IsOpen O ∧ x₀ ∈ O ∧
    (∀ n, @MeasurableSet X3 Work.EKLContract.instMeasurableSpaceX3 (E n)) ∧
    (∀ n, BigPlaqueOn U R (E n) (Z n) (m n)) ∧
    (O ∩ FreeSet U) ⊆ ⋃ n, E n

/-- The local flower family, uniformly in the point and the radius. -/
def LocalFlowerFam (U : Subgroup SL3) : Prop :=
  ∀ x₀ : X3, (∀ u ∈ U, u • x₀ = x₀ → u = 1) → ∀ R : ℝ, 0 < R → LocalFlowerFamAt U x₀ R

/-- **The geometric input** (Pisa 6.7 + 6.9–6.15) for horospherical subgroups of `SL₃(ℝ)`. -/
abbrev LocalFlowerFamHyp : Prop := ∀ (U : Subgroup SL3), IsHoro U → LocalFlowerFam U

end Work.EKLC7
