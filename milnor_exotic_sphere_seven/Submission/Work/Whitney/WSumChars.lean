import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# The vocabulary of the relative Thom product formula for a Whitney sum

For complex gluing-data bundles `Z₁` (rank `m₁`) and `Z₂` (rank `m₂`) over a common base `B`, with
realifications `V₁ = (Z₁)_ℝ`, `V₂ = (Z₂)_ℝ` and `V = (Z₁ ⊕ Z₂)_ℝ`
(`Work.Whitney.whitneySum`, `Work.Thom.realification`), and two coordinate projections

`π₁ : V.TotalSpace → V₁.TotalSpace`, `π₂ : V.TotalSpace → V₂.TotalSpace`

given by the explicit formulas `p ↦ ⟨p.1, ((sumFibreC m₁ m₂).symm p.2).1⟩` and `… .2`, this module
packages

* `Work.Whitney.wsumPiece1`, `wsumPiece2` — the two pieces `π₁⁻¹(V₁∖0)`, `π₂⁻¹(V₂∖0)` of `V∖0`;
* `Work.Whitney.wsumRelTau1`, `wsumRelTau2` — the two pulled-back Thom classes
  `π₁^*τ_{Z₁} ∈ H^{2m₁}(V, π₁⁻¹(V₁∖0))` and `π₂^*τ_{Z₂}`;
* `Work.Whitney.wsumCup` — their relative–relative cup
  `π₁^*τ_{Z₁} ⌣ π₂^*τ_{Z₂} ∈ H^{2m₁+2m₂}(V, π₁⁻¹(V₁∖0) ∪ π₂⁻¹(V₂∖0))`;
* `Work.Whitney.wsumTau` — the Thom class `τ_{Z₁⊕Z₂} ∈ H^{2(m₁+m₂)}(V, V∖0)`;
* `Work.Whitney.wsumCastEq` — the type equality relating the degree `2m₁+2m₂` and the closed set
  `π₁⁻¹(V₁∖0) ∪ π₂⁻¹(V₂∖0)` of `wsumCup` to the degree `2(m₁+m₂)` and the closed set `V∖0` of
  `wsumTau`, built from the degree equality `Nat.mul_add 2 m₁ m₂` (in the direction
  `2*m₁ + 2*m₂ = 2*(m₁+m₂)`) and from the set equality `hset`.

The two statements that use this vocabulary are

* `Work.Whitney.thomClassRank_whitneySum_rel` (the relative Thom product formula, the mathematical
  content of `Work.Whitney.TopClassMul`), and
* `Work.Whitney.chernClass_whitneySum_top_of_thomProduct` (the assembly turning it into the top
  Chern class identity).
-/

namespace Work.Whitney

open Work.Thom
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-- **The first piece of the zero complement of the sum**: the points over which the first
summand of the Whitney sum does not vanish. -/
def wsumPiece1 (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((realification (whitneySum Z₁ Z₂)).TotalSpace, (realification Z₁).TotalSpace)) :
    Set (realification (whitneySum Z₁ Z₂)).TotalSpace :=
  π₁ ⁻¹' zeroComplement (realification Z₁)

/-- **The second piece of the zero complement of the sum**. -/
def wsumPiece2 (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₂ : C((realification (whitneySum Z₁ Z₂)).TotalSpace, (realification Z₂).TotalSpace)) :
    Set (realification (whitneySum Z₁ Z₂)).TotalSpace :=
  π₂ ⁻¹' zeroComplement (realification Z₂)

/-- **The first pulled-back Thom class**: `π₁^* τ_{Z₁} ∈ H^{2m₁}(V, π₁⁻¹(V₁∖0))`. -/
def wsumRelTau1 (hm₁ : 1 ≤ m₁)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((realification (whitneySum Z₁ Z₂)).TotalSpace, (realification Z₁).TotalSpace)) :
    RelCoh ℤ (2 * m₁) (realification (whitneySum Z₁ Z₂)).TotalSpace
      (wsumPiece1 Z₁ Z₂ π₁) :=
  (relCohMap π₁ (wsumPiece1 Z₁ Z₂ π₁) (zeroComplement (realification Z₁))
    (fun _ hx => hx) ℤ (2 * m₁)).hom (thomClassRank m₁ hm₁ Z₁).τ

/-- **The second pulled-back Thom class**: `π₂^* τ_{Z₂} ∈ H^{2m₂}(V, π₂⁻¹(V₂∖0))`. -/
def wsumRelTau2 (hm₂ : 1 ≤ m₂)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₂ : C((realification (whitneySum Z₁ Z₂)).TotalSpace, (realification Z₂).TotalSpace)) :
    RelCoh ℤ (2 * m₂) (realification (whitneySum Z₁ Z₂)).TotalSpace
      (wsumPiece2 Z₁ Z₂ π₂) :=
  (relCohMap π₂ (wsumPiece2 Z₁ Z₂ π₂) (zeroComplement (realification Z₂))
    (fun _ hx => hx) ℤ (2 * m₂)).hom (thomClassRank m₂ hm₂ Z₂).τ

/-- **The relative–relative cup of the two pulled-back Thom classes**, in degree
`2*m₁ + 2*m₂` and relative to the union of the two pieces. -/
noncomputable def wsumCup (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((realification (whitneySum Z₁ Z₂)).TotalSpace, (realification Z₁).TotalSpace))
    (π₂ : C((realification (whitneySum Z₁ Z₂)).TotalSpace, (realification Z₂).TotalSpace))
    (hAopen : IsOpen (wsumPiece1 Z₁ Z₂ π₁)) (hCopen : IsOpen (wsumPiece2 Z₁ Z₂ π₂)) :
    RelCoh ℤ (2 * m₁ + 2 * m₂) (realification (whitneySum Z₁ Z₂)).TotalSpace
      (wsumPiece1 Z₁ Z₂ π₁ ∪ wsumPiece2 Z₁ Z₂ π₂) :=
  tcmRelCup (wsumPiece1 Z₁ Z₂ π₁) (wsumPiece2 Z₁ Z₂ π₂) hAopen hCopen
    (2 * m₁) (2 * m₂) (wsumRelTau1 hm₁ Z₁ Z₂ π₁) (wsumRelTau2 hm₂ Z₁ Z₂ π₂)

/-- **The Thom class of the sum**, in the form used by the statements below. -/
def wsumTau (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    RelCoh ℤ (2 * (m₁ + m₂)) (realification (whitneySum Z₁ Z₂)).TotalSpace
      (zeroComplement (realification (whitneySum Z₁ Z₂))) :=
  (thomClassRank (m₁ + m₂) (Nat.le_trans hm₁ (Nat.le_add_right m₁ m₂))
    (whitneySum Z₁ Z₂)).τ

/-- **The transport** that carries the natural degree `2*m₁ + 2*m₂` and the natural closed set
`π₁⁻¹(V₁∖0) ∪ π₂⁻¹(V₂∖0)` of `Work.Whitney.wsumCup` to the degree `2*(m₁+m₂)` and the closed set
`V∖0` of `Work.Whitney.wsumTau`.  It is the composition of the degree transport along
`Nat.mul_add 2 m₁ m₂` (in the direction `2*m₁ + 2*m₂ = 2*(m₁+m₂)`) with the transport of the closed
set along `hset`. -/
noncomputable def wsumCast
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((realification (whitneySum Z₁ Z₂)).TotalSpace, (realification Z₁).TotalSpace))
    (π₂ : C((realification (whitneySum Z₁ Z₂)).TotalSpace, (realification Z₂).TotalSpace))
    (hset : wsumPiece1 Z₁ Z₂ π₁ ∪ wsumPiece2 Z₁ Z₂ π₂
      = zeroComplement (realification (whitneySum Z₁ Z₂)))
    (x : RelCoh ℤ (2 * m₁ + 2 * m₂) (realification (whitneySum Z₁ Z₂)).TotalSpace
      (wsumPiece1 Z₁ Z₂ π₁ ∪ wsumPiece2 Z₁ Z₂ π₂)) :
    RelCoh ℤ (2 * (m₁ + m₂)) (realification (whitneySum Z₁ Z₂)).TotalSpace
      (zeroComplement (realification (whitneySum Z₁ Z₂))) :=
  hset ▸ (Nat.mul_add 2 m₁ m₂).symm ▸ x

end

end Work.Whitney
