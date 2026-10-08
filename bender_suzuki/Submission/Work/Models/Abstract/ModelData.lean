import Submission.Blueprint.Interfaces
import Submission.Work.Models.Basic
import Submission.Work.Models.Port.BenderSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.Abstract.ModelData` — the model-data layer of `ModelFactsProp`

`Submission.BenderPair` (ported from fm1, `Submission.Work.Models.Port.BenderSetup`) is the
abstract rank-one `(B,N)`-pair of a group with a strongly embedded subgroup.  `ModelData`
adds the four model-specific facts that `ModelFactsProp` needs:

* `K0 = J(T,w) = invertedBy T w` is cyclic of order `#Inv(B) ≥ 2` (the torus inverted by the
  Weyl element),
* the torus `T` is abelian,
* `w² = 1`,
* every involution of `U` is central in `U`.

`ModelFactsFor` is the body of `Submission.Blueprint.ModelFactsProp` for one group, and
`modelFactsProp_of` checks (by `rfl`) that `ModelFactsProp` is
`∀ Y, IsSimpleBenderGroup Y → ModelFactsFor Y`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.Models

/-- Model data: a `BenderPair` plus the four model-specific facts used by `ModelFactsProp`. -/
structure ModelData (G : Type*) [Group G] [Finite G] extends Submission.BenderPair G where
  /-- `K₀ = J(T,w)`: the part of the torus inverted by the Weyl element. -/
  K0 : Subgroup G
  /-- the torus is abelian -/
  hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x
  /-- the Weyl element is an involution -/
  hww : w * w = 1
  /-- `K₀` is `J(T,w)` -/
  hK0 : (K0 : Set G) = invertedBy T w
  /-- `K₀` is cyclic -/
  hK0cyc : IsCyclic K0
  /-- the order of `K₀` is the number of involutions of the Borel -/
  hK0card : Nat.card K0 = (involutions (B : Set G)).ncard
  /-- `K₀` is nontrivial -/
  hK0two : 2 ≤ Nat.card K0
  /-- involutions of `U` are central in `U` -/
  hUinv : ∀ u ∈ U, u * u = 1 → ∀ v ∈ U, u * v = v * u

/-- The body of `ModelFactsProp` for one group (syntactically identical to the definition in
`Submission.Blueprint.Interfaces`). -/
def ModelFactsFor (Y : Type*) [Group Y] : Prop :=
    IsSimpleGroup Y ∧ HasFourGroup Y ∧ (∃ H : Subgroup Y, IsStronglyEmbedded H) ∧
    ∀ H : Subgroup Y, IsStronglyEmbedded H →
      (∀ a ∈ involutions (H : Set Y), ∀ b ∈ involutions (H : Set Y), a * b = b * a) ∧
      ∀ t : Y, orderOf t = 2 → t ∉ H →
        ∃ S K : Subgroup Y, IsPGroup 2 S ∧ S ≤ H ∧ H ≤ Subgroup.normalizer (S : Set Y) ∧
          S ⊓ twoPoint H t = ⊥ ∧ S ⊔ twoPoint H t = H ∧
          (K : Set Y) = invertedBy (twoPoint H t) t ∧ IsCyclic K ∧
          Nat.card K = (involutions (H : Set Y)).ncard

/-- `ModelFactsProp` is `∀ Y, IsSimpleBenderGroup Y → ModelFactsFor Y` (definitionally). -/
theorem modelFactsProp_of
    (h : ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleBenderGroup Y → ModelFactsFor Y) :
    ModelFactsProp := h

end Work.Models
