import Submission.Work.Step7Comm.Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.Bender.DTransitiveInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Step7Comm.isElementaryAbelianTwo_Q0sub`

`Q₀sub H = ⟨Inv H ∪ {1}⟩` is elementary abelian of exponent two: the involutions of `H` commute
(Ch. V §1 Prop. 1 (c), `L5.involutions_commute`, from `ChIIFourProp`; or directly from
`ChV12.prop1c` when `Q` is known to be nilpotent) and `Q0sub_elementary` converts that into the
closed form `y * y = 1` for all `y ∈ Q₀sub H` plus commutativity.

Both variants are provided: the `ChIIFourProp` one is what the §3 chain has at hand, and the
nilpotent one is what the design pass 17 states (it avoids `ChIIFourProp`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.Step7Comm

variable {G : Type} [Group G] [Finite G]

/-- `Q₀sub H` is elementary abelian of exponent two, from `ChIIFourProp`. -/
theorem isElementaryAbelianTwo_Q0sub {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hC4 : ChIIFourProp) :
    IsElementaryAbelianTwo (Work.ThmF.Q0sub H) := by
  obtain ⟨h1, h2, -, -⟩ :=
    Work.ThmF.ChV12.Q0sub_elementary H (Work.ThmF.L5.involutions_commute c.sit hC4 c.split)
  exact ⟨h1, h2⟩

/-- `Q₀sub H` is elementary abelian of exponent two, from nilpotency of `Q`. -/
theorem isElementaryAbelianTwo_Q0sub_of_nilpotent {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hnil : Group.IsNilpotent ↥Q) :
    IsElementaryAbelianTwo (Work.ThmF.Q0sub H) := by
  have hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b :=
    Work.ThmF.Bender.DTransitiveInv c.split.stronglyEmbedded c.split.invol c.split.not_mem
  have hcomm : ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u := by
    intro u hu v hv
    have hcu := (Work.ThmF.mem_centerOf (Q := Q)).mp
      (Work.ThmF.ChV12.prop1c c.sit H Q t c.split hD hnil u hu)
    have hcv := (Work.ThmF.mem_centerOf (Q := Q)).mp
      (Work.ThmF.ChV12.prop1c c.sit H Q t c.split hD hnil v hv)
    exact hcu.2 v hcv.1
  obtain ⟨h1, h2, -, -⟩ := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  exact ⟨h1, h2⟩

end Work.Step7Comm
