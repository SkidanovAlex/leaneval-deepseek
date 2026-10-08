import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The set `G₀ = QK ∪ QK·t·Q` (Peterfalvi II, Ch. VI §2)

Shared definition for the "Suzuki subgroup" used in case (b) of the Proposition of Ch. VI §1:
`G0set Q K t = (Q ⊔ K) ∪ {p * t * q | p ∈ Q ⊔ K, q ∈ Q}`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Work.PSU3.StageA

/-- The carrier of the "Suzuki subgroup" `G₀ = QK ∪ QK·t·Q`. -/
def G0set {G : Type} [Group G] (Q K : Subgroup G) (t : G) : Set G :=
  ((Q ⊔ K : Subgroup G) : Set G) ∪
    {x : G | ∃ p : G, p ∈ (Q ⊔ K : Subgroup G) ∧ ∃ q : G, q ∈ Q ∧ x = p * t * q}

theorem mem_G0set {G : Type} [Group G] {Q K : Subgroup G} {t x : G} :
    x ∈ G0set Q K t ↔ x ∈ (Q ⊔ K : Subgroup G) ∨
      ∃ p : G, p ∈ (Q ⊔ K : Subgroup G) ∧ ∃ q : G, q ∈ Q ∧ x = p * t * q :=
  Iff.rfl

end Work.PSU3.StageA
