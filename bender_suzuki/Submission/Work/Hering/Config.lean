import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The reduced configuration of Peterfalvi I §2

Peterfalvi I §2 Proposition (p. 191): a finite group of 2-rank `≥ 2` acting doubly transitively
on its involutions can be reduced to a group `G` with a normal elementary abelian subgroup `V`
of order `8` such that `Inv(G) = V#`, `C_G(V)` is a 2-group, and `G/C_G(V) ≅ Aut(V)`.

`Work.Hering.no_reduced_config` (the "hard core", §3–§4 of Chapter IV) says that no group has this
configuration; `Work.Hering.hering_of_no_reduced` shows `HeringProp` follows from it.
-/

set_option autoImplicit false

namespace Work.Hering

open LeanEval.GroupTheory.Defs

variable {G : Type*} [Group G]

/-- The conjugation action of `G` on the normal subgroup `V` realises **all** automorphisms of
`V`, i.e. `G/C_G(V) ≅ Aut(V)`. -/
def ActsAsAut (V : Subgroup G) (hV : V.Normal) : Prop :=
  ∀ φ : MulAut ↥V, ∃ g : G, ∀ v : ↥V,
    φ v = ⟨g * (v : G) * g⁻¹, hV.conj_mem v v.2 g⟩

/-- The reduced configuration of Peterfalvi I §2 Proposition (p. 191):
`V ⊴ G` is elementary abelian of order `8`, `Inv(G) = V#`, `C_G(V)` is a 2-group and
`G/C_G(V) ≅ Aut(V)`. -/
def ReducedConfig (G : Type*) [Group G] : Prop :=
  ∃ V : Subgroup G, ∃ hV : V.Normal,
    Nat.card V = 8 ∧ (∀ x ∈ V, x * x = 1) ∧
    (∀ x : G, orderOf x = 2 → x ∈ V) ∧
    IsPGroup 2 (Subgroup.centralizer ((V : Set G))) ∧ ActsAsAut V hV

/-- **The hard core of Hering's theorem** (Peterfalvi I Ch. IV §§2–4): no finite group carries
the reduced configuration. -/
def NoReducedConfigProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ¬ ReducedConfig G

end Work.Hering
