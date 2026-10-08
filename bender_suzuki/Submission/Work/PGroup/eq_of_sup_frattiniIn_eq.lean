import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Frattini subgroup consists of non-generators (subgroup form)

The Frattini subgroup `Φ(P)` of a finite group `P` consists of *non-generators*: if a subgroup
`H ≤ P` together with `Φ(P)` generates `P`, then already `H = P`.  Equivalently, every proper
subgroup is contained in a maximal subgroup, and every maximal subgroup contains `Φ(P)`.

In the vocabulary of `Work.PGroup` (all subgroups are subgroups of an ambient group `G` and
`Work.PGroup.frattiniIn P` is `Φ(P)` viewed inside `G`), the statement reads

`H ⊔ Φ(P) = P → H = P`   for a finite `P`.

Mathlib's `frattini_nongenerating` proves exactly this inside a group `H` with coatomic subgroup
lattice.  The subgroup lattice of a finite group is coatomic (`IsCoatomic (Subgroup H)` is
inferred from `[Finite H]`), so the only work is transporting the statement along the subtype
`P.subtype : ↥P →* G`: the order isomorphism `Subgroup ↥P ≃ {A | A ≤ P}` given by `map`/`comap`
turns `H ⊔ Φ(P) = P` into `(H.comap P.subtype) ⊔ Φ(↥P) = ⊤`.
-/

set_option linter.unusedVariables false

open Subgroup

namespace Work.PGroup

/-- If `H ≤ P` and `H` together with the Frattini subgroup of `P` generates `P`, then `H = P`.
This is the "non-generating" property of the Frattini subgroup, in the ambient-group form used
throughout the `Work.PGroup` development. -/
theorem eq_of_sup_frattiniIn_eq {G : Type*} [Group G] {p : ℕ} (P H : Subgroup G) [Finite P]
    (hP : IsPGroup p P) (hH : H ≤ P) (h : H ⊔ Work.PGroup.frattiniIn P = P) : H = P := by
  -- Transport to `↥P`, where `frattini_nongenerating` applies.
  have hsup : H.comap P.subtype ⊔ frattini ↥P = ⊤ := by
    have h1 : frattini ↥P = (Work.PGroup.frattiniIn P).comap P.subtype := by
      rw [Work.PGroup.frattiniIn, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    rw [h1, Subgroup.comap_sup_eq_of_le_range (f := P.subtype)
      (by rwa [Subgroup.range_subtype])
      (by rw [Subgroup.range_subtype]; exact Work.PGroup.frattiniIn_le P), h]
    ext x; simp
  have hK : H.comap P.subtype = ⊤ := frattini_nongenerating hsup
  have h2 : (H.comap P.subtype).map P.subtype = H :=
    Subgroup.map_comap_eq_self (f := P.subtype) (by rwa [Subgroup.range_subtype])
  rw [← h2, hK, Subgroup.map_top, Subgroup.range_subtype]

end Work.PGroup
