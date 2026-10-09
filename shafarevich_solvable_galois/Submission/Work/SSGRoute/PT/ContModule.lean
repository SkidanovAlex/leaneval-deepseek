import Mathlib
import Submission.Work.SSGRoute.ContCohomology
import Submission.Work.SSGRoute.PT.contSmulMem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `ZMod p`-linear packaging of the continuous cochain groups

`Submission.Work.SSGRoute.ContCohomology` models the continuous cohomology `H1cont`/`H2cont` as
quotients of `AddSubgroup`s, which carry only an additive structure.  Together with
`Work.SSGRoute.PT.contSmulMem` (the four `ZMod p`-scaling closures) the same carriers are
`Submodule`s, and the quotients of `Work.SSGRoute.contSmulMem`-closed subgroups by *submodules*
carry a `Module (ZMod p)` structure.  This file provides that packaging:

* `Z1contS`, `B1contS`, `Z2contS`, `B2contS` — the `Submodule (ZMod p)` structures with the same
  carriers as `Z1cont`, `B1cont`, `Z2cont`, `B2cont`;
* `H1contS`, `H2contS` — the corresponding quotients, which are `Module (ZMod p)` (whereas
  `H1cont`, `H2cont` are only `AddCommGroup`).

Recall the design note: the *product* form `H1cont ⊤ →+ ∏_A H1loc (decomp k A)` does not
elaborate (timeout at 8M heartbeats); the localisation maps are stated per place and assembled.
-/

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (Γ G M : Type) [Group Γ] [TopologicalSpace Γ] [Group G]
  [AddCommGroup M] [DistribMulAction G M] [Module (ZMod p) M] [SMulCommClass G (ZMod p) M]

/-- `Z1cont` as a `ZMod p`-submodule (same carrier). -/
def Z1contS (act : Γ →* G) (H : Subgroup Γ) : Submodule (ZMod p) (Γ → M) where
  carrier := (Z1cont Γ G M act H : Set (Γ → M))
  zero_mem' := (Z1cont Γ G M act H).zero_mem'
  add_mem' := (Z1cont Γ G M act H).add_mem'
  smul_mem' := fun r f hf => (PT.contSmulMem p Γ G M act H r).1 f hf

/-- `B1cont` as a `ZMod p`-submodule (same carrier). -/
def B1contS (act : Γ →* G) (H : Subgroup Γ) : Submodule (ZMod p) (Γ → M) where
  carrier := (B1cont Γ G M act H : Set (Γ → M))
  zero_mem' := (B1cont Γ G M act H).zero_mem'
  add_mem' := (B1cont Γ G M act H).add_mem'
  smul_mem' := fun r f hf => (PT.contSmulMem p Γ G M act H r).2.1 f hf

/-- `Z2cont` as a `ZMod p`-submodule (same carrier). -/
def Z2contS (act : Γ →* G) : Submodule (ZMod p) (Γ → Γ → M) where
  carrier := (Z2cont Γ G M act : Set (Γ → Γ → M))
  zero_mem' := (Z2cont Γ G M act).zero_mem'
  add_mem' := (Z2cont Γ G M act).add_mem'
  smul_mem' := fun r f hf => (PT.contSmulMem p Γ G M act ⊤ r).2.2.1 f hf

/-- `B2cont` as a `ZMod p`-submodule (same carrier). -/
def B2contS (act : Γ →* G) (H : Subgroup Γ) : Submodule (ZMod p) (Γ → Γ → M) where
  carrier := (B2cont Γ G M act H : Set (Γ → Γ → M))
  zero_mem' := (B2cont Γ G M act H).zero_mem'
  add_mem' := (B2cont Γ G M act H).add_mem'
  smul_mem' := fun r f hf => (PT.contSmulMem p Γ G M act H r).2.2.2 f hf

/-- The `ZMod p`-linear `H¹`: the quotient of the `Submodule` `Z1contS` by `B1contS`. -/
abbrev H1contS (act : Γ →* G) (H : Subgroup Γ) : Type _ :=
  ↥(Z1contS p Γ G M act H) ⧸ ((B1contS p Γ G M act H).comap (Z1contS p Γ G M act H).subtype)

/-- The `ZMod p`-linear `H²`. -/
abbrev H2contS (act : Γ →* G) (H : Subgroup Γ) : Type _ :=
  ↥(Z2contS p Γ G M act) ⧸ ((B2contS p Γ G M act H).comap (Z2contS p Γ G M act).subtype)

-- The two packagings are *definitionally* the same type, so the `Module (ZMod p)` structure of
-- `H1contS` is already available on `H1cont` (and likewise in degree `2`).
example (act : Γ →* G) (H : Subgroup Γ) : H1cont Γ G M act H = H1contS p Γ G M act H := rfl
example (act : Γ →* G) (H : Subgroup Γ) : Module (ZMod p) (H1contS p Γ G M act H) := inferInstance
example (act : Γ →* G) (H : Subgroup Γ) : Module (ZMod p) (H2contS p Γ G M act H) := inferInstance

end

end Work.SSGRoute
