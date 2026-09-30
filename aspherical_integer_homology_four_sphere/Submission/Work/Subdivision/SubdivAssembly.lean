/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubdivChain
import Submission.Work.Subdivision.subdivCpt_comm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision chain map of a polyhedral CW complex

Assembling `PolyCW.subdivCpt` and the chain-map compatibility
`Work.Subdivision.subdivCpt_comm` into the chain map
`PolyCW.subdiv : cellChain P ⟶ sdChain P` — the object requested by the
blueprint's HS3 section, together with the chain-map equation `subdiv_chainMap`
and the value on a single cell (`subdiv_apply_single`, the cone recursion).
-/

namespace Work.Subdivision

open CategoryTheory

universe u

namespace PolyCW

variable (P : PolyCW.{u})

/-- **The subdivision chain map** `cellChain P ⟶ sdChain P`.  In degree `k` it
sends the `k`-cell `e` to its subdivision chain `subdivCell P k e`. -/
noncomputable def subdiv (hdd : P.HasDdZero) (haug : P.HasAugZero) :
    cellChain P hdd ⟶ sdChain P :=
  subdivOf P hdd (subdivCpt_comm P hdd haug)

@[simp] theorem subdiv_f (hdd : P.HasDdZero) (haug : P.HasAugZero) (k : ℕ) :
    (subdiv P hdd haug).f k = subdivCpt P hdd k := rfl

@[simp] theorem subdiv_f_apply (hdd : P.HasDdZero) (haug : P.HasAugZero) (k : ℕ) :
    ((subdiv P hdd haug).f k).hom = subdivLM P k := rfl

/-- The value of the subdivision on a single cell: the cone recursion. -/
theorem subdiv_apply_single (hdd : P.HasDdZero) (haug : P.HasAugZero) (k : ℕ)
    (e : {e : P.Cell // P.dim e = k}) :
    (subdiv P hdd haug).f k (Finsupp.single e 1) = subdivCell P k e := by
  show subdivLM P k (Finsupp.single e 1) = subdivCell P k e
  exact subdivLM_single P k e

/-- The chain-map equation for the subdivision. -/
theorem subdiv_comm (hdd : P.HasDdZero) (haug : P.HasAugZero) (k : ℕ) :
    (subdiv P hdd haug).f (k + 1) ≫ (sdChain P).d (k + 1) k =
      (cellChain P hdd).d (k + 1) k ≫ (subdiv P hdd haug).f k :=
  (subdiv P hdd haug).comm (k + 1) k

end PolyCW

end Work.Subdivision
