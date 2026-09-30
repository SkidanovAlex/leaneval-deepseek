/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SdChain
import Submission.Work.Subdivision.CellChain
import Submission.Work.Subdivision.Subdiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision chain map

`PolyCW.subdivOf` assembles the cone recursion `subdivCell` into a chain map
`cellChain P ⟶ sdChain P`.  Its `k`-th component (`PolyCW.subdivCpt`) sends the
`k`-cell `e` to its subdivision chain `subdivCell e` (see `Subdiv.lean`); the
compatibility with the differentials is the hypothesis `hcomm`, which is exactly
the statement `∂ ∘ subdiv = subdiv ∘ ∂` (the blueprinted `subdiv_chainMap`),
proved from the cone recursion, the support invariant `subdivCell_support` and
the two cone identities by `Work.Subdivision.subdivCpt_comm`.
-/

open CategoryTheory

namespace Work.Subdivision

universe u

namespace PolyCW

variable (P : PolyCW.{u})

/-- The `k`-th component of the subdivision chain map, as a morphism of the
ambient complexes. -/
noncomputable def subdivCpt (hdd : P.HasDdZero) (k : ℕ) :
    (cellChain P hdd).X k ⟶ (sdChain P).X k :=
  ModuleCat.ofHom (subdivLM P k)

@[simp] theorem subdivCpt_apply (hdd : P.HasDdZero) (k : ℕ) :
    (subdivCpt P hdd k).hom = subdivLM P k := rfl

/-- **The subdivision chain map** `cellChain P ⟶ sdChain P`, given the chain-map
compatibility of its components. -/
noncomputable def subdivOf (hdd : P.HasDdZero)
    (hcomm : ∀ k, subdivCpt P hdd (k + 1) ≫ (sdChain P).d (k + 1) k =
      (cellChain P hdd).d (k + 1) k ≫ subdivCpt P hdd k) :
    cellChain P hdd ⟶ sdChain P :=
  ChainComplex.ofHom (fun k => subdivCpt P hdd k) hcomm

@[simp] theorem subdivOf_f (hdd : P.HasDdZero)
    (hcomm : ∀ k, subdivCpt P hdd (k + 1) ≫ (sdChain P).d (k + 1) k =
      (cellChain P hdd).d (k + 1) k ≫ subdivCpt P hdd k) (k : ℕ) :
    (subdivOf P hdd hcomm).f k = subdivCpt P hdd k := rfl

/-- The chain-map equation for the subdivision: its components commute with the
differentials. -/
theorem subdiv_chainMap (hdd : P.HasDdZero)
    (hcomm : ∀ k, subdivCpt P hdd (k + 1) ≫ (sdChain P).d (k + 1) k =
      (cellChain P hdd).d (k + 1) k ≫ subdivCpt P hdd k) (k : ℕ) :
    (subdivOf P hdd hcomm).f (k + 1) ≫ (sdChain P).d (k + 1) k =
      (cellChain P hdd).d (k + 1) k ≫ (subdivOf P hdd hcomm).f k :=
  (subdivOf P hdd hcomm).comm (k + 1) k

end PolyCW

end Work.Subdivision
