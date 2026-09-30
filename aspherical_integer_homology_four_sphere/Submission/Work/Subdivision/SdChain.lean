/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.OrderComplex
import Submission.Work.Subdivision.orderD_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision of a `PolyCW` as a chain complex

`PolyCW.sdChain P` is the order complex of the poset of cells of `P` — i.e. the
barycentric subdivision of `P` — as a `ChainComplex (ModuleCat ℤ) ℕ`.  Its
`k`-chains are the free ℤ-module on the `k`-simplices of the subdivision, i.e.
the strictly increasing chains of `k+1` cells of `P`, and the differential is the
alternating sum of the face maps (`D`), which is a chain complex by
`Work.Subdivision.orderD_comp`.
-/

namespace Work.Subdivision

universe u

namespace PolyCW

variable (P : PolyCW.{u})

/-- The barycentric subdivision of `P`, as a chain complex of ℤ-modules. -/
noncomputable def sdChain : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of ℤ (chainMod P.Cell k))
    (fun k => ModuleCat.ofHom (D (α := P.Cell) k))
    (fun k => ModuleCat.hom_ext (by simpa using orderD_comp (α := P.Cell) k))

@[simp] theorem sdChain_X (k : ℕ) :
    (sdChain P).X k = ModuleCat.of ℤ (chainMod P.Cell k) := rfl

@[simp] theorem sdChain_d (k : ℕ) :
    (sdChain P).d (k + 1) k = ModuleCat.ofHom (D (α := P.Cell) k) := by
  simp only [sdChain, ChainComplex.of_d]

end PolyCW

end Work.Subdivision
