/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.ComapChainIso
import Submission.Work.Subdivision.SubDataQuasiIso
import Submission.Work.Subdivision.Filtration
import Submission.Work.Subdivision.SubdivAssembly
import Submission.Work.Subdivision.subdivCpt_mem

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The skeletal levels of the subdivision

`PolyCW.cellSub n` and `PolyCW.sdSub n` are the two skeletal filtrations
(`Filtration.lean`).  Here we record, for the induction of
`SkelInduction.lean`:

* `cellRel P hdd n`, the `n`-skeleton inside the `(n+1)`-skeleton of the
  cellular chain complex, as a `SubData` of `(cellSub (n+1)).chain`;
* `sdRel P n`, the same on the subdivided side;
* the canonical isomorphisms `cellRelIso`, `sdRelIso` identifying these
  relative subcomplexes with the previous skeleta `(cellSub n).chain`,
  `(sdSub n).chain` (`SubData.comapChainIso`);
* `subdivSkel P hdd haug n`, the restriction of the subdivision chain map to
  the `n`-skeleta.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

namespace PolyCW

variable (P : PolyCW.{u})

/-- The `n`-skeleton inside the `(n+1)`-skeleton of the cellular chain complex. -/
noncomputable def cellRel (hdd : P.HasDdZero) (n : ℕ) :
    SubData ((cellSub P hdd (n + 1)).chain) :=
  SubData.comapChain (cellSub P hdd (n + 1)) (cellSubMod P hdd n)
    (fun k => cellSubMod_mono P hdd (Nat.le_succ n) k)
    (fun k x hx => (cellSub P hdd n).d_mem k x hx)

/-- The `n`-skeleton inside the `(n+1)`-skeleton of the subdivided chain
complex. -/
noncomputable def sdRel (n : ℕ) : SubData ((sdSub P (n + 1)).chain) :=
  SubData.comapChain (sdSub P (n + 1)) (sdSubMod P n)
    (fun k => sdSubMod_mono P (Nat.le_succ n) k)
    (fun k x hx => (sdSub P n).d_mem k x hx)

/-- The relative subcomplex `cellRel` is the previous skeleton. -/
noncomputable def cellRelIso (hdd : P.HasDdZero) (n : ℕ) :
    (cellRel P hdd n).chain ≅ (cellSub P hdd n).chain :=
  SubData.comapChainIso (cellSub P hdd (n + 1)) (cellSubMod P hdd n)
    (fun k => cellSubMod_mono P hdd (Nat.le_succ n) k)
    (fun k x hx => (cellSub P hdd n).d_mem k x hx)

/-- The relative subcomplex `sdRel` is the previous skeleton. -/
noncomputable def sdRelIso (n : ℕ) :
    (sdRel P n).chain ≅ (sdSub P n).chain :=
  SubData.comapChainIso (sdSub P (n + 1)) (sdSubMod P n)
    (fun k => sdSubMod_mono P (Nat.le_succ n) k)
    (fun k x hx => (sdSub P n).d_mem k x hx)

/-- The subdivision chain map restricted to the `n`-skeleta. -/
noncomputable def subdivSkel (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) :
    (cellSub P hdd n).chain ⟶ (sdSub P n).chain :=
  (cellSub P hdd n).restrictMap (sdSub P n) (subdiv P hdd haug)
    (fun k => subdivCpt_mem P hdd haug n k)

end PolyCW

end Work.Subdivision
