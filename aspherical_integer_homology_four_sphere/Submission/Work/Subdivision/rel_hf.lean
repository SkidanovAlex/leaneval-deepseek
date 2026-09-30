import Mathlib
import Submission.Work.Subdivision.SkelLevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision respects the relative skeleta

The chain map `subdivSkel (n+1)` (the restriction of the subdivision to the
`(n+1)`-skeleta) carries the relative subcomplex `cellRel n` — the chains of the
`(n+1)`-skeleton whose underlying chain lies in the `n`-skeleton — into
`sdRel n`, the analogous relative subcomplex on the subdivided side.

Unwinding the definitions, a chain `x` of `cellRel n` in degree `k` is an element
of the `(n+1)`-skeleton whose underlying cellular chain lies in
`cellSubMod n k`; its image under the subdivision is `subdivLM k` applied to that
underlying chain, and `subdivCpt_mem` says exactly that this lies in
`sdSubMod n k`.  All the work is in unfolding the three `SubData`-level
definitions (`comapChain`, `restrictMap`/`restrictCptMap`, `subdivSkel`), which
the `show`s below do.
-/

namespace Work.Subdivision

theorem rel_hf (P : Work.Subdivision.PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) :
    ∀ k, (Work.Subdivision.PolyCW.cellRel P hdd n).sub k ≤
      ((Work.Subdivision.PolyCW.sdRel P n).sub k).comap
        ((Work.Subdivision.PolyCW.subdivSkel P hdd haug (n + 1)).f k).hom := by
  intro k x hx
  -- `x` lies in the two-fold submodule: it is an `(n+1)`-chain whose underlying
  -- cellular chain lies in the `n`-skeleton.
  rw [Submodule.mem_comap]
  have hx' : (Submodule.subtype ((PolyCW.cellSub P hdd (n + 1)).sub k)) x ∈
      PolyCW.cellSubMod P hdd n k := hx
  -- The image of `x` under `subdivSkel (n+1)` has underlying `sdChain`-element
  -- `subdivLM k (subtype x)`.
  show (PolyCW.subdivCpt P hdd k).hom
      (Submodule.subtype ((PolyCW.cellSub P hdd (n + 1)).sub k) x) ∈ PolyCW.sdSubMod P n k
  exact subdivCpt_mem P hdd haug n k hx'

end Work.Subdivision
