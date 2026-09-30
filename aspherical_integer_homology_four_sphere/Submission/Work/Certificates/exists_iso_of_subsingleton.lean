import Mathlib
import Submission.Work.Certificates.ChainCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates

/-- Any two subsingleton `ℤ`-modules are isomorphic: a subsingleton module is a zero object,
and any two zero objects in a category are canonically isomorphic. -/
theorem exists_iso_of_subsingleton {M N : ModuleCat ℤ} [Subsingleton M] [Subsingleton N] :
    Nonempty (M ≅ N) :=
  ⟨(ModuleCat.isZero_of_subsingleton M).iso (ModuleCat.isZero_of_subsingleton N)⟩

end Work.Certificates
