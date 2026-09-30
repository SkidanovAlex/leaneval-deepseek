import Mathlib
import Submission.Work.Certificates.ChainCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates

/-- If `M` is a subsingleton `ℤ`-module (hence the zero module), then any two
morphisms `M ⟶ N` agree: they are both determined by their value at `0`. -/
theorem subsingleton_hom_of_subsingleton {M N : ModuleCat ℤ} [Subsingleton M] :
    Subsingleton (M ⟶ N) :=
  ⟨fun f g => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩

end Work.Certificates
