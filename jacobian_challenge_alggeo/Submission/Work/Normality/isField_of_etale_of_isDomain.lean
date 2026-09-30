import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normality

set_option linter.style.haveILetI false in
/-- An étale algebra over a field which is a domain is a field.

Proof sketch: `Algebra.Etale L B` gives `Algebra.FormallyUnramified L B` and
`Algebra.EssFiniteType L B`, so `Algebra.FormallyUnramified.finite_of_free L B` (with
`Module.Free.of_divisionRing L B`, every module over a field is free) gives `Module.Finite L B`;
then `IsArtinianRing.of_finite L B` and `IsArtinianRing.isField_of_isDomain B` finish. -/
theorem isField_of_etale_of_isDomain {L : Type*} [Field L] {B : Type*} [CommRing B]
    [IsDomain B] [Algebra L B] [Algebra.Etale L B] : IsField B := by
  haveI : Algebra.FormallyUnramified L B := inferInstance
  have : Module.Finite L B := Algebra.FormallyUnramified.finite_of_free L B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite L B
  exact IsArtinianRing.isField_of_isDomain B

end Work.Normality
